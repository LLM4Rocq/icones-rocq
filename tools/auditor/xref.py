"""Clickable identifier cross-references inside highlighted snippets.

Post-parse, pre-render pass: once a tab's :class:`~tools.auditor.schema.
Document` is fully assembled, build an ``{ident: entry_id}`` map from
every entry's ``rocq_idents`` (sections, chapters AND beyond trees) and
wrap matching identifier tokens in each snippet's Pygments HTML in
``<a class="code-xref" …>`` anchors pointing at the defining entry's
page.

Two passes cooperate
---------------------
* :func:`linkify_document` is the *per-tab* pass.  It links an ident to
  another entry **of the same tab** with a uniform ``../entries/<id>.html``
  href.  Single-tab callers (and the legacy goldens) rely on it.
* :func:`linkify_all` is the *global* pass run by the orchestrator once
  all three tabs are parsed.  It mops up the tokens the per-tab pass left
  plain by consulting (a) a cross-tab entry map — so a PPL snippet can
  link ``EM_term`` to its Paper entry page — and (b) a source-line index
  scraped from ``theories/**/*.v`` — so an ident documented *nowhere*
  links to its GitHub blob ``#L`` line.  Cross-tab entry hrefs are
  tab-aware (``../../<tab>/entries/<id>.html``); source hrefs are
  absolute and carry the extra ``code-xref-src`` class.

Both passes share the same token machinery, so they compose: the global
pass only ever sees tokens the per-tab pass left unwrapped (a span that
already holds an ``<a>`` can never re-match — see *Idempotency*).

Design decisions
----------------
* **Token classes** — Pygments' Coq/Rocq lexer emits plain names as
  ``<span class="n">ident</span>`` (verified on real project source:
  only ``Token.Name`` / class ``n`` occurs).  We also accept ``nf`` /
  ``nb`` / ``nc`` defensively; comment (``c``) and string (``s2``)
  spans are never touched.  Identifiers with underscores are single
  tokens (the lexer does not split on ``_``).
* **Minimum length** — idents shorter than :data:`MIN_IDENT_LEN` (4)
  are excluded: 1–3 char names (``f``, ``mu``, ``der``) are pervasive
  as local binders and would over-link.
* **Duplicates** — when two entries claim the same ident, the entry
  whose ``id`` equals ``slugify_label(ident)`` wins (it *is* the
  ident's page); otherwise first-wins in document order.  The global
  entry map applies the same rule across tabs, ordering the tabs
  deterministically (paper, then ppl, then examples).
* **Source ambiguity** — when an ident is declared at top level in more
  than one ``.v`` file the source index drops it entirely: a link to one
  of several definitions would be a *wrong* link, which is worse than no
  link.  Idents that resolve to a documented entry never consult the
  source index, so a name that is both documented and multiply-declared
  still links (to its entry page).
* **URL prefix** — every page that embeds snippet HTML lives at depth 2
  from the site root (``<tab>/sections/x.html``, ``<tab>/entries/x.html``,
  ``<tab>/beyond/x.html``).  A same-tab entry link is therefore
  ``../entries/<id>.html``; a cross-tab one is
  ``../../<tab>/entries/<id>.html``.
* **Self-links** — when linkifying a snippet owned by entry E,
  occurrences mapping back to E are left unwrapped (a self-link is
  noise on E's own page).
* **Idempotency** — the token regex matches ``[^<]+`` span bodies only;
  a span already containing an ``<a>`` can never match again, so
  running either pass twice (or both in sequence) is a no-op on the
  already-linked tokens.

Prose cross-references
----------------------
The same maps linkify prose: statement HTML, entry detail prose,
section/chapter intros and notes.  Prose is rendered by the parser's
``_inline_to_html`` into ``<code>ident</code>`` spans (never Pygments).
We wrap a ``<code>`` body in a ``code-xref`` anchor when, after
HTML-unescape, it ``fullmatch``es the identifier regex, is at least
:data:`MIN_IDENT_LEN` long and resolves to a target.  Math / notation
``<code>`` (spaces, operators, ``⟦``, ``∫``, ``·`` …) never matches the
identifier regex and is left untouched, as are self-links and unknown
idents.  The ``[^<]+`` body discipline keeps the pass idempotent.
"""

from __future__ import annotations

import html as html_mod
import re
from pathlib import Path
from typing import Callable

from .coqdoc import CoqdocResolver
from .schema import (
    ALL_TABS,
    CoqSnippet,
    Document,
    Entry,
    ThreeTabDocument,
)

#: Identifiers shorter than this are never linkified (over-link noise).
MIN_IDENT_LEN = 4

#: Shape of a linkable Rocq identifier — plain name, no dots/operators.
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

#: A single Pygments name token.  ``[^<]+`` keeps the match within one
#: leaf span: spans that already contain markup (e.g. an ``<a>`` from a
#: previous pass) can never match, which makes the pass idempotent.
_NAME_SPAN_RE = re.compile(r'<span class="(n|nf|nb|nc)">([^<]+)</span>')

#: Relative href prefix from any snippet-embedding page (all depth 2 from
#: the site root: ``<tab>/<kind>/x.html``) back to its own tab root.
_HREF_PREFIX = "../"

#: A single ``<code>…</code>`` prose span.  ``[^<]+`` keeps the match
#: within one leaf span: a ``<code>`` already containing markup (e.g. an
#: ``<a>`` from a previous pass) can never match, keeping the pass
#: idempotent.
_CODE_SPAN_RE = re.compile(r"<code>([^<]+)</code>")

#: Top-level Rocq declaration keywords whose first ``\w+`` token names a
#: definition.  ``Notation`` is handled by the same pattern but only its
#: bare-identifier form matches (a quoted ``Notation "…"`` name fails the
#: identifier class and is skipped).
_DECL_KEYWORDS = (
    "Definition",
    "Lemma",
    "Theorem",
    "Corollary",
    "Proposition",
    "Fixpoint",
    "CoFixpoint",
    "Inductive",
    "CoInductive",
    "Variant",
    "Record",
    "Structure",
    "Class",
    "Instance",
    "Canonical",
    "Notation",
)

#: ``<keyword> <name>`` at the start of a (possibly indented) line.  The
#: name is captured as a bare identifier; ``Notation "…"`` forms whose
#: name is a string literal simply fail this pattern (the ``"`` is not in
#: the identifier class) and are skipped.
_DECL_RE = re.compile(
    r"^\s*(?:" + "|".join(_DECL_KEYWORDS) + r")\s+([A-Za-z_][A-Za-z0-9_']*)"
)

#: Named ``HB.instance``/``HB.structure`` definitions of the form
#: ``HB.instance Definition Name := …`` (and the ``HB.structure`` analogue).
_HB_DECL_RE = re.compile(
    r"^\s*HB\.(?:instance|structure)\s+Definition\s+([A-Za-z_][A-Za-z0-9_']*)"
)


# -- maps -------------------------------------------------------------------


def _iter_entries(doc: Document):
    """Yield every Entry of ``doc`` across sections, chapters and beyond.

    The beyond compat shim aliases Section/Entry objects, so callers that
    need object-level dedup must do it themselves; for map building the
    revisits are harmless (idempotent inserts).
    """
    for section in doc.sections:
        yield from section.entries
    for chapter in doc.chapters:
        for section in chapter.sections:
            yield from section.entries
    for contrib in doc.beyond:
        yield from contrib.entries


def build_ident_map(doc: Document) -> dict[str, str]:
    """Collect ``{ident: entry_id}`` over every entry of ``doc``.

    Walks the paper-section tree, the PPL/Examples chapter tree and the
    (possibly shimmed) beyond list; the shim shares Entry objects so
    revisiting them is harmless.  Filtering and dedup rules are
    documented in the module docstring.
    """
    # Lazy import to avoid a cycle (parser imports this module).
    from .parser import slugify_label

    mapping: dict[str, str] = {}

    def consider(entry: Entry) -> None:
        for ident in entry.rocq_idents:
            if len(ident) < MIN_IDENT_LEN:
                continue
            if not _IDENT_RE.fullmatch(ident):
                continue  # qualified / operator / notation-like cells
            prev = mapping.get(ident)
            if prev is None:
                mapping[ident] = entry.id
            elif prev != entry.id and entry.id == slugify_label(ident):
                # The ident's "own" page trumps an earlier claimant.
                mapping[ident] = entry.id

    for entry in _iter_entries(doc):
        consider(entry)
    return mapping


def build_global_entry_map(three: ThreeTabDocument) -> dict[str, tuple[str, str]]:
    """Collect ``{ident: (tab, entry_id)}`` across all three tabs.

    Tabs are visited in the deterministic order :data:`ALL_TABS`
    (paper, ppl, examples).  Within and across tabs the dedup rule is
    the same as :func:`build_ident_map`: an ident's *own* page — where
    ``entry.id == slugify_label(ident)`` — always wins; otherwise the
    first claimant in tab/document order keeps the slot.
    """
    from .parser import slugify_label

    mapping: dict[str, tuple[str, str]] = {}

    def consider(tab: str, entry: Entry) -> None:
        for ident in entry.rocq_idents:
            if len(ident) < MIN_IDENT_LEN:
                continue
            if not _IDENT_RE.fullmatch(ident):
                continue
            prev = mapping.get(ident)
            if prev is None:
                mapping[ident] = (tab, entry.id)
            elif prev != (tab, entry.id) and entry.id == slugify_label(ident):
                mapping[ident] = (tab, entry.id)

    for tab in ALL_TABS:
        doc = three.tab(tab)
        for entry in _iter_entries(doc):
            consider(tab, entry)
    return mapping


def build_source_index(
    theories_root: str | Path,
    *,
    repo_root: str | Path | None = None,
) -> dict[str, tuple[str, int]]:
    """Scrape ``{ident: (vfile, line)}`` from ``theories/**/*.v``.

    ``vfile`` is repository-relative (e.g. ``theories/homs/coalgebra.v``),
    suitable for :meth:`CoqdocResolver.github_url`.  Paths are made
    relative to ``repo_root`` (the directory holding ``theories/``);
    when omitted it defaults to ``theories_root``'s parent.  Only
    top-level declarations are indexed (see :data:`_DECL_KEYWORDS`, plus
    named ``HB.instance``/``HB.structure`` forms); constructors, local
    binders and ``Notation "…"`` string forms are not.

    Ambiguity is resolved by *exclusion*: an ident declared at top level
    in more than one file is dropped, so the index never yields a wrong
    target.  Idents shorter than :data:`MIN_IDENT_LEN` are excluded.
    """
    root = Path(theories_root)
    if not root.is_dir():
        return {}
    base = Path(repo_root) if repo_root is not None else root.parent

    # First sighting wins per ident; a later sighting in a *different*
    # file marks it ambiguous and it is removed at the end.
    first: dict[str, tuple[str, int]] = {}
    ambiguous: set[str] = set()

    for vfile in sorted(root.rglob("*.v")):
        try:
            rel = vfile.relative_to(base).as_posix()
        except ValueError:
            rel = vfile.as_posix()
        try:
            lines = vfile.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        for lineno, text in enumerate(lines, start=1):
            m = _DECL_RE.match(text) or _HB_DECL_RE.match(text)
            if not m:
                continue
            name = m.group(1)
            if len(name) < MIN_IDENT_LEN:
                continue
            existing = first.get(name)
            if existing is None:
                first[name] = (rel, lineno)
            elif existing[0] != rel:
                ambiguous.add(name)

    for name in ambiguous:
        first.pop(name, None)
    return first


# -- shared linkify core ----------------------------------------------------

#: A resolver maps an ident to ``(href, extra_class)`` or ``None``.
#: ``href`` is the anchor target; ``extra_class`` is appended to the base
#: ``code-xref`` class (``""`` for entry links, ``" code-xref-src"`` for
#: source links).  ``None`` means "leave the token plain" (unknown ident
#: or self-link).
Resolver = Callable[[str], "tuple[str, str] | None"]


def _linkify_html(highlighted_html: str, resolve: Resolver) -> str:
    """Wrap resolvable name tokens of one snippet's HTML in anchors."""

    def repl(m: re.Match[str]) -> str:
        cls, escaped_tok = m.group(1), m.group(2)
        ident = html_mod.unescape(escaped_tok)
        target = resolve(ident)
        if target is None:
            return m.group(0)
        href, extra = target
        return (
            f'<span class="{cls}">'
            f'<a class="code-xref{extra}" href="{href}">'
            f"{escaped_tok}</a></span>"
        )

    return _NAME_SPAN_RE.sub(repl, highlighted_html)


def _linkify_prose(prose_html: str, resolve: Resolver) -> str:
    """Wrap resolvable ``<code>`` prose spans in ``code-xref`` anchors.

    Only ``<code>`` bodies that, after HTML-unescape, are a single
    identifier (``_IDENT_RE.fullmatch``), at least :data:`MIN_IDENT_LEN`
    long and resolve to a target are wrapped.  Math / notation spans
    never match the regex and are returned verbatim, as are self-links
    and unknown idents.
    """
    if not prose_html or "<code>" not in prose_html:
        return prose_html

    def repl(m: re.Match[str]) -> str:
        escaped_tok = m.group(1)
        ident = html_mod.unescape(escaped_tok)
        if len(ident) < MIN_IDENT_LEN or not _IDENT_RE.fullmatch(ident):
            return m.group(0)
        target = resolve(ident)
        if target is None:
            return m.group(0)
        href, extra = target
        return (
            f"<code>"
            f'<a class="code-xref{extra}" href="{href}">'
            f"{escaped_tok}</a></code>"
        )

    return _CODE_SPAN_RE.sub(repl, prose_html)


def _walk_document(
    doc: Document,
    resolve_for: Callable[[str | None], Resolver],
) -> None:
    """Apply ``resolve_for(owner_id)`` to every snippet/prose of ``doc``.

    ``resolve_for`` is given the owning entry id (or ``None`` for
    section-/chapter-level prose and snippets) and returns the
    :data:`Resolver` to use for that owner.  Snippets are deduplicated by
    object identity so the beyond compat shim (which aliases Section /
    Entry objects) processes each exactly once; the prose passes are
    idempotent so re-touching aliased prose is harmless.
    """
    seen: set[int] = set()

    def do_snippets(snips: list[CoqSnippet], owner: str | None) -> None:
        resolve = resolve_for(owner)
        for s in snips:
            if id(s) in seen:
                continue
            seen.add(id(s))
            s.highlighted_html = _linkify_html(s.highlighted_html, resolve)

    def do_entry(entry: Entry) -> None:
        resolve = resolve_for(entry.id)
        entry.statement_html = _linkify_prose(entry.statement_html, resolve)
        if entry.detail is not None:
            do_snippets(entry.detail.snippets, entry.id)
            entry.detail.prose_html = _linkify_prose(entry.detail.prose_html, resolve)

    def do_section(section) -> None:
        none_resolve = resolve_for(None)
        section.intro_html = _linkify_prose(section.intro_html, none_resolve)
        section.notes_html = _linkify_prose(section.notes_html, none_resolve)
        do_snippets(section.snippets, None)
        for entry in section.entries:
            do_entry(entry)

    for section in doc.sections:
        do_section(section)
    for chapter in doc.chapters:
        none_resolve = resolve_for(None)
        chapter.intro_html = _linkify_prose(chapter.intro_html, none_resolve)
        chapter.notes_html = _linkify_prose(chapter.notes_html, none_resolve)
        for section in chapter.sections:
            do_section(section)
    for contrib in doc.beyond:
        none_resolve = resolve_for(None)
        contrib.intro_html = _linkify_prose(contrib.intro_html, none_resolve)
        contrib.notes_html = _linkify_prose(contrib.notes_html, none_resolve)
        do_snippets(contrib.snippets, None)
        for entry in contrib.entries:
            do_entry(entry)
    # ``preamble_html`` is rendered ONLY on the depth-1 ``index.html``
    # landing (every other field embeds in depth-2 pages); its hrefs need
    # a different relative prefix and are handled by the global pass'
    # :func:`_linkify_preamble`, so it is deliberately skipped here.


# -- per-tab pass (legacy / single-tab) -------------------------------------


def linkify_document(doc: Document) -> Document:
    """Linkify every snippet/prose of ``doc`` in place; returns ``doc``.

    Same-tab pass: links an ident to another entry of *this* document
    with a uniform ``../entries/<id>.html`` href, suppressing self-links.
    Run by the single-tab :func:`~tools.auditor.parser.parse` path and
    relied on by the goldens.  The global :func:`linkify_all` pass later
    mops up whatever this pass leaves plain.
    """
    mapping = build_ident_map(doc)
    if not mapping:
        return doc

    def resolve_for(owner: str | None) -> Resolver:
        def resolve(ident: str) -> tuple[str, str] | None:
            target = mapping.get(ident)
            if target is None or target == owner:
                return None
            return (f"{_HREF_PREFIX}entries/{target}.html", "")

        return resolve

    _walk_document(doc, resolve_for)
    return doc


# -- global pass (cross-tab + source fallback) ------------------------------


def linkify_all(
    three: ThreeTabDocument,
    *,
    resolver: CoqdocResolver,
    theories_root: str | Path,
    repo_root: str | Path | None = None,
) -> ThreeTabDocument:
    """Global linkify pass across all three tabs; returns ``three``.

    For each name token / prose ``<code>`` ident in a snippet owned by
    ``(tab, owner_entry)`` the resolution order is:

    1. self-link (ident maps to ``owner_entry`` in this tab) → leave plain;
    2. global entry map → link to that entry page with a tab-aware href
       (same tab ``../entries/X.html``; cross tab
       ``../../<tab>/entries/X.html``);
    3. source index → absolute GitHub blob ``#L`` line, class
       ``code-xref code-xref-src``;
    4. otherwise leave plain.

    Composes with :func:`linkify_document`: the per-tab pass has already
    wrapped same-tab entry idents, so step 2's same-tab branch only ever
    fires on tokens the per-tab pass skipped (and re-linking is a no-op
    by idempotency anyway).
    """
    entry_map = build_global_entry_map(three)
    source_index = build_source_index(theories_root, repo_root=repo_root)

    def source_target(ident: str) -> tuple[str, str] | None:
        src = source_index.get(ident)
        if src is None:
            return None
        vfile, line = src
        return (resolver.github_url(vfile, line), " code-xref-src")

    for tab in ALL_TABS:
        doc = three.tab(tab)

        def resolve_for(owner: str | None, _tab: str = tab) -> Resolver:
            # Depth-2 pages (sections/entries/beyond): own tab root is one
            # level up; another tab is two up then into ``<tab>/``.
            def resolve(ident: str) -> tuple[str, str] | None:
                hit = entry_map.get(ident)
                if hit is not None:
                    target_tab, target_id = hit
                    if target_tab == _tab and target_id == owner:
                        return None  # self-link on its own page
                    if target_tab == _tab:
                        href = f"{_HREF_PREFIX}entries/{target_id}.html"
                    else:
                        href = f"../../{target_tab}/entries/{target_id}.html"
                    return (href, "")
                return source_target(ident)

            return resolve

        _walk_document(doc, resolve_for)

        # The preamble renders on the depth-1 ``<tab>/index.html`` landing,
        # so its relative hrefs drop one ``../`` level: same tab is
        # ``entries/X.html``, another tab is ``../<tab>/entries/X.html``.
        # There is no "owner entry" on the landing, so no self-links.
        def preamble_resolve(ident: str, _tab: str = tab) -> tuple[str, str] | None:
            hit = entry_map.get(ident)
            if hit is not None:
                target_tab, target_id = hit
                if target_tab == _tab:
                    href = f"entries/{target_id}.html"
                else:
                    href = f"../{target_tab}/entries/{target_id}.html"
                return (href, "")
            return source_target(ident)

        doc.preamble_html = _linkify_prose(doc.preamble_html, preamble_resolve)
    return three


__all__ = [
    "MIN_IDENT_LEN",
    "build_global_entry_map",
    "build_ident_map",
    "build_source_index",
    "linkify_all",
    "linkify_document",
]
