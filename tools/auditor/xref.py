"""Clickable identifier cross-references inside highlighted snippets.

Post-parse, pre-render pass: once a tab's :class:`~tools.auditor.schema.
Document` is fully assembled, build an ``{ident: entry_id}`` map from
every entry's ``rocq_idents`` (sections, chapters AND beyond trees) and
wrap matching identifier tokens in each snippet's Pygments HTML in
``<a class="code-xref" …>`` anchors pointing at the defining entry's
page.

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
  ident's page); otherwise first-wins in document order.
* **URL prefix** — every page that embeds snippet HTML lives at depth 1
  within its tab (``sections/x.html``, ``entries/x.html``,
  ``beyond/x.html``; chapter and index pages only show counts), so a
  uniform relative ``../entries/<id>.html`` href resolves everywhere.
* **Self-links** — when linkifying a snippet owned by entry E,
  occurrences mapping back to E are left unwrapped (a self-link is
  noise on E's own page).
* **Idempotency** — the token regex matches ``[^<]+`` span bodies only;
  a span already containing an ``<a>`` can never match again, so
  running the pass twice is a no-op.

Prose cross-references
----------------------
The same ``{ident: entry_id}`` map also linkifies prose: statement
HTML, entry detail prose, section/chapter intros and notes.  Prose is
rendered by the parser's ``_inline_to_html`` into ``<code>ident</code>``
spans (never Pygments).  We wrap a ``<code>`` body in a ``code-xref``
anchor when, after HTML-unescape, it ``fullmatch``es the identifier
regex, is at least :data:`MIN_IDENT_LEN` long and is a known map key.
Math / notation ``<code>`` (spaces, operators, ``⟦``, ``∫``, ``·`` …)
never matches the identifier regex and is left untouched, as are
self-links (an ident mapping back to the owning entry).  The ``[^<]+``
body discipline keeps the pass idempotent: a ``<code>`` already holding
an ``<a>`` cannot re-match.
"""

from __future__ import annotations

import html as html_mod
import re

from .schema import CoqSnippet, Document, Entry

#: Identifiers shorter than this are never linkified (over-link noise).
MIN_IDENT_LEN = 4

#: Shape of a linkable Rocq identifier — plain name, no dots/operators.
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

#: A single Pygments name token.  ``[^<]+`` keeps the match within one
#: leaf span: spans that already contain markup (e.g. an ``<a>`` from a
#: previous pass) can never match, which makes the pass idempotent.
_NAME_SPAN_RE = re.compile(r'<span class="(n|nf|nb|nc)">([^<]+)</span>')

#: Relative href prefix from any snippet-embedding page (all depth 1
#: within the tab) back to the tab root.
_HREF_PREFIX = "../"

#: A single ``<code>…</code>`` prose span.  ``[^<]+`` keeps the match
#: within one leaf span: a ``<code>`` already containing markup (e.g. an
#: ``<a>`` from a previous pass) can never match, keeping the pass
#: idempotent.
_CODE_SPAN_RE = re.compile(r"<code>([^<]+)</code>")


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

    for section in doc.sections:
        for entry in section.entries:
            consider(entry)
    for chapter in doc.chapters:
        for section in chapter.sections:
            for entry in section.entries:
                consider(entry)
    for contrib in doc.beyond:
        for entry in contrib.entries:
            consider(entry)
    return mapping


def _linkify_html(
    highlighted_html: str,
    mapping: dict[str, str],
    owner_entry_id: str | None,
) -> str:
    """Wrap known-ident name tokens of one snippet's HTML in anchors."""

    def repl(m: re.Match[str]) -> str:
        cls, escaped_tok = m.group(1), m.group(2)
        ident = html_mod.unescape(escaped_tok)
        target = mapping.get(ident)
        if target is None or target == owner_entry_id:
            return m.group(0)
        return (
            f'<span class="{cls}">'
            f'<a class="code-xref" href="{_HREF_PREFIX}entries/{target}.html">'
            f"{escaped_tok}</a></span>"
        )

    return _NAME_SPAN_RE.sub(repl, highlighted_html)


def _linkify_prose(
    prose_html: str,
    mapping: dict[str, str],
    owner_entry_id: str | None,
) -> str:
    """Wrap known-ident ``<code>`` prose spans in ``code-xref`` anchors.

    Only ``<code>`` bodies that, after HTML-unescape, are a single
    identifier (``_IDENT_RE.fullmatch``), at least :data:`MIN_IDENT_LEN`
    long and a key in ``mapping`` are wrapped.  Math / notation spans
    (spaces, operators, non-identifier glyphs) never match the regex and
    are returned verbatim, as are self-links and unknown idents.
    """
    if not prose_html or "<code>" not in prose_html:
        return prose_html

    def repl(m: re.Match[str]) -> str:
        escaped_tok = m.group(1)
        ident = html_mod.unescape(escaped_tok)
        if len(ident) < MIN_IDENT_LEN or not _IDENT_RE.fullmatch(ident):
            return m.group(0)
        target = mapping.get(ident)
        if target is None or target == owner_entry_id:
            return m.group(0)
        return (
            f"<code>"
            f'<a class="code-xref" href="{_HREF_PREFIX}entries/{target}.html">'
            f"{escaped_tok}</a></code>"
        )

    return _CODE_SPAN_RE.sub(repl, prose_html)


def linkify_document(doc: Document) -> Document:
    """Linkify every snippet of ``doc`` in place; returns ``doc``.

    The beyond compat shim aliases Section/Entry objects into
    ``doc.beyond``, so snippets are deduplicated by object identity to
    process each exactly once (the pass is idempotent anyway, but this
    keeps it single-shot).
    """
    mapping = build_ident_map(doc)
    if not mapping:
        return doc

    seen: set[int] = set()

    def do_snippets(snips: list[CoqSnippet], owner: str | None) -> None:
        for s in snips:
            if id(s) in seen:
                continue
            seen.add(id(s))
            s.highlighted_html = _linkify_html(s.highlighted_html, mapping, owner)

    def do_entry(entry: Entry) -> None:
        entry.statement_html = _linkify_prose(
            entry.statement_html, mapping, entry.id
        )
        if entry.detail is not None:
            do_snippets(entry.detail.snippets, entry.id)
            entry.detail.prose_html = _linkify_prose(
                entry.detail.prose_html, mapping, entry.id
            )

    for section in doc.sections:
        section.intro_html = _linkify_prose(section.intro_html, mapping, None)
        section.notes_html = _linkify_prose(section.notes_html, mapping, None)
        do_snippets(section.snippets, None)
        for entry in section.entries:
            do_entry(entry)
    for chapter in doc.chapters:
        chapter.intro_html = _linkify_prose(chapter.intro_html, mapping, None)
        chapter.notes_html = _linkify_prose(chapter.notes_html, mapping, None)
        for section in chapter.sections:
            section.intro_html = _linkify_prose(section.intro_html, mapping, None)
            section.notes_html = _linkify_prose(section.notes_html, mapping, None)
            do_snippets(section.snippets, None)
            for entry in section.entries:
                do_entry(entry)
    for contrib in doc.beyond:
        contrib.intro_html = _linkify_prose(contrib.intro_html, mapping, None)
        contrib.notes_html = _linkify_prose(contrib.notes_html, mapping, None)
        do_snippets(contrib.snippets, None)
        for entry in contrib.entries:
            do_entry(entry)
    doc.preamble_html = _linkify_prose(doc.preamble_html, mapping, None)
    return doc


__all__ = [
    "MIN_IDENT_LEN",
    "build_ident_map",
    "linkify_document",
]
