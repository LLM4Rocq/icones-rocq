"""Real Coq-level dependency edges, parsed from ``.glob`` files.

The graph's *doc-co-reference* edges (``tools.auditor.xref.build_entry_edges``)
connect entry ``A`` to entry ``B`` when ``A``'s statement / prose / snippet
**text** names an identifier ``B`` documents.  That misses dependencies the
docs describe narratively: a proof that *uses* a lemma without ever spelling
its backticked name in the surrounding prose.

Coq's ``.glob`` files (one per ``theories/**/*.v``, emitted by ``coqc
-emit-glob``) record every identifier *reference* with a byte range and every
top-level object's *definition*.  Parsing them yields a faithful proof-level
dependency relation: for a documented lemma ``L`` we collect every identifier
``L``'s statement-and-proof region *uses*, then map those used identifiers back
to the entries that *document* them.  The result is the ``depends`` edge kind
(real Coq dependency), kept distinct from the ``mentions`` kind (doc
co-reference).

``.glob`` line grammar (the two forms we consume):

* **definition** — ``<kind> <bytestart>:<byteend> <modpath> <name>`` where
  ``<kind>`` is ``def``/``thm``/``lem``/``prf``/``abbrev``/``var``/``not``/…
  Top-level proof-bearing objects (``def``/``thm``/``lem``/``prf``) carry a
  ``<>`` modpath; section variables / local lets carry the *section* name.
* **reference** — ``R<bytestart>:<byteend> <modpath> <dotpath> <localname>
  <refkind>`` — a *use* of ``<modpath>.<localname>`` at that byte offset.

The byte offsets inside a proof are *elaboration*-ordered, not source-ordered,
so a span cannot be delimited by "next larger offset".  Instead we walk the
file **line by line**: a definition line opens a region that owns every
subsequent reference line until the next definition line.  This matches how
coqdoc streams a ``.glob`` (declaration, then its references, then the next
declaration), and correctly attributes each ``R`` line to the object whose
body it belongs to.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Iterable

from .schema import ALL_TABS, Entry, ThreeTabDocument

#: ``.glob`` definition line: ``<kind> <bs>:<be> <modpath> <name>``.  The name
#: may carry trailing tokens for notations; we keep only the first token.
_GLOB_DEF_RE = re.compile(
    r"^(def|thm|lem|prf|abbrev|var|not|constr|proj|scheme|rec|ind|sec|coind|inst)"
    r"\s+\d+:\d+\s+(\S+)\s+(\S.*)$"
)

#: ``.glob`` reference line:
#: ``R<bs>:<be> <modpath> <dotpath> <localname> <refkind>``.
_GLOB_REF_RE = re.compile(r"^R\d+:\d+\s+(\S+)\s+\S+\s+(\S+)\s+(\S+)\s*$")

#: Reference kinds that name a *defined object* we may depend on (lemmas,
#: definitions, constructors, fields, instances).  Notations (``not``),
#: section variables (``var``), binders and library module markers are not
#: dependencies on documented entries.
_DEP_REF_KINDS = frozenset(
    {"def", "thm", "lem", "prf", "constr", "proj", "inst", "ind", "rec", "scheme"}
)


def parse_glob_uses(text: str) -> dict[str, set[str]]:
    """Parse one ``.glob`` file body into ``{object_name: {used_idents}}``.

    Walks ``text`` line by line.  A definition line opens the *current*
    region; every following reference line whose kind is a real object
    reference (see :data:`_DEP_REF_KINDS`) contributes its ``<localname>``
    to the current region's use-set.  Only the bare ``<localname>`` is kept
    (the last component of the dotted path) so it can be matched against an
    entry's ``rocq_idents``.  Self-references are *not* filtered here; the
    edge builder drops self-edges downstream.

    Multiple definition lines with the same name (re-opened sections,
    overloaded local lets) accumulate into one use-set — harmless, since we
    only query documented top-level names.
    """
    uses: dict[str, set[str]] = {}
    current: str | None = None
    for line in text.splitlines():
        m = _GLOB_DEF_RE.match(line)
        if m is not None:
            name = m.group(3).split()[0].strip()
            current = name
            uses.setdefault(current, set())
            continue
        r = _GLOB_REF_RE.match(line)
        if r is not None and current is not None:
            localname, refkind = r.group(2), r.group(3)
            if refkind in _DEP_REF_KINDS and localname != "<>":
                # Keep the bare local name (drop any dotted qualifier).
                uses[current].add(localname.rsplit(".", 1)[-1])
    return uses


def _glob_path_for(vfile_rel: str, theories_root: Path) -> Path | None:
    """Map a repo-relative ``theories/…/foo.v`` to its sibling ``.glob``.

    ``vfile_rel`` is the entry's ``rocq_files`` path (e.g.
    ``theories/programs/ex_reject_model.v``); the ``.glob`` sits next to the
    ``.v`` under ``theories_root``'s parent.  Returns ``None`` if the path is
    not under ``theories/`` or has no ``.v`` suffix.
    """
    rel = vfile_rel.strip()
    if not rel.endswith(".v"):
        return None
    base = theories_root.parent
    candidate = (base / rel).with_suffix(".glob")
    return candidate


def load_glob_uses(
    theories_root: str | Path, vfiles: Iterable[str]
) -> tuple[dict[str, set[str]], list[str]]:
    """Load and merge ``{object_name: {used_idents}}`` for the given ``.v``s.

    ``vfiles`` is the set of repo-relative ``.v`` paths the documented
    entries reference (their ``rocq_files`` paths).  For each we read the
    sibling ``.glob`` and merge its per-object use-sets.  Returns
    ``(uses, missing)`` where ``missing`` is the list of ``.v`` paths whose
    ``.glob`` was absent or unreadable — the caller turns a non-empty
    ``missing`` into a build NOTICE and degrades gracefully.
    """
    theories_root = Path(theories_root)
    merged: dict[str, set[str]] = {}
    missing: list[str] = []
    for vfile in sorted(set(vfiles)):
        gpath = _glob_path_for(vfile, theories_root)
        if gpath is None:
            continue
        if not gpath.is_file():
            missing.append(vfile)
            continue
        try:
            text = gpath.read_text(encoding="utf-8")
        except OSError:
            missing.append(vfile)
            continue
        for name, used in parse_glob_uses(text).items():
            if used:
                merged.setdefault(name, set()).update(used)
    return merged, missing


def _entry_owned_names(entry: Entry) -> list[str]:
    """The Coq object names an entry *documents* — its ``rocq_idents``.

    These are the names whose ``.glob`` use-sets define the entry's real
    dependencies.  No filtering beyond what the entry already carries; the
    edge builder validates targets against the documented-ident map.
    """
    return list(entry.rocq_idents)


def build_glob_edges(
    three: ThreeTabDocument,
    theories_root: str | Path,
) -> tuple[list[tuple[tuple[str, str], tuple[str, str]]], list[str]]:
    """Real Coq dependency edges ``A -> B`` derived from ``.glob`` files.

    For each documented entry ``A`` and each Coq object name ``A``
    documents, look up that object's ``.glob`` use-set, map every used
    identifier through the cross-tab documented-ident map
    (:func:`tools.auditor.xref.build_global_entry_map`) to the entry ``B``
    that *documents* it, and emit ``A -> B``.  Only edges to **other
    documented** entries are kept (this bounds the edge count: a proof uses
    hundreds of idents but only a handful are themselves documented nodes).
    Self-edges and duplicates are dropped; the list is sorted for
    determinism.

    Returns ``(edges, notices)``.  ``notices`` is a list of human-readable
    strings describing graceful degradation (e.g. ``.glob`` files that were
    not found, so those files' real dependencies are absent and only
    doc-co-reference edges cover them).  ``notices`` is *never* a parser
    warning — a missing ``.glob`` must not trip ``--strict``.
    """
    from .xref import build_global_entry_map

    entry_map = build_global_entry_map(three)

    # The (tab, id) set of real nodes + the entries to source edges from.
    known: set[tuple[str, str]] = set()
    owners: list[tuple[str, str, Entry]] = []
    vfiles: set[str] = set()
    for tab in ALL_TABS:
        doc = three.tab(tab)
        seen: set[int] = set()
        for section in _walk_sections(doc):
            for entry in section:
                if id(entry) in seen:
                    continue
                seen.add(id(entry))
                known.add((tab, entry.id))
                owners.append((tab, entry.id, entry))
                for rf in entry.rocq_files:
                    if rf.path:
                        vfiles.add(rf.path)

    uses, missing = load_glob_uses(theories_root, vfiles)

    notices: list[str] = []
    if not uses and missing:
        notices.append(
            "no .glob files found next to theories/ sources "
            f"({len(missing)} .v file(s) had no sibling .glob); "
            "real Coq dependency edges are unavailable — falling back to "
            "doc co-reference edges only. Build theories with "
            "`coqc -emit-glob` (the default) to enable them."
        )
    elif missing:
        notices.append(
            f"{len(missing)} .v file(s) had no sibling .glob; their real "
            "Coq dependencies are omitted (doc co-reference still covers them)."
        )

    edges: set[tuple[tuple[str, str], tuple[str, str]]] = set()
    for tab, eid, entry in owners:
        src = (tab, eid)
        used: set[str] = set()
        for name in _entry_owned_names(entry):
            used |= uses.get(name, set())
        for ident in used:
            tgt = entry_map.get(ident)
            if tgt is None or tgt == src or tgt not in known:
                continue
            edges.add((src, tgt))
    return sorted(edges), notices


def _walk_sections(doc) -> Iterable[list[Entry]]:
    """Yield each section's entry list (sections, chapters, beyond)."""
    for section in doc.sections:
        yield section.entries
    for chapter in doc.chapters:
        for section in chapter.sections:
            yield section.entries
    for contrib in doc.beyond:
        yield contrib.entries


__all__ = ["parse_glob_uses", "load_glob_uses", "build_glob_edges"]
