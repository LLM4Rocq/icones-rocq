#!/usr/bin/env python3
"""Blueprint-to-docs citation parity baseline.

WHY THIS EXISTS
===============
``blueprint/`` is FROZEN as of 2026-08 (see the banner at the top of
``blueprint/src/chapters/00-intro.tex``) and is scheduled for deletion once
the auditor sources — ``docs/PAPER.md``, ``docs/PPL.md``,
``docs/EXAMPLES.md`` — demonstrably cover everything the blueprint cites.

This script measures that coverage.  It must be run and its output checked
in as ``tools/blueprint_parity_baseline.json`` **before** any module rename
or file move, so that later phases can re-run it and compare against a
baseline taken while the blueprint's citations were still accurate.  Once
modules move, the blueprint's stale paths stop resolving and the measurement
is no longer meaningful — hence the baseline.

USAGE
=====
    python3 tools/blueprint_parity.py                    # JSON on stdout
    python3 tools/blueprint_parity.py -o tools/blueprint_parity_baseline.json
    python3 tools/blueprint_parity.py --summary          # human-readable table
    python3 tools/blueprint_parity.py --gate             # exit 1 if the gate fails
    python3 tools/blueprint_parity.py --allowlist FILE   # newline-separated names

THE DELETION GATE
=================
The gate for eventually deleting ``blueprint/`` is:

    **"absent" is empty for chapters 01-08, modulo an allowlist.**

Chapters 01-08 are the paper chapters and their target document is
``docs/PAPER.md``.  Chapter ``09-cbv`` is the beyond-the-paper CBV/PPL
material; its targets are ``docs/PPL.md`` + ``docs/EXAMPLES.md``, and it is
reported but is NOT part of the gate (``--gate`` ignores it), because the
PPL layer is documented top-down rather than citation-by-citation.  An
allowlist file (one name per line, ``#`` comments allowed) records the
citations that are deliberately not mirrored in the docs.

WHAT IT DOES
============
(a) Extracts every ``\\rocq{...}`` from ``blueprint/src/chapters/*.tex``.
    ``\\rocq`` is the *only* citation macro (confirmed against
    ``blueprint/src/macros/{common,print,web}.tex``: ``print.tex`` defines
    ``\\rocq[1]``, ``\\rocqok``, ``\\notready``, ``\\mathcompok``,
    ``\\discussion``; only ``\\rocq`` takes a Rocq name).  LaTeX comments are
    stripped first, so the convention lines in ``00-intro.tex``'s header
    comment (``\\rocq{Icones.<dir>.<File>.<name>}``) are not picked up.

(b) Resolves each cited name's FINAL identifier segment against an index of
    declared identifiers built from ``theories/**/*.v``.  The index regex
    covers Definition / Lemma / Theorem / Corollary / Fact / Remark /
    Example / Notation / Record / Structure / Inductive / Fixpoint /
    CoFixpoint / Variant / Class / Instance / Canonical, with
    Local/Global/Program/Export/Polymorphic and ``#[...]`` attribute
    prefixes, plus HB.mixin / HB.structure / HB.factory / HB.instance /
    HB.builders.  Coq comments are stripped before indexing so that prose
    inside ``(* ... *)`` cannot mint identifiers.  Record/mixin *fields* are
    indexed too (the blueprint cites e.g. ``cone.cnorm``, a mixin field).

(c) Presence-checks each cited final segment against its chapter's TARGET
    document only, matching ONLY inside backticked spans or fenced code
    blocks, with Rocq-aware word boundaries (``_`` and ``'`` are identifier
    characters).  LaTeX math (``$..$``, ``$$..$$``, ``\\(..\\)``, ``\\[..\\]``)
    is stripped from the prose before inline-code spans are harvested.
    Restricting to code context is what kills the proven "Delta-style" false
    positives: an identifier such as ``Delta`` otherwise matches the prose
    LaTeX ``\\Delta`` and every chapter looks fully covered.

OUTPUT
======
JSON with a ``meta`` block and one entry per chapter holding the four
spec'd lists (all sorted, de-duplicated, and holding the FULL cited names):

    cited                 every \\rocq{...} name in the chapter
    resolved_in_code      those whose final segment is declared in theories/
    present_in_target_doc those whose final segment appears in code context
                          in the chapter's target doc(s)
    absent                cited - present_in_target_doc  (the gate set)

plus two conveniences: ``absent_unresolved`` (the subset of ``absent`` that
does not resolve in ``theories/`` either — stale citations, prime allowlist
material) and ``counts``.

No Rocq or LaTeX toolchain is required; this is pure text analysis.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

CHAPTERS_DIR = REPO_ROOT / "blueprint" / "src" / "chapters"
THEORIES_DIR = REPO_ROOT / "theories"
DOCS_DIR = REPO_ROOT / "docs"

#: Chapter stem -> target documents.  Chapters 01-08 are the paper chapters
#: (docs/PAPER.md); 09-cbv is the beyond-the-paper CBV/PPL material.
#: 00-intro is prose only and is measured against PAPER.md for completeness.
PAPER_DOCS = ("docs/PAPER.md",)
PPL_DOCS = ("docs/PPL.md", "docs/EXAMPLES.md")

#: Chapters whose "absent" list the deletion gate looks at.
GATED_CHAPTERS = (
    "01-cones",
    "02-mcones",
    "03-icones",
    "04-linhom",
    "05-skern",
    "06-tensor",
    "07-stable",
    "08-exponential",
)


def target_docs_for(stem: str) -> tuple[str, ...]:
    """Map a chapter file stem to the doc(s) that must cover its citations."""
    return PPL_DOCS if stem.startswith("09") else PAPER_DOCS


# --------------------------------------------------------------------------
# (a) blueprint citations
# --------------------------------------------------------------------------

#: The one citation macro.  Its argument never nests braces (verified over
#: all chapters), so a flat ``[^{}]*`` body is exact.
ROCQ_CITE_RE = re.compile(r"\\rocq\{([^{}]*)\}")

#: Placeholder citations in documentation-of-conventions text.
_PLACEHOLDER_RE = re.compile(r"[<>]|\.\.\.")


def strip_tex_comments(text: str) -> str:
    """Drop LaTeX comments (unescaped ``%`` to end of line), keeping lines."""
    out = []
    for line in text.split("\n"):
        i, n = 0, len(line)
        cut = None
        while i < n:
            c = line[i]
            if c == "\\":
                i += 2
                continue
            if c == "%":
                cut = i
                break
            i += 1
        out.append(line if cut is None else line[:cut])
    return "\n".join(out)


def extract_citations(path: Path) -> list[str]:
    """Every ``\\rocq{...}`` argument in *path*, in source order."""
    text = strip_tex_comments(path.read_text(encoding="utf-8"))
    names = []
    for m in ROCQ_CITE_RE.finditer(text):
        name = m.group(1).strip()
        if not name or _PLACEHOLDER_RE.search(name):
            continue
        names.append(name)
    return names


def final_segment(name: str) -> str:
    """The identifier part of a dotted ``Icones.dir.File.ident`` citation."""
    return name.rsplit(".", 1)[-1]


# --------------------------------------------------------------------------
# (b) declared-identifier index over theories/**/*.v
# --------------------------------------------------------------------------

_IDENT = r"[A-Za-z_][A-Za-z0-9_']*"

_ATTRS = r"(?:#\[[^\]]*\]\s*)*"
_MODIFIERS = r"(?:(?:Local|Global|Program|Export|Polymorphic|Monomorphic|Private|Time)\s+)*"

_VERNAC_KEYWORDS = (
    "Definition|Lemma|Theorem|Corollary|Fact|Remark|Example|Notation|Record|"
    "Structure|Inductive|Fixpoint|CoFixpoint|Variant|Class|Instance|Canonical"
)

#: Plain vernacular declarations.  Anchored at a line start (possibly behind
#: ``#[...]`` attributes and Local/Global/... modifiers, which may sit on
#: their own lines) so that keywords occurring mid-term are not mistaken for
#: declarations.
DECL_RE = re.compile(
    rf"^[ \t]*{_ATTRS}{_MODIFIERS}(?:{_VERNAC_KEYWORDS})\s+({_IDENT})",
    re.MULTILINE,
)

#: Hierarchy-Builder declarations.  ``HB.mixin Record isC``,
#: ``HB.structure Definition C``, ``HB.factory Record f``,
#: ``HB.instance Definition _``, ``HB.builders Context isC``.
HB_DECL_RE = re.compile(
    rf"^[ \t]*{_ATTRS}HB\.(?:mixin|structure|factory|instance|builders)\s+"
    rf"(?:Record|Definition|Context)?\s*({_IDENT})",
    re.MULTILINE,
)

#: Fields of a ``Record`` / ``HB.mixin Record`` body: ``  name : ty ;``.
#: The blueprint cites mixin fields directly (e.g. ``cones.cone.cnorm``), so
#: an index without them reports spurious "not in the code" citations.
FIELD_RE = re.compile(rf"^[ \t]+({_IDENT})\s*:[^=:]", re.MULTILINE)

#: Keywords that FIELD_RE must never swallow (a tactic/term line can look
#: like a field).  Cheap denylist; false negatives here are harmless.
_FIELD_DENY = {
    "forall", "fun", "let", "in", "match", "with", "end", "if", "then",
    "else", "return", "Proof", "Qed", "Defined", "Admitted", "by", "move",
    "case", "elim", "apply", "exact", "rewrite", "have", "suff", "wlog",
    "Context", "Variable", "Variables", "Hypothesis", "Hypotheses",
    "Implicit", "Arguments", "Section", "Module", "End", "Import", "Require",
    "Export", "Open", "Close", "Scope", "Notation", "Local", "Global",
}


def strip_coq_comments(text: str) -> str:
    """Remove ``(* ... *)`` comments (nested), preserving newlines.

    String literals are honoured so that ``"(*"`` inside a notation string
    does not open a comment.
    """
    out = []
    i, n, depth = 0, len(text), 0
    in_string = False
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_string:
            if c == '"':
                in_string = False
            if depth == 0:
                out.append(c)
            elif c == "\n":
                out.append(c)
            i += 1
            continue
        if c == "(" and nxt == "*":
            depth += 1
            i += 2
            continue
        if c == "*" and nxt == ")" and depth:
            depth -= 1
            i += 2
            continue
        if depth:
            if c == "\n":
                out.append(c)
            i += 1
            continue
        if c == '"':
            in_string = True
        out.append(c)
        i += 1
    return "".join(out)


def build_identifier_index(theories: Path) -> dict[str, list[str]]:
    """Map declared identifier -> sorted repo-relative .v files declaring it."""
    index: dict[str, set[str]] = {}
    for vfile in sorted(theories.rglob("*.v")):
        rel = str(vfile.relative_to(REPO_ROOT))
        src = strip_coq_comments(vfile.read_text(encoding="utf-8"))
        for rx in (DECL_RE, HB_DECL_RE):
            for m in rx.finditer(src):
                ident = m.group(1)
                if ident == "_":
                    continue
                index.setdefault(ident, set()).add(rel)
        for m in FIELD_RE.finditer(src):
            ident = m.group(1)
            if ident in _FIELD_DENY:
                continue
            index.setdefault(ident, set()).add(rel)
    return {k: sorted(v) for k, v in index.items()}


# --------------------------------------------------------------------------
# (c) code-context identifier set of a Markdown document
# --------------------------------------------------------------------------

FENCE_RE = re.compile(r"^[ \t]*(`{3,}|~{3,})[^\n]*\n(.*?)(?:^[ \t]*\1[ \t]*$|\Z)",
                      re.MULTILINE | re.DOTALL)
INLINE_CODE_RE = re.compile(r"(`+)(?!`)(.+?)(?<!`)\1(?!`)", re.DOTALL)
MATH_RE = re.compile(r"\$\$.*?\$\$|\$[^$\n]*\$|\\\(.*?\\\)|\\\[.*?\\\]", re.DOTALL)

#: A Rocq identifier occurrence: not glued to another identifier character.
#: ``_`` and ``'`` are identifier characters in Rocq, and a dotted qualifier
#: (``Icones.cones.cone.cnorm``) counts as an occurrence of ``cnorm``.
_IDENT_CHARS = r"A-Za-z0-9_'"


def code_context_text(md: str) -> str:
    """Concatenate every fenced block and inline-code span of *md*.

    Fenced blocks are harvested (and removed) first so their contents cannot
    be re-parsed as inline spans; LaTeX math is then stripped from the
    remaining prose before inline spans are collected.
    """
    chunks: list[str] = []

    def _take_fence(m: re.Match[str]) -> str:
        chunks.append(m.group(2))
        return "\n"

    prose = FENCE_RE.sub(_take_fence, md)
    prose = MATH_RE.sub(" ", prose)
    for m in INLINE_CODE_RE.finditer(prose):
        chunks.append(m.group(2))
    return "\n".join(chunks)


def code_identifiers(md: str) -> set[str]:
    """All identifier-shaped tokens appearing in code context in *md*."""
    return set(re.findall(rf"[A-Za-z_][{_IDENT_CHARS}]*", code_context_text(md)))


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------


def load_allowlist(path: Path | None) -> set[str]:
    if path is None:
        return set()
    out = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            out.add(line)
    return out


def analyse(allowlist: set[str]) -> dict:
    index = build_identifier_index(THEORIES_DIR)

    doc_idents: dict[str, set[str]] = {}
    for rel in sorted(set(PAPER_DOCS) | set(PPL_DOCS)):
        doc_idents[rel] = code_identifiers(
            (REPO_ROOT / rel).read_text(encoding="utf-8")
        )

    chapters: dict[str, dict] = {}
    for tex in sorted(CHAPTERS_DIR.glob("*.tex")):
        stem = tex.stem
        targets = target_docs_for(stem)
        target_set: set[str] = set()
        for rel in targets:
            target_set |= doc_idents[rel]

        cited = sorted(set(extract_citations(tex)))
        resolved, present, absent, absent_unresolved = [], [], [], []
        for name in cited:
            seg = final_segment(name)
            in_code = seg in index
            in_doc = seg in target_set
            if in_code:
                resolved.append(name)
            if in_doc:
                present.append(name)
            else:
                absent.append(name)
                if not in_code:
                    absent_unresolved.append(name)

        gated = stem in GATED_CHAPTERS
        unallowed = [n for n in absent if n not in allowlist]
        chapters[stem] = {
            "source": str(tex.relative_to(REPO_ROOT)),
            "target_docs": list(targets),
            "gated": gated,
            "cited": cited,
            "resolved_in_code": resolved,
            "present_in_target_doc": present,
            "absent": absent,
            "absent_unresolved": absent_unresolved,
            "absent_not_allowlisted": unallowed,
            "counts": {
                "cited": len(cited),
                "resolved_in_code": len(resolved),
                "present_in_target_doc": len(present),
                "absent": len(absent),
                "absent_unresolved": len(absent_unresolved),
                "absent_not_allowlisted": len(unallowed),
            },
        }

    gate_blockers = sorted(
        {
            n
            for stem, ch in chapters.items()
            if ch["gated"]
            for n in ch["absent_not_allowlisted"]
        }
    )
    return {
        "meta": {
            "tool": "tools/blueprint_parity.py",
            "gate": (
                "blueprint/ may be deleted when 'absent' is empty for chapters "
                "01-08, modulo an allowlist"
            ),
            "citation_macro": "\\rocq",
            "chapters_dir": str(CHAPTERS_DIR.relative_to(REPO_ROOT)),
            "theories_dir": str(THEORIES_DIR.relative_to(REPO_ROOT)),
            "declared_identifiers": len(index),
            "allowlist_size": len(allowlist),
            "gate_chapters": list(GATED_CHAPTERS),
            "gate_pass": not gate_blockers,
            "gate_blockers": len(gate_blockers),
        },
        "chapters": chapters,
    }


def print_summary(report: dict, stream=sys.stdout) -> None:
    hdr = f"{'chapter':<16} {'gate':>4} {'cited':>6} {'in code':>8} {'in doc':>7} {'absent':>7}"
    print(hdr, file=stream)
    print("-" * len(hdr), file=stream)
    for stem, ch in report["chapters"].items():
        c = ch["counts"]
        print(
            f"{stem:<16} {'yes' if ch['gated'] else '-':>4} "
            f"{c['cited']:>6} {c['resolved_in_code']:>8} "
            f"{c['present_in_target_doc']:>7} {c['absent']:>7}",
            file=stream,
        )
    m = report["meta"]
    print(
        f"\ngate ({', '.join(m['gate_chapters'])}): "
        f"{'PASS' if m['gate_pass'] else 'FAIL'} "
        f"({m['gate_blockers']} non-allowlisted absent citation(s))",
        file=stream,
    )


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        prog="python3 tools/blueprint_parity.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("-o", "--out", metavar="JSON",
                   help="write the report here instead of stdout")
    p.add_argument("--allowlist", metavar="FILE", type=Path,
                   help="newline-separated citations exempt from the gate")
    p.add_argument("--summary", action="store_true",
                   help="print a human-readable table (to stderr when -o is used)")
    p.add_argument("--gate", action="store_true",
                   help="exit 1 when a gated chapter has non-allowlisted absences")
    args = p.parse_args(argv)

    report = analyse(load_allowlist(args.allowlist))
    payload = json.dumps(report, indent=2, sort_keys=False) + "\n"

    if args.out:
        Path(args.out).write_text(payload, encoding="utf-8")
        if args.summary:
            print_summary(report, sys.stderr)
    else:
        if args.summary:
            print_summary(report, sys.stdout)
        else:
            sys.stdout.write(payload)

    if args.gate and not report["meta"]["gate_pass"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
