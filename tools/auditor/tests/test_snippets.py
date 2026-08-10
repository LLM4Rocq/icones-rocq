"""Tests for the live-snippet resolver (``tools/auditor/snippets.py``).

Every test builds a throw-away ``theories/`` tree in ``tmp_path`` so the
suite is independent of the real corpus *and* of whether the project has
been compiled (``.glob`` files are build artefacts; CI never has them).
The last test drives the full parser to check the wiring end-to-end.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make ``tools.auditor`` importable when running from the repo root.
ROOT = Path(__file__).resolve().parents[2]
if str(ROOT.parent) not in sys.path:
    sys.path.insert(0, str(ROOT.parent))

from tools.auditor.coqdoc import CoqProjectBinding, CoqdocResolver
from tools.auditor.parser import parse, snippet_stats
from tools.auditor.snippets import (
    SnippetResolver,
    _normalise_code,  # noqa: PLC2701 — tested intentionally
    clear_index_cache,
)


def _code(highlighted_html: str) -> str:
    """Plain text of a Pygments-highlighted block (drop tags, unescape)."""
    import html as html_mod
    import re as re_mod

    return html_mod.unescape(re_mod.sub(r"<[^>]+>", "", highlighted_html))


SOURCE = '''\
(** The precone axioms. *)
HB.mixin Record isPrecone (R : realType) (P : Type) := {
  precone_zero : P;
  precone_add  : P -> P -> P;
}.

#[short(type="preconeType")]
HB.structure Definition Precone (R : realType) := { P of isPrecone R P }.

Lemma add0p (P : preconeType R) (x : P) :
  precone_add precone_zero x = x.
Proof.
by rewrite precone_addC precone_add0.
Qed.

Definition twice (P : preconeType R) (x : P) : P :=
  precone_add x x.

Inductive expr :=
  (* a literal *)
  | e_lit (n : nat)
  (* a sum *)
  | e_add (a b : expr)
  | e_neg (a : expr).

Notation "x '+p' y" := (precone_add x y) (at level 50) : cone_scope.

HB.instance Definition _ (R : realType) :=
  @isPrecone.Build R unit tt (fun _ _ => tt).
'''


@pytest.fixture()
def resolver(tmp_path: Path) -> SnippetResolver:
    clear_index_cache()
    theories = tmp_path / "theories" / "cones"
    theories.mkdir(parents=True)
    (theories / "precone.v").write_text(SOURCE, encoding="utf-8")
    yield SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    clear_index_cache()


VFILE = "theories/cones/precone.v"


# -- statement extraction ---------------------------------------------------


def test_lemma_statement_stops_before_proof(resolver: SnippetResolver):
    decl = resolver.lookup("add0p", VFILE)
    assert decl is not None
    assert decl.text.startswith("Lemma add0p")
    assert decl.text.rstrip().endswith("precone_add precone_zero x = x.")
    assert "Proof." not in decl.text
    assert "Qed." not in decl.text
    assert decl.start_line == 10


def test_record_body_is_part_of_the_statement(resolver: SnippetResolver):
    decl = resolver.lookup("isPrecone", VFILE)
    assert decl is not None
    assert decl.keyword == "HB.mixin Record"
    assert "precone_add  : P -> P -> P;" in decl.text
    assert decl.text.rstrip().endswith("}.")


def test_attribute_line_is_part_of_the_declaration(resolver: SnippetResolver):
    decl = resolver.lookup("Precone", VFILE)
    assert decl is not None
    assert decl.text.startswith('#[short(type="preconeType")]\nHB.structure')


def test_definition_keeps_its_body(resolver: SnippetResolver):
    decl = resolver.lookup("twice", VFILE)
    assert decl is not None
    assert decl.text.rstrip().endswith("precone_add x x.")


def test_notation_is_resolved_by_its_string(resolver: SnippetResolver):
    decl = resolver.lookup_notation("x '+p' y", VFILE)
    assert decl is not None
    assert "at level 50" in decl.text
    # Whitespace inside the notation string is not significant.
    assert resolver.lookup_notation("x   '+p'  y", VFILE) is decl


def test_inductive_constructors_are_indexed(resolver: SnippetResolver):
    decl = resolver.lookup_constructor("e_add", VFILE)
    assert decl is not None
    assert decl.text.strip() == "| e_add (a b : expr)"
    # The trailing ``.`` of the family is dropped from the last case…
    last = resolver.lookup_constructor("e_neg", VFILE)
    assert last is not None and last.text.strip() == "| e_neg (a : expr)"
    # …and the comment documenting the *next* case is not absorbed.
    first = resolver.lookup_constructor("e_lit", VFILE)
    assert first is not None and "a sum" not in first.text


def test_unknown_identifier_does_not_resolve(resolver: SnippetResolver):
    assert resolver.lookup("no_such_lemma", VFILE) is None


# -- block resolution -------------------------------------------------------


def test_stale_paste_is_replaced_by_the_source(resolver: SnippetResolver):
    raw = (
        f"(* {VFILE} *)\n"
        "Lemma add0p (P : preconeType R) (x : P) :\n"
        "  precone_add precone_zero x = x.  (* WRONG, and reformatted *)\n"
    )
    block = resolver.resolve_block(raw, VFILE, context="t")
    assert block.n_units == 1
    assert block.n_resolved == 1
    assert block.units[0].name == "add0p"
    assert block.changed
    assert block.source_file == VFILE
    assert block.start_line == 10
    assert f"(* {VFILE} *)" in block.text  # the lead comment is preserved
    assert "WRONG" not in block.text
    # Same text modulo whitespace/comments ⇒ NOT stale.
    assert block.n_stale == 0


def test_materially_different_paste_is_flagged_stale(resolver: SnippetResolver):
    raw = (
        f"(* {VFILE} *)\n"
        "Lemma add0p (P : preconeType R) (x : P) :\n"
        "  precone_add x precone_zero = x.\n"
    )
    block = resolver.resolve_block(raw, VFILE, context="t")
    assert block.n_resolved == 1
    assert block.n_stale == 1
    assert "precone_add precone_zero x = x." in block.text


def test_editorial_lines_between_declarations_survive(resolver: SnippetResolver):
    raw = (
        f"(* {VFILE} *)\n"
        "Lemma add0p : True.\n"
        "\n"
        "(** Hand-written gloss that must survive. *)\n"
        "Definition twice := 0.\n"
    )
    block = resolver.resolve_block(raw, VFILE, context="t")
    assert block.n_resolved == 2
    assert "(** Hand-written gloss that must survive. *)" in block.text
    assert "precone_add x x." in block.text


def test_attribute_lines_are_not_duplicated(resolver: SnippetResolver):
    raw = (
        f"(* {VFILE} *)\n"
        '#[short(type="preconeType")]\n'
        "HB.structure Definition Precone := { P of isPrecone R P }.\n"
    )
    block = resolver.resolve_block(raw, VFILE, context="t")
    assert block.n_resolved == 1
    assert block.text.count('#[short(type="preconeType")]') == 1


def test_constructor_fragment_is_resolved(resolver: SnippetResolver):
    raw = f"(* {VFILE} *)\n  | e_add (a b : expr)  (* stale gloss *)\n"
    block = resolver.resolve_block(raw, VFILE, context="t")
    assert block.n_units == 1
    assert block.units[0].keyword == "constructor"
    assert block.n_resolved == 1
    assert "| e_add (a b : expr)" in block.text


def test_anonymous_hb_instance_matches_by_builder(resolver: SnippetResolver):
    raw = (
        f"(* {VFILE} *)\n"
        "HB.instance Definition _ := @isPrecone.Build R unit (* … *).\n"
    )
    block = resolver.resolve_block(raw, VFILE, context="t")
    assert block.n_resolved == 1
    assert "fun _ _ => tt" in block.text
    # A builder that exists nowhere in the file must NOT match some other
    # anonymous instance.
    other = resolver.resolve_block(
        f"(* {VFILE} *)\nHB.instance Definition _ := @isCone.Build R unit.\n",
        VFILE,
        context="t",
    )
    assert other.n_resolved == 0


def test_unresolvable_declaration_falls_back_and_is_reported(
    resolver: SnippetResolver,
):
    raw = f"(* {VFILE} *)\nLemma ghost_lemma : 1 = 1.\n"
    block = resolver.resolve_block(raw, VFILE, context="ctx")
    assert block.n_units == 1 and block.n_resolved == 0
    assert block.text == raw  # rendered exactly as pasted
    assert not block.changed
    assert resolver.stats.fallbacks[-1][0] == "ctx"
    assert resolver.stats.fallbacks[-1][1] == "ghost_lemma"


def test_block_without_declarations_is_reported_as_opaque(
    resolver: SnippetResolver,
):
    raw = f"(* {VFILE} *)\n[ let \"x\" := 1 in # \"x\" ]\n"
    block = resolver.resolve_block(raw, VFILE, context="ctx")
    assert block.n_units == 0
    assert block.text == raw
    assert resolver.stats.opaque == [("ctx", VFILE)]


def test_wrong_provenance_comment_is_reported(resolver: SnippetResolver):
    raw = "(* theories/cones/elsewhere.v *)\nLemma add0p : True.\n"
    block = resolver.resolve_block(
        raw, "theories/cones/elsewhere.v", context="ctx"
    )
    # Unknown provenance ⇒ resolved through the globally-unique name.
    assert block.n_resolved == 1
    assert block.files == [VFILE]
    assert resolver.stats.provenance == [
        ("ctx", "theories/cones/elsewhere.v", VFILE)
    ]


def test_ambiguous_name_across_files_does_not_resolve(tmp_path: Path):
    clear_index_cache()
    for name in ("a", "b"):
        d = tmp_path / "theories" / name
        d.mkdir(parents=True)
        (d / "m.v").write_text("Lemma dup : True.\nProof. done. Qed.\n", "utf-8")
    res = SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    assert res.lookup("dup") is None  # ambiguous ⇒ no guess
    assert res.lookup("dup", "theories/a/m.v") is not None  # hint decides
    clear_index_cache()


def test_missing_theories_tree_is_a_pass_through(tmp_path: Path):
    clear_index_cache()
    res = SnippetResolver(tmp_path / "nowhere")
    raw = "Lemma add0p : True.\n"
    block = res.resolve_block(raw, None, context="t")
    assert not res.available
    assert block.text == raw and block.n_units == 0 and not block.changed


# -- .glob overlay ----------------------------------------------------------


def test_glob_overlay_adds_a_declaration_the_regex_scan_missed(tmp_path: Path):
    """A ``.glob`` ``def`` line lets an unusual layout still be resolved."""
    clear_index_cache()
    d = tmp_path / "theories" / "odd"
    d.mkdir(parents=True)
    src = "Section S.\nDefinition\n  weird_name (x : nat) : nat := x.\nEnd S.\n"
    (d / "m.v").write_text(src, encoding="utf-8")
    # ``weird_name`` sits on the line *after* its keyword, so the regex scan
    # cannot key it; the .glob gives the byte offset of the name token.
    offset = src.index("weird_name")
    (d / "m.glob").write_text(
        f"DIGEST x\nFtest.odd.m\ndef {offset}:{offset + 9} <> weird_name\n",
        encoding="utf-8",
    )
    res = SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    assert res.n_glob_files == 1
    decl = res.lookup("weird_name", "theories/odd/m.v")
    assert decl is not None
    assert decl.text.startswith("Definition\n  weird_name")
    clear_index_cache()


def test_truncated_glob_is_tolerated(tmp_path: Path):
    """A half-written ``.glob`` (mid-rebuild) must not break the build."""
    clear_index_cache()
    d = tmp_path / "theories" / "odd"
    d.mkdir(parents=True)
    (d / "m.v").write_text("Lemma ok : True.\nProof. done. Qed.\n", "utf-8")
    (d / "m.glob").write_text("DIGEST x\ndef 99999:100000 <> \n", "utf-8")
    res = SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    assert res.lookup("ok", "theories/odd/m.v") is not None
    clear_index_cache()


# -- normalisation ----------------------------------------------------------


def test_normalise_code_ignores_whitespace_and_comments():
    a = "Lemma  foo :\n   True.  (* a comment *)"
    b = "(* other *) Lemma foo : True."
    assert _normalise_code(a) == _normalise_code(b)
    assert _normalise_code("Lemma foo : True.") != _normalise_code(
        "Lemma foo : False."
    )


# -- end-to-end through the parser -----------------------------------------


MARKDOWN = """\
# Auditor

## Paper § 2 — Cones

| Paper | English statement | Rocq |
| --- | --- | --- |
| Def 2.1 | The precone axioms. | `isPrecone` — theories/cones/precone.v |

### Def 2.1 (`isPrecone`)

Prose.

```coq
(* theories/cones/precone.v *)
HB.mixin Record isPrecone (R : realType) (P : Type) := {
  precone_zero : P;
}.
```
"""


def test_parser_wires_live_snippets(tmp_path: Path):
    clear_index_cache()
    theories = tmp_path / "theories" / "cones"
    theories.mkdir(parents=True)
    (theories / "precone.v").write_text(SOURCE, encoding="utf-8")
    resolver = CoqdocResolver(
        bindings=[CoqProjectBinding(physical="theories", logical="Icones")],
        github_repo="demo/demo",
        commit="abc123",
    )
    doc, _ = parse(
        MARKDOWN, resolver=resolver, project_root=tmp_path, strict=False
    )
    entry = doc.sections[0].entries[0]
    assert entry.detail is not None
    snip = entry.detail.snippets[0]
    assert snip.resolved
    assert snip.stale  # the paste dropped the ``precone_add`` field
    assert snip.source_file == "theories/cones/precone.v"
    assert snip.source_line == 2
    assert snip.github_url.endswith("theories/cones/precone.v#L2")
    assert snip.coqdoc_url == "docs/Icones.cones.precone.html"
    assert snip.decls == ["isPrecone"]
    assert "precone_add  : P -> P -> P;" in _code(snip.highlighted_html)

    stats = snippet_stats(doc)
    assert stats.blocks == 1 and stats.units_resolved == 1
    assert stats.units_stale == 1
    assert "resolved=1 (100%)" in stats.summary()
    clear_index_cache()


def test_parser_without_sources_keeps_the_pasted_text(tmp_path: Path):
    """No theories/ tree ⇒ byte-identical to the legacy pasted rendering."""
    clear_index_cache()
    resolver = CoqdocResolver(
        bindings=[CoqProjectBinding(physical="theories", logical="Icones")],
        github_repo="demo/demo",
        commit="abc123",
    )
    doc, _ = parse(
        MARKDOWN, resolver=resolver, project_root=tmp_path, strict=False
    )
    snip = doc.sections[0].entries[0].detail.snippets[0]
    assert not snip.resolved and not snip.stale
    assert snip.source_line == 0
    assert "precone_zero : P;" in _code(snip.highlighted_html)
    assert "precone_add" not in _code(snip.highlighted_html)
    clear_index_cache()


# -- .glob / .v mismatch ----------------------------------------------------
#
# The ``.glob`` tree and the ``.v`` tree are INDEPENDENT inputs: CI downloads
# the ``.glob`` files as another workflow's artefact, so they routinely
# describe a neighbouring commit's sources.  Every offset in them is therefore
# untrusted.  ``test_truncated_glob_is_tolerated`` above does NOT cover this —
# its fixture line has an empty name, so ``_GLOB_DEF_RE`` never matches and
# the offset path is never entered at all.


def test_glob_offset_past_end_of_file_is_skipped(tmp_path: Path):
    """An offset beyond the ``.v`` must be dropped, not clamped, not raised.

    A file ending in ``\\n`` makes the offset→line table one entry longer
    than the line list, so an out-of-range offset used to map to
    ``len(lines)`` and index one past the end.
    """
    clear_index_cache()
    d = tmp_path / "theories" / "odd"
    d.mkdir(parents=True)
    src = "Definition foo := 1.\nLemma bar : True.\n"  # note: trailing newline
    (d / "m.v").write_text(src, "utf-8")
    (d / "m.glob").write_text(
        f"DIGEST x\nFtest.odd.m\ndef {len(src) + 500}:{len(src) + 520} <> gone\n",
        "utf-8",
    )
    res = SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    assert res.n_glob_files == 0  # nothing usable was added
    assert res.lookup("foo", "theories/odd/m.v") is not None  # regex index intact
    assert res.lookup("gone", "theories/odd/m.v") is None
    clear_index_cache()


def test_glob_offset_at_exact_file_size_is_skipped(tmp_path: Path):
    """The boundary case: offset == len(bytes) is one past the last line."""
    clear_index_cache()
    d = tmp_path / "theories" / "odd"
    d.mkdir(parents=True)
    src = "Lemma ok : True.\nProof. done. Qed.\n"
    (d / "m.v").write_text(src, "utf-8")
    (d / "m.glob").write_text(
        f"DIGEST x\ndef {len(src)}:{len(src) + 4} <> late\n", "utf-8"
    )
    res = SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    assert res.lookup("ok", "theories/odd/m.v") is not None
    assert res.lookup("late", "theories/odd/m.v") is None
    clear_index_cache()


def test_glob_from_a_longer_revision_of_every_file(tmp_path: Path):
    """A whole tree whose ``.glob`` files describe LONGER ``.v`` sources.

    This is the shape CI now feeds in by construction (the artefact lags the
    checkout by at least one commit), so it must degrade to the regex index
    rather than take the build down.
    """
    clear_index_cache()
    d = tmp_path / "theories" / "pkg"
    d.mkdir(parents=True)
    for i in range(5):
        src = f"Lemma keep_{i} : True.\nProof. done. Qed.\n"
        (d / f"m{i}.v").write_text(src, "utf-8")
        (d / f"m{i}.glob").write_text(
            "DIGEST x\n"
            f"def 3:9 <> keep_{i}\n"
            f"def {len(src) + 40}:{len(src) + 50} <> dropped_{i}\n",
            "utf-8",
        )
    res = SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    for i in range(5):
        assert res.lookup(f"keep_{i}", f"theories/pkg/m{i}.v") is not None
        assert res.lookup(f"dropped_{i}") is None
    clear_index_cache()


# -- the splice guard -------------------------------------------------------


def test_proof_mode_source_does_not_replace_a_pasted_body(tmp_path: Path):
    """``Fixpoint f … : T.`` + ``Proof.`` must not eat a pasted ``:=`` body.

    ``_statement_extent`` correctly stops at the signature, so splicing would
    turn a 20-line pasted interpreter into its two-line type — the deployed
    card would silently lose the whole match.
    """
    clear_index_cache()
    d = tmp_path / "theories" / "pkg"
    d.mkdir(parents=True)
    (d / "m.v").write_text(
        "Fixpoint interp (e : expr) {struct e} : val.\n"
        "Proof. refine (match e with C1 => v1 | C2 => v2 end). Defined.\n",
        "utf-8",
    )
    pasted = (
        "Fixpoint interp (e : expr) {struct e} : val :=\n"
        + "\n".join(f"  | C{i} => v{i}" for i in range(12))
        + "\n  end.\n"
    )
    res = SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    block = res.resolve_block(pasted, "theories/pkg/m.v")
    assert block.text == pasted  # the paste survives verbatim
    assert not block.changed
    unit = block.units[0]
    assert unit.resolved and not unit.spliced
    assert "proof-mode" in unit.mismatch
    assert res.stats.units_mismatched == 1
    clear_index_cache()


def test_curated_excerpt_is_not_replaced_by_a_full_record_dump(tmp_path: Path):
    """A deliberately short quote of a huge record keeps its curation."""
    clear_index_cache()
    d = tmp_path / "theories" / "pkg"
    d.mkdir(parents=True)
    fields = "\n".join(f"  field_{i} : nat;" for i in range(60))
    (d / "m.v").write_text(f"Record Big := {{\n{fields}\n}}.\n", "utf-8")
    pasted = "Record Big := {\n  field_0 : nat;\n  field_1 : nat;\n}.\n"
    res = SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    block = res.resolve_block(pasted, "theories/pkg/m.v")
    assert block.text == pasted
    unit = block.units[0]
    assert unit.resolved and not unit.spliced
    assert "curated excerpt" in unit.mismatch
    # A held-back unit contributes an anchor line but no source *range*.
    assert block.start_line == 1
    assert block.end_line == 0
    clear_index_cache()


def test_a_modest_growth_still_splices(tmp_path: Path):
    """The guard must not smother the feature: normal upgrades go through."""
    clear_index_cache()
    d = tmp_path / "theories" / "pkg"
    d.mkdir(parents=True)
    (d / "m.v").write_text(
        "Lemma grown (a : nat) (b : nat) (c : nat) :\n"
        "  a + b = b + a ->\n"
        "  b + c = c + b ->\n"
        "  a + c = c + a.\n"
        "Proof. done. Qed.\n",
        "utf-8",
    )
    res = SnippetResolver(tmp_path / "theories", repo_root=tmp_path)
    block = res.resolve_block("Lemma grown : commutes.\n", "theories/pkg/m.v")
    assert "b + c = c + b" in block.text
    assert block.changed
    unit = block.units[0]
    assert unit.resolved and unit.spliced and unit.stale
    assert res.stats.units_mismatched == 0
    clear_index_cache()
