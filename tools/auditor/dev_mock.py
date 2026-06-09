#!/usr/bin/env python3
"""Emit a synthetic data.json matching the auditor schema.

Used by dev_serve.py while the real parser/builder (sibling agent) is in
flight. The default output is the triple-tab document (Paper + PPL +
Examples); pass ``--single`` for the legacy single-Document payload.
"""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone


GH = "icones/icones"


def _file(path, section=None, anchor=None):
    return {
        "path": path,
        "section": section,
        "github_url": f"https://github.com/{GH}/blob/main/{path}",
        "coqdoc_url": f"../coqdoc/{path.replace('/', '.').replace('.v', '.html')}",
        "coqdoc_anchor": anchor,
    }


def _snippet(file, sect, code):
    # Minimal highlighting fake: wrap kw and idents in span classes so the
    # template's <pre> renders something colourful. The real builder uses
    # Pygments — this just shows shape.
    import html as _html
    lines = []
    KW = {"Definition", "Lemma", "Theorem", "Proof", "Qed", "forall",
          "fun", "match", "with", "end", "if", "then", "else",
          "Record", "HB.mixin", "HB.structure", "Section", "Variable",
          "Variables", "Context", "let", "in"}
    for line in code.splitlines():
        rendered = []
        for tok in line.split(" "):
            esc = _html.escape(tok)
            if tok in KW:
                rendered.append(f'<span class="k">{esc}</span>')
            elif tok.startswith("(*") or tok.startswith("*)"):
                rendered.append(f'<span class="c">{esc}</span>')
            else:
                rendered.append(esc)
        lines.append(" ".join(rendered))
    html = "<pre><code>" + "\n".join(lines) + "</code></pre>"
    return {"source_file": file, "source_section": sect, "highlighted_html": html}


def _entry(eid, label, kind, num, sect, status, idents, files, statement,
           prose=None, snippets=None, notes=None, xrefs=None):
    snippets = snippets or []
    notes = notes or []
    return {
        "id": eid,
        "paper_label": label,
        "paper_kind": kind,
        "paper_number": num,
        "paper_section_id": sect,
        "statement_html": statement,
        "rocq_idents": idents,
        "rocq_files": files,
        "status": status,
        "detail": {
            "prose_html": prose or "",
            "notes": notes,
            "snippets": snippets,
        } if (prose or snippets or notes) else None,
        "cross_refs": xrefs or [],
    }


def make_paper_document() -> dict:
    section_2 = {
        "id": "sec-2-cones",
        "paper_section": "Cones",
        "paper_section_number": "2",
        "title": "Cones",
        "intro_html": "<p>The paper introduces <em>positive cones</em> — additive "
                      "monoids with a non-negative scalar action and a complete norm. "
                      "Formalised as a Hierarchy Builder tower.</p>",
        "entries": [
            _entry(
                "e-2-1", "Def 2.1", "Definition", "2.1", "sec-2-cones",
                ["axiom-free"],
                ["precone", "PreCone.type", "isPrecone"],
                [_file("theories/cones/precone.v")],
                "<p>A <em>precone</em> is an additive commutative monoid with a "
                "non-negative real scalar action satisfying distributivity and "
                "bilinearity.</p>",
                prose="<p>The HB mixin packages the algebraic axioms exactly as the paper.</p>",
                snippets=[_snippet("theories/cones/precone.v", "Section Precone",
                    "HB.mixin Record isPrecone (R : realType) (P : Type) := {\n"
                    "  precone_zero  : P;\n"
                    "  precone_add   : P -> P -> P;\n"
                    "  precone_scale : {nonneg R} -> P -> P;\n"
                    "  precone_addA : associative precone_add;\n"
                    "  precone_addC : commutative precone_add;\n"
                    "}.")],
            ),
            _entry(
                "e-2-2", "Def 2.2", "Definition", "2.2", "sec-2-cones",
                ["axiom-free"],
                ["Cone.type", "isCone"],
                [_file("theories/cones/cone.v")],
                "<p>A <em>cone</em> is a precone with Selinger's partial order ≤, the "
                "supremum of every increasing norm-bounded ω-chain, and the norm "
                "acting as a continuous semi-norm.</p>",
                xrefs=[{"kind": "entry", "target": "e-2-1", "label": "Def 2.1"}],
            ),
            _entry(
                "e-2-cat", "Cat 2", "Category", "Cat-2", "sec-2-cones",
                ["axiom-free"],
                ["cones_hom", "cones_comp", "Cones"],
                [_file("theories/cones/cone_cat.v")],
                "<p>The category <code>Cones</code> has cones as objects and "
                "norm-≤ 1 continuous linear maps as morphisms.</p>",
            ),
            _entry(
                "e-2-8", "Lem 2.8 / 2.10", "Lemma", "2.8,2.10", "sec-2-cones",
                ["axiom-free"],
                ["invf_omega_continuous", "diff_omega_continuous"],
                [_file("theories/cones/basic_lemmas.v")],
                "<p>ω-continuity of inverse and of the difference operator on the unit ball.</p>",
            ),
            _entry(
                "e-2-notes", "Design note", "Note", None, "sec-2-cones",
                ["beyond-paper"],
                ["is_omega_continuous", "is_scott_continuous_unit"],
                [_file("theories/cones/cone.v")],
                "<p>Two flavours of ω-continuity: a linear-tailored unit-ball form, "
                "and a Scott form for non-linear stable maps in §7. Both equivalent on linear maps.</p>",
                notes=[{"kind": "info", "title": "Why two definitions",
                        "html": "<p>The §7 stable functions only see input chains in the ball; "
                                "their outputs can grow. We prove the equivalence in "
                                "<code>basic_lemmas.v</code>.</p>"}],
            ),
        ],
        "notes_html": "<p>The Rocq encoding follows the paper's definitional path almost verbatim.</p>",
    }

    section_3 = {
        "id": "sec-3-mcones",
        "paper_section": "Measurable cones",
        "paper_section_number": "3",
        "title": "Measurable cones (MCones)",
        "intro_html": "<p>Cones equipped with a parametrised family of measurable tests.</p>",
        "entries": [
            _entry(
                "e-3-arcat", "Cat. ARCAT", "Definition", "Ar", "sec-3-mcones",
                ["axiom-free"],
                ["MeasSubcat", "ar_obj", "ar_carrier"],
                [_file("theories/mcones/ar.v")],
                "<p>A small full subcategory of <code>MEAS</code> with a chosen "
                "point, terminal object, and binary products.</p>",
            ),
            _entry(
                "e-3-5", "Def 3.5", "Definition", "3.5", "sec-3-mcones",
                ["axiom-free"],
                ["MCone.type", "isMCone"],
                [_file("theories/mcones/mcone.v")],
                "<p>An <em>mcone</em> is a cone equipped with a family of measurable "
                "tests (continuous, ≤ 1, separating).</p>",
            ),
            _entry(
                "e-3-13", "Def 3.13", "Definition", "3.13", "sec-3-mcones",
                ["axiom-free"],
                ["mcones_hom", "MCones"],
                [_file("theories/mcones/mcone_cat.v")],
                "<p>An <em>mcones morphism</em> is a Cones-morphism preserving paths.</p>",
            ),
            _entry(
                "e-3-11", "Prop 3.11", "Proposition", "3.11", "sec-3-mcones",
                ["axiom-free"],
                ["mcone_norm_le_pairing_ub", "mcone_test_pairing_adherent"],
                [_file("theories/mcones/mcone_cat.v", section="Section Proposition311")],
                "<p>Dual norm separation: ‖x‖ ≤ sup_{t ∈ M} ⟨t,x⟩.</p>",
            ),
            _entry(
                "e-3-16", "Def 3.16", "Definition", "3.16", "sec-3-mcones",
                ["axiom-free", "regression-anchor"],
                ["fmeas", "FMeas"],
                [_file("theories/mcones/fmeas.v")],
                "<p>The <em>measure cone</em> <code>FMeas(X)</code> of finite measures on "
                "<code>X ∈ ARCAT</code>, with test <code>t ↦ ∫ t dµ</code>.</p>",
            ),
        ],
        "notes_html": "",
    }

    section_5 = {
        "id": "sec-5-smcc",
        "paper_section": "SMCC",
        "paper_section_number": "5",
        "title": "Internal hom, tensor, SMCC",
        "intro_html": "<p>ICones is a Symmetric Monoidal Closed Category.</p>",
        "entries": [
            _entry(
                "e-5-1", "Def 5.1", "Definition", "5.1", "sec-5-smcc",
                ["axiom-free"],
                ["linhom_car"],
                [_file("theories/homs/linhom.v")],
                "<p>The internal hom <code>C ⊸ D</code> as a full iconeType.</p>",
            ),
            _entry(
                "e-5-15", "Thm 5.15", "Theorem", "5.15", "sec-5-smcc",
                ["axiom-free", "regression-anchor"],
                ["ICones_SMCC", "ICones_smcc"],
                [_file("theories/homs/smcc.v")],
                "<p><code>(ICones, ⊗, 1)</code> is a Symmetric Monoidal Closed Category.</p>",
                snippets=[_snippet("theories/homs/smcc.v", None,
                    "Theorem ICones_smcc : SMCC ICones.\n"
                    "Proof. exact ICones_SMCC. Qed.")],
            ),
            _entry(
                "e-5-9", "Thm 5.9", "Theorem", "5.9", "sec-5-smcc",
                ["axiom-free"],
                ["limpl_preserves_limits"],
                [_file("theories/homs/limpl_continuous.v")],
                "<p><code>C ⊸ −</code> preserves products and equalisers, hence all limits.</p>",
            ),
            _entry(
                "e-5-12", "Thm 5.12", "Theorem", "5.12", "sec-5-smcc",
                ["axiom-free"],
                ["tensor_hom_iso"],
                [_file("theories/homs/tensor.v")],
                "<p>The adjunction iso <code>(B ⊗ C) ⊸ D ≅ B ⊸ (C ⊸ D)</code>.</p>",
            ),
            _entry(
                "e-5-cor20", "Cor 20 (Melliès)", "Beyond", None, "sec-5-smcc",
                ["beyond-paper"],
                ["EMComon_all"],
                [_file("theories/homs/em_cartesian.v")],
                "<p>Full cartesianness of <code>EM(!)</code> via Melliès' Corollary 20.</p>",
                xrefs=[{"kind": "beyond", "target": "b-cor20",
                        "label": "Beyond: Cor-20 retraction"}],
            ),
        ],
        "notes_html": "",
    }

    beyond = [
        {
            "id": "b-saft",
            "title": "Mechanisation of SAFT",
            "subtitle": "Special Adjoint Functor Theorem made concrete.",
            "paper_refs": ["§4.3", "§5", "§7", "§9"],
            "lemma_count": 24,
            "html": "<p>The paper applies Freyd's SAFT as a black box. We mechanise "
                    "the construction concretely — the left adjoint at <code>c</code> is "
                    "the wide intersection of subobjects of a power of the coseparator.</p>",
            "entries": [
                {"label": "Subobject classifier on ICones",
                 "rocq_idents": ["SubobjClassifier", "icones_subobject_classP"],
                 "rocq_files": [_file("theories/icones/representable.v")]},
                {"label": "Wide intersection + UMP",
                 "rocq_idents": ["wi_obj", "wi_med", "wi_med_proj"],
                 "rocq_files": [_file("theories/icones/representable.v")]},
            ],
            "snippets": [_snippet("theories/icones/representable.v", "Section WideIntersection",
                "Definition wi_med : icones_hom Ar Z wi_obj :=\n"
                "  icones_eq_med wi_u wi_v wi_tuple wi_tuple_equ.")],
            "references": [{"html": "Riehl, <em>Category Theory in Context</em>, Thm 4.6.10."}],
        },
        {
            "id": "b-cbv",
            "title": "CBV calculi and a direct-style PPL",
            "subtitle": "Moggi-CBV plus Saito–Affeldt QBS mirror.",
            "paper_refs": ["Beyond §9"],
            "lemma_count": 42,
            "html": "<p>Two surface calculi exercising the !-coalgebra structure: a "
                    "first-order Moggi-CBV (<code>cbv.v</code>) and a direct-style multi-var named "
                    "PPL (<code>ppl.v</code>) with examples like <code>ex_random_linear</code> and "
                    "<code>ex_geom_arr_mass_one</code> — all axiom-free.</p>",
            "entries": [
                {"label": "CBV value-fixpoint at function types",
                 "rocq_idents": ["Yfix_fun_T"],
                 "rocq_files": [_file("theories/programs/infra/em_fix.v")]},
                {"label": "Geometric example, mass 1",
                 "rocq_idents": ["ex_geom_arr_mass_one"],
                 "rocq_files": [_file("theories/programs/ppl.v")]},
            ],
            "snippets": [],
            "references": [],
        },
    ]

    gaps = [
        {
            "id": "gap-8", "title": "Analytic functions and ACONES",
            "paper_ref": "§ 8",
            "html": "<p>A separate analytic layer (radius-of-convergence, complex "
                    "analyticity, Taylor expansion of stable functions) is required. "
                    "Out of current scope.</p>",
        },
        {
            "id": "gap-9-em", "title": "Polish / standard-Borel full subcategory (post-9.7)",
            "paper_ref": "§ 9 (post-9.7)",
            "html": "<p>The full-subcategory theorem requires a Polish / standard-Borel "
                    "layer in mathcomp-analysis plus two folklore measure-theoretic lemmas "
                    "(regularity of finite Borel measures, image-measure determination). "
                    "Not yet in inventory.</p>",
        },
        {
            "id": "gap-10", "title": "Probabilistic coherence spaces embedding",
            "paper_ref": "§ 10",
            "html": "<p>Requires a separate PCS formalisation, which lives outside the "
                    "current development.</p>",
        },
    ]

    return {
        "preamble_html":
            "<p>This dashboard mirrors <code>AUDITOR.md</code> "
            "(<a href=\"https://github.com/" + GH + "/blob/main/AUDITOR.md\">source</a>). "
            "Use the search bar to jump to a paper number or a Rocq identifier; status "
            "badges show axiom-budget at a glance.</p>",
        "sections": [section_2, section_3, section_5],
        "beyond": beyond,
        "gaps": gaps,
        "verify_instructions_html":
            "<pre><code># 1. Clone and build (Rocq 9.1.1 + mathcomp-analysis 1.16).\n"
            "opam install --deps-only ./icones.opam\n"
            "make -j\n\n"
            "# 2. Run the axiom-budget check on the regression anchor.\n"
            "./verify.sh\n</code></pre>"
            "<p>The three classical-logic axioms inherited from mathcomp-analysis are "
            "the only ones that should appear: "
            "<code>propositional_extensionality</code>, "
            "<code>functional_extensionality_dep</code>, "
            "<code>constructive_indefinite_description</code>.</p>",
        "axiom_anchors": {
            "regression": "Icones.kernels.kernel_embedding.Skern_to_ICones_fully_faithful",
            "headlines": [
                "Icones.homs.smcc.ICones_smcc",
                "Icones.homs.seely.ICones_Seely",
                "Icones.homs.coalgebra.FMeas_coalgebra",
                "Icones.stable.scones_ccc.SCones_ccc",
                "Icones.programs.ppl.ex_geom_arr_mass_one",
            ],
        },
        "build_meta": {
            "commit": "deadbeefcafe1234567890abcdef0000000000",
            "built_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
            "auditor_lines": 2352,
            "repo": GH,
        },
    }


def make_ppl_document() -> dict:
    """Top-down PPL narrative: a few story sections + 'examples' beyond."""
    sec_cbv = {
        "id": "sec-cbv",
        "paper_section": "CBV core",
        "paper_section_number": "CBV",
        "title": "Call-by-value core",
        "intro_html": "<p>A Moggi-style call-by-value calculus on top of the "
                      "Eilenberg-Moore category of the <code>!</code> comonad.</p>",
        "entries": [
            _entry(
                "ppl-cbv-types", "CBV types", "Story", None, "sec-cbv",
                ["axiom-free"],
                ["cbv_type", "cbv_denot"],
                [_file("theories/programs/cbv.v")],
                "<p>Object types <code>tunit · tbase · tprod · tfun · tbool</code> "
                "with a single <em>denotation</em> functor into ICones.</p>",
            ),
            _entry(
                "ppl-cbv-fix", "Value fixpoint", "Story", None, "sec-cbv",
                ["axiom-free"],
                ["Yfix_fun_T", "linhom_lfp"],
                [_file("theories/programs/infra/em_fix.v")],
                "<p>The CBV value-fixpoint at function types — packaged via "
                "<code>adj_psi</code> of the <code>linhom_lfp</code>.</p>",
            ),
        ],
        "notes_html": "",
    }
    sec_recur = {
        "id": "sec-rec",
        "paper_section": "Recursion",
        "paper_section_number": "Rec",
        "title": "Productive partiality",
        "intro_html": "<p>The Phase-4 examples: bare divergence, geometric mass 1, "
                      "and the parameterised almost-loop.</p>",
        "entries": [
            _entry(
                "ppl-loop", "ex_loop", "Example", None, "sec-rec",
                ["axiom-free"],
                ["ex_loop"],
                [_file("theories/programs/examples/loop.v")],
                "<p>Bare divergence — every iterate has mass 0.</p>",
            ),
            _entry(
                "ppl-geom", "ex_geom", "Example", None, "sec-rec",
                ["axiom-free", "regression-anchor"],
                ["ex_geom", "ex_geom_arr_mass_one"],
                [_file("theories/programs/examples/geom.v")],
                "<p>Geometric — mass 1 in the limit.</p>",
                snippets=[_snippet("theories/programs/examples/geom.v", None,
                    "Lemma ex_geom_arr_mass_one : cone_mass ex_geom_arr = 1.\n"
                    "Proof. by apply: geom_mass_lim. Qed.")],
            ),
        ],
        "notes_html": "",
    }
    return {
        "preamble_html":
            "<p>Top-down narrative of the direct-style PPL.  Each section "
            "covers a piece of the surface calculus and its ICones denotation.</p>",
        "sections": [sec_cbv, sec_recur],
        "beyond": [
            {
                "id": "ppl-examples",
                "title": "Worked PPL programs",
                "subtitle": "Programs and their denotational masses.",
                "paper_refs": [],
                "lemma_count": 11,
                "html": "<p>Examples beyond the paper proper.</p>",
                "entries": [
                    {"label": "Random constant",
                     "rocq_idents": ["ex_random_constant"],
                     "rocq_files": [_file("theories/programs/ppl.v")]},
                    {"label": "Bayesian linear",
                     "rocq_idents": ["ex_bayes_linear"],
                     "rocq_files": [_file("theories/programs/ppl.v")]},
                ],
                "snippets": [],
                "references": [],
            },
        ],
        "gaps": [],
        "verify_instructions_html":
            "<p>Reuse the paper-tab verify pipeline; the PPL examples "
            "compile from the same <code>_CoqProject</code>.</p>",
        "axiom_anchors": {
            "regression": "Icones.programs.examples.geom.ex_geom_arr_mass_one",
            "headlines": ["Icones.programs.ppl.ex_random_constant"],
        },
        "build_meta": {
            "commit": "deadbeefcafe1234567890abcdef0000000000",
            "built_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
            "auditor_lines": 1421,
            "repo": GH,
        },
    }


def make_examples_document() -> dict:
    """Surface-program examples tab: PPL programs and headline lemmas."""
    sec_random = {
        "id": "sec-random",
        "paper_section": "Randomness",
        "paper_section_number": "Rand",
        "title": "Random and Bayesian programs",
        "intro_html": "<p>First-order surface examples that pull from "
                      "<code>bernoulli</code> / <code>uniform</code> and combine "
                      "the resulting random values through CBV terms.</p>",
        "entries": [
            _entry(
                "ex-random-constant", "ex_random_constant", "Example", None,
                "sec-random",
                ["axiom-free"],
                ["ex_random_constant"],
                [_file("theories/programs/ppl.v")],
                "<p>Sample a constant; the marginal is a Dirac.</p>",
            ),
            _entry(
                "ex-bayes-linear", "ex_bayes_linear", "Example", None,
                "sec-random",
                ["axiom-free"],
                ["ex_bayes_linear", "ex_bayes_linear_is_weighted"],
                [_file("theories/programs/ppl.v")],
                "<p>Bayesian linear regression; mass equals the weighted Lebesgue "
                "integral of the prior.</p>",
                snippets=[_snippet("theories/programs/ppl.v", None,
                    "Lemma ex_bayes_linear_is_weighted :\n"
                    "  ex_bayes_linear_denot = weighted_marginal.\n"
                    "Proof. by apply: Law3_marginal. Qed.")],
            ),
        ],
        "notes_html": "",
    }
    sec_partial = {
        "id": "sec-partial",
        "paper_section": "Partial",
        "paper_section_number": "Part",
        "title": "Productive partiality",
        "intro_html": "<p>Phase-4 worked programs: bare divergence, geometric, "
                      "and the parameterised almost-loop.</p>",
        "entries": [
            _entry(
                "ex-loop", "ex_loop", "Example", None, "sec-partial",
                ["axiom-free"],
                ["ex_loop", "ex_loop_denot_E"],
                [_file("theories/programs/examples/loop.v")],
                "<p>Bare divergence — every iterate has mass 0.</p>",
            ),
            _entry(
                "ex-geom", "ex_geom", "Example", None, "sec-partial",
                ["axiom-free", "regression-anchor"],
                ["ex_geom", "ex_geom_arr_mass_one"],
                [_file("theories/programs/examples/geom.v")],
                "<p>Geometric — mass 1 in the limit.</p>",
                snippets=[_snippet("theories/programs/examples/geom.v", None,
                    "Lemma ex_geom_arr_mass_one : cone_mass ex_geom_arr = 1.\n"
                    "Proof. by apply: geom_mass_lim. Qed.")],
            ),
            _entry(
                "ex-even-odd-pair", "ex_even_odd_pair", "Example", None,
                "sec-partial",
                ["axiom-free"],
                ["ex_even_odd_pair"],
                [_file("theories/programs/examples/pair.v")],
                "<p>Two mutually recursive booleans, paired — the cascade test.</p>",
            ),
        ],
        "notes_html": "",
    }
    return {
        "preamble_html":
            "<p>Surface programs and their CBV / CBN headline lemmas. "
            "Each section groups examples by what feature of the PPL they "
            "exercise.</p>",
        "sections": [sec_random, sec_partial],
        "beyond": [
            {
                "id": "ex-beyond-cascade",
                "title": "Boolean cascade gallery",
                "subtitle": "ne_if / case_em walkthroughs.",
                "paper_refs": [],
                "lemma_count": 7,
                "html": "<p>Programs that thread <code>ne_if</code> through a "
                        "nested cascade and the EM-Kleisli <code>case_em</code>.</p>",
                "entries": [
                    {"label": "Bernoulli cascade",
                     "rocq_idents": ["ex_bernoulli_cascade"],
                     "rocq_files": [_file("theories/programs/ppl.v")]},
                ],
                "snippets": [],
                "references": [],
            },
        ],
        "gaps": [],
        "verify_instructions_html":
            "<p>Reuse the paper-tab verify pipeline; the examples compile "
            "from the same <code>_CoqProject</code>.</p>",
        "axiom_anchors": {
            "regression": "Icones.programs.examples.geom.ex_geom_arr_mass_one",
            "headlines": ["Icones.programs.ppl.ex_random_constant"],
        },
        "build_meta": {
            "commit": "deadbeefcafe1234567890abcdef0000000000",
            "built_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
            "auditor_lines": 612,
            "repo": GH,
        },
    }


def make_three_tab_document() -> dict:
    """Combined triple-tab dashboard payload (Paper + PPL + Examples)."""
    paper = make_paper_document()
    ppl = make_ppl_document()
    examples = make_examples_document()
    return {
        "paper": paper,
        "ppl": ppl,
        "examples": examples,
        "build_meta": {
            "commit": "deadbeefcafe1234567890abcdef0000000000",
            "built_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
            "auditor_lines": (
                paper["build_meta"]["auditor_lines"]
                + ppl["build_meta"]["auditor_lines"]
                + examples["build_meta"]["auditor_lines"]
            ),
            "repo": GH,
        },
    }


# Back-compat aliases.
make_two_tab_document = make_three_tab_document
make_document = make_paper_document


def main(argv: list[str] | None = None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--single", action="store_true",
                    help="emit a single-tab Document (paper only) instead "
                         "of the triple-tab payload.")
    args = ap.parse_args(argv)
    payload = make_paper_document() if args.single else make_three_tab_document()
    json.dump(payload, sys.stdout, indent=2, ensure_ascii=False)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
