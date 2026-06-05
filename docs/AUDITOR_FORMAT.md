# Auditor MD format — the parser's contract

This document describes the structural conventions that
[`tools/build_auditor.py`](../tools/build_auditor.py) expects in its
**two** input files — `docs/PAPER.md` and `docs/PPL.md` — and the JSON
schema it emits at `site/auditor/data.json`.

## Two-tab model (since 2026-06)

The dashboard renders two **tabs**:

- **Paper** — sourced from `docs/PAPER.md`, definition-by-definition map
  from the paper's §§ 2 – 9 into Rocq.
- **PPL**   — sourced from `docs/PPL.md`, top-down narrative of the
  direct-style PPL on top of the !-coalgebra structure.

Each MD file uses the *same* per-document format described below (H2
chapters, overview tables, H3 detail blocks, snippets, blockquotes).
The two-tab orchestrator
([`parse_two_tabs`](../tools/auditor/parser.py)) wraps the per-file
parser; warnings are tagged with `[paper]` / `[ppl]` so the CLI's
`--strict` mode can attribute failures.

The output tree is split under two subdirectories with shared static
assets:

```
site/auditor/index.html              dual-tab landing
site/auditor/data.json               combined JSON ({paper, ppl, build_meta})
site/auditor/static/                 shared CSS/JS/Pygments
site/auditor/paper/index.html        Paper-tab landing
site/auditor/paper/sections/<id>.html
site/auditor/paper/entries/<id>.html
site/auditor/paper/beyond/<id>.html
site/auditor/paper/gaps.html
site/auditor/paper/data.json         Paper-only export
site/auditor/ppl/...                 mirror of the above for the PPL tab
```

Every per-tab page carries a tab-nav row in the header
(`Paper`/`PPL` chips); the active tab gets `aria-current="page"`.
The root landing renders both chips unhighlighted plus a dual-tab
summary grid.

## Markdown structure

1. **H1** — one document title at the top (parsed as the preamble heading).

2. **Preamble** — everything between the H1 and the first H2 becomes the
   document's `preamble_html`.

3. **H2 chapters** — each H2 is classified by its title:

   | Pattern (regex)                                | Kind        |
   |------------------------------------------------|-------------|
   | `^Paper § (?P<num>[0-9.]+) — (?P<title>...)$`  | `paper`     |
   | `^Beyond the paper\b`                          | `beyond`    |
   | `^What is (\*\*)?not(\*\*)? formalised`        | `gap`       |
   | `^How to verify\b`                             | `verify`    |
   | anything else                                  | `other`     |

   The `Paper § N — Title` form supplies the section number and title.

4. **Overview table** (in a paper / beyond chapter) — a Markdown table
   whose first column is the *paper label* (`Def 2.1`, `Lem 2.8 / 2.10`,
   `Cat 2`, `LL `!``, …).  Three- and two-column tables are both
   accepted: 3-col is `Paper | English statement | Rocq`, 2-col is
   `Construction | Rocq` (used inside the *Beyond the paper* chapter).

   Cell contents are parsed as Markdown.  Identifiers are extracted from
   backticked spans, file paths from `theories/.../*.v` regex matches,
   and the section qualifier from `(Section X)`.

5. **H3 detail blocks** — one optional detail block per overview-table
   row.  The H3 heading is `### <paper label> (`name1`, `name2`, …)`.

   The parser matches a row to its H3 detail block by normalised slug
   (`Def 2.1` → `def-2-1`).  Two fuzzy fallbacks resolve real
   irregularities in the document:

   - **prefix fuzzy match** — `Def 4.1` row matches an `### Def 4.1 / 4.3`
     H3 because one slug is a prefix of the other.
   - **identifier fuzzy match** — `LL `!`` row matches an
     `### Linear exponential `!` (`Bang`, `nl`, ...)` H3 because they
     share the identifier `Bang` (and others).

6. **Coq snippets** — fenced ``` ```coq …``` ``` blocks inside an H3
   detail block.  The first line of the block should be a provenance
   comment `(* theories/foo/bar.v *)` (or with a `Section X` qualifier
   `(* theories/foo/bar.v — Section X *)`); both are extracted.

7. **Blockquotes** inside an H3 become `NoteBlock` entries on the
   entry's `detail.notes`.  Above any H3, blockquotes attach to the
   section's `notes_html`.

8. **Cross-references** — the text `Beyond the paper` appearing in any
   row's statement or Rocq cell produces a `CrossRef` of kind `beyond`.

## JSON schema (the contract with the UI agent)

See [`tools/auditor/schema.py`](../tools/auditor/schema.py) for the
dataclasses.

Per-tab `Document` shape (one of these per tab; written to
`site/auditor/<tab>/data.json`):

```jsonc
{
  "preamble_html": "<p>...</p>",
  "sections":       [Section, ...],
  "beyond":         [BeyondContrib, ...],
  "gaps":           [GapEntry, ...],
  "verify_instructions_html": "<p>...</p>",
  "axiom_anchors":  {"regression": "Thm 6.5", "headlines": ["thm-6-5", ...]},
  "build_meta":     {"commit": "...", "built_at": "...", "auditor_lines": 2352}
}
```

Combined `TwoTabDocument` shape (written to `site/auditor/data.json`):

```jsonc
{
  "paper":      { ...Document... },
  "ppl":        { ...Document... },
  "build_meta": {"commit": "...", "built_at": "...", "auditor_lines": 3773}
}
```

Per-entry status flags are computed by the classifier
([`tools/auditor/classifier.py`](../tools/auditor/classifier.py)):

- `axiom-free`         — default for paper-§ entries
- `beyond-paper`       — default for Beyond entries
- `gap`                — default for gap entries
- `regression-anchor`  — currently just `Thm 6.5`
- `discharged-deferred` — text contains `previously-deferred` or
  `deferred ... discharged`

## Per-template context dicts (M2/M4 contract)

The render driver
([`tools/auditor/render.py`](../tools/auditor/render.py))
calls each template with these keyword arguments:

| Template          | Required keys                                            |
|-------------------|----------------------------------------------------------|
| `index.html`      | `document`, `sections`, `beyond`, `gaps`, `axiom_anchors`, `build_meta`, `title`, `body` |
| `section.html`    | `document`, `section`, `entries`, `build_meta`, `title`, `body` |
| `entry.html`      | `document`, `entry`, `section` (or `None`), `contrib` (or absent), `build_meta`, `title`, `body` |
| `beyond.html`     | `document`, `contrib`, `entries`, `build_meta`, `title`, `body` |
| `gap.html`        | `document`, `gap`, `build_meta`, `title`, `body` |

The keys `title` and `body` are pre-rendered fallbacks that the
placeholder template uses; the real UI templates may ignore them.

When a template is missing, the renderer falls back to
`__placeholder.html` (bundled with the parser); both loaders are stacked
in a `ChoiceLoader` so the UI agent's `templates/` directory takes
priority.

## CLI

```
python tools/build_auditor.py \\
    --paper docs/PAPER.md \\
    --ppl   docs/PPL.md \\
    --out   site/auditor/ \\
    --coqproject _CoqProject \\
    --github-repo $GITHUB_REPOSITORY \\
    --commit $GITHUB_SHA \\
    [--strict] \\
    [--template-dir tools/auditor/templates]
```

`--strict` mode treats parser warnings as errors and exits with status 1
if any of these conditions trigger:

- a referenced `theories/foo.v` file is not on disk,
- two entries normalise to the same slug,
- an H3 in a paper chapter has no matching overview-table row,
- a table row has a cell count outside `{2, 3}`.

## Output tree

```
site/auditor/
├── index.html                       dual-tab landing
├── data.json                        combined {paper, ppl, build_meta}
├── static/
│   ├── style.css
│   ├── print.css
│   ├── app.js
│   └── pygments.css
├── paper/
│   ├── index.html                   Paper-tab landing
│   ├── data.json                    paper-only export
│   ├── sections/sec-2.html
│   ├── entries/def-2-1.html
│   ├── beyond/<id>.html
│   └── gaps.html
└── ppl/
    ├── index.html                   PPL-tab landing
    ├── data.json                    ppl-only export
    ├── sections/<id>.html
    ├── entries/<id>.html
    ├── beyond/<id>.html
    └── gaps.html
```
