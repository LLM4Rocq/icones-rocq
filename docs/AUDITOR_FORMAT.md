# Auditor MD format — the parser's contract

This document describes the structural conventions that
[`tools/build_auditor.py`](../tools/build_auditor.py) expects in its
**three** input files — `docs/PAPER.md`, `docs/PPL.md`, and
`docs/EXAMPLES.md` — and the JSON schema it emits at
`site/auditor/data.json`.

## Three-tab model (since 2026-06)

The dashboard renders three **tabs**:

- **Paper**    — sourced from `docs/PAPER.md`, definition-by-definition
  map from the paper's §§ 2 – 9 into Rocq.
- **PPL**      — sourced from `docs/PPL.md`, top-down narrative of the
  direct-style PPL on top of the !-coalgebra structure.
- **Examples** — sourced from `docs/EXAMPLES.md`, worked surface
  programs and their CBV / CBN headline lemmas.

Each MD file uses the *same* per-document format described below (H2
chapters, overview tables, H3 detail blocks, snippets, blockquotes).
The three-tab orchestrator
([`parse_three_tabs`](../tools/auditor/parser.py)) wraps the per-file
parser; warnings are tagged with `[paper]` / `[ppl]` / `[examples]` so
the CLI's `--strict` mode can attribute failures.

The output tree is split under three subdirectories with shared static
assets:

```
site/auditor/index.html              triple-tab landing
site/auditor/data.json               combined JSON ({paper, ppl, examples, build_meta})
site/auditor/static/                 shared CSS/JS/Pygments
site/auditor/paper/index.html        Paper-tab landing
site/auditor/paper/sections/<id>.html
site/auditor/paper/entries/<id>.html
site/auditor/paper/beyond/<id>.html
site/auditor/paper/gaps.html
site/auditor/paper/data.json         Paper-only export
site/auditor/ppl/...                 mirror for the PPL tab
site/auditor/examples/...            mirror for the Examples tab
```

Every per-tab page carries a tab-nav row in the header
(`Paper` / `PPL` / `Examples` chips); the active tab gets
`aria-current="page"`. The root landing renders all three chips
unhighlighted plus a triple-tab summary grid.

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

   Snippets are **live**: their Rocq code is *resolved from the sources at
   build time*, not taken from the Markdown.  See
   [Live snippets](#live-snippets-resolved-not-pasted) below — that
   section is the one to read before writing a new entry.

7. **Blockquotes** inside an H3 become `NoteBlock` entries on the
   entry's `detail.notes`.  Above any H3, blockquotes attach to the
   section's `notes_html`.

8. **Cross-references** — the text `Beyond the paper` appearing in any
   row's statement or Rocq cell produces a `CrossRef` of kind `beyond`.

## Live snippets (resolved, not pasted)

A card's Rocq code is **resolved from `theories/**/*.v` at build time** by
[`tools/auditor/snippets.py`](../tools/auditor/snippets.py).  Hand-pasted
code is a *legacy fallback*: it rots the moment a lemma is renamed or
generalised, and nothing on the page tells the reader that it has.

### What the build does with a fenced block

The resolver splits every ``` ```coq ``` block into **declaration units**
and editorial material, then rewrites each unit from the sources:

1. A unit opens at a declaration keyword — `Definition`, `Lemma`,
   `Theorem`, `Corollary`, `Proposition`, `Fact`, `Remark`, `Example`,
   `Fixpoint`, `CoFixpoint`, `Inductive`, `CoInductive`, `Variant`,
   `Record`, `Structure`, `Class`, `Instance`, `Canonical`, `Coercion`,
   `Notation`, `Axiom`, `Parameter`, `Variable`, `Hypothesis`, and the
   `HB.mixin Record` / `HB.structure Definition` /
   `HB.instance Definition` / `HB.factory Record` / `HB.builders Context`
   forms — optionally prefixed by `Local` / `Global` / `Program` and by
   `#[…]` attribute lines (which are part of the unit).
2. The unit's **identifier** is looked up in the ``.v`` sources: in the
   file named by the provenance comment first, then — if that file does
   not have it — globally, provided the name is unique across
   `theories/`.  `Notation "…"` units are keyed by their notation string;
   a lone `| Cn …` line is keyed as a **constructor** of the inductive
   that declares it; `HB.instance Definition _` units (which have no
   name) are keyed by the `X.Build` they apply.
3. The **statement** is extracted verbatim from the source: from the
   keyword (with its attribute lines) to the first statement-terminating
   `.` at bracket/comment/string depth 0 — the `.` before `Proof.` for a
   proof-carrying object, the `.` that closes `:= …` for a definition,
   record or inductive (whose body *is* the statement).  A term body
   longer than 40 lines is elided at its `:=`.
4. Everything that is **not** a declaration — blank lines, your
   `(* … *)` glosses, `Section` / `End` markers — is copied through
   verbatim, so the editorial shape of a block survives.

The rendered card therefore always shows what is in `theories/` today,
and its header carries the source line range plus a GitHub deep link.

### Writing a new entry

Quote the declaration you are documenting; anything that is stale or
elided in your paste is replaced by the source text at build time:

````markdown
```coq
(* theories/cones/cone.v *)
Lemma cone_norm0 (P : coneType R) : cone_norm (precone_zero : P) = 0.
```
````

You do not have to keep the body in sync — only the **identifier** and
the provenance file matter.  A one-line stub naming the declaration is
enough; the build renders the real statement.

The rewrite is a fixpoint: pasting a *rendered* snippet back into the
Markdown resolves to itself and clears that block's `stale` warning.

### The splice guard: a replacement must not lose content

Finding a declaration proves *where* it lives; it does not prove that its
extracted statement is a fair stand-in for what you wrote.  Two shapes
break that assumption, and both silently destroy curated content on the
deployed page:

- **proof mode** — `Fixpoint eD_cbv … : EXi G t.` followed by
  `Proof. refine (…)` puts the body in the proof script, so the statement
  extent (correctly) ends at the signature.  Splicing would collapse a
  48-line pasted interpreter to its two-line type.
- **curated excerpt** — the paste quotes a handful of constructors of a
  178-line `Inductive`, or a few fields of a large `Record`.  Those
  keywords are in `_BODY_IS_STATEMENT`, so their body is never elided and
  the splice would replace the excerpt with the full dump.

So the extracted statement only replaces the paste when it is a plausible
stand-in for it, measured in **code lines** (blank and comment-only lines
excluded):

| condition | outcome |
|---|---|
| identical modulo whitespace/comments | splice (a no-op) |
| source has no `:=`, paste does, source is shorter | **keep the paste** |
| source ≥ `MIN_SHRINK_LINES` shorter *and* < `SHRINK_RATIO`× the paste | **keep the paste** |
| source ≥ `MIN_GROWTH_LINES` longer *and* > `GROWTH_RATIO`× the paste | **keep the paste** |
| otherwise | splice |

The thresholds live at the top of
[`snippets.py`](../tools/auditor/snippets.py).  A held-back unit is still
*resolved* — the card keeps its source link and anchor line — but renders
the paste verbatim and is reported under **paste-kept**.  A splice may
only ever make a card more accurate, never less complete; when the two
readings conflict, the human-curated one wins and the report names it.

### What the build reports

`tools/build_auditor.py` prints a one-line summary and then a maintenance
report on stderr:

```
[build_auditor] live snippets: blocks=214 (full=213 partial=0 none=1) \
    decls=518 resolved=518 (100%) fallback=0 stale=68 paste-kept=7
```

- **fallback** — a unit whose identifier was *not* found (or was
  ambiguous across files).  The card renders the pasted text and the
  identifier is listed: either the name is wrong, or the declaration
  moved.  This is the list to drive to zero.
- **paste-kept** — the declaration *was* found, but the splice guard
  above refused the source statement as a replacement.  The card renders
  the paste unchanged.  The report names the file, line and reason; under
  GitHub Actions each one is also emitted as a `::warning::` annotation,
  so the signal shows on the run summary of a green build.
- **stale** — the paste materially disagreed (modulo whitespace and
  comments) with the source.  The card shows the *source*; the report
  names the file and line, and the line-count delta.  Stale entries are
  informational — they are the docs' own drift, not a build failure.
- **provenance** — the `(* theories/… *)` comment names a file that does
  not hold the block's declarations.
- **opaque** — no declaration recognised at all (a bare term or a proof
  fragment).  Nothing to resolve; the block renders as pasted and is
  marked `pasted` on the page.

Standalone check (no rendering; same numbers as the build):

```
python -m tools.auditor.snippets                 # exit 1 on any fallback
python -m tools.auditor.snippets --strict        # also fail on stale pastes
python tools/build_auditor.py … --check-snippets # full report + exit code
```

### Degradation

Resolution is a pure text scan of `theories/**/*.v`, so it works in CI
without compiling anything.  When a sibling `.glob` *is* present (a local
build, or a CI job that downloaded the `theories-glob` artefact), its
`def` byte offsets are used as an overlay to catch layouts the scan
cannot key (e.g. a name on the line after its keyword).  When `theories/`
is absent altogether, every block renders exactly as pasted — the
pre-live-snippets behaviour.

A `.glob` is an **untrusted, independently-produced input**: it is built
by a different workflow from a possibly different commit, or rewritten
under a concurrent `make`.  So offsets past the end of the `.v` are
skipped (never clamped — clamping would key an unrelated declaration to
the name), the offset→line map is bounded by the real line count, and any
failure at all degrades to the regex index.  Nothing a `.glob` can say
may break the docs build.

## Dependency graph (real, from `.glob`)

The graph page (`site/auditor/graph.html` + `graph.json`) is the site's
navigation spine. Its nodes are entries, compound-nested entry → section →
tab; its edges come in exactly two kinds, and the distinction is the whole
point:

| kind | source | meaning | drawn |
|------|--------|---------|-------|
| `depends`  | `theories/**/*.glob` | a **real Coq proof-level dependency**: an object this entry documents *uses* an object the target documents | solid |
| `mentions` | entry statement / prose / snippet text | a **doc co-reference**: the text names an identifier the target documents | dashed |

When the same ordered pair is both, `depends` wins. The same edge data
also drives every card's **Uses / Used by** panel, so an entry page links
straight to what its proofs rest on and to what rests on it, cross-tab —
each relation ref carrying `via: "glob" | "doc"` and rendered solid vs
dashed to match the graph.

### Where the `.glob` files come from

`coqc` writes one `.glob` next to each compiled `.v`. They are
`.gitignore`d, so a fresh checkout has none:

- **Locally** — run `make` once. Without it the build still works and
  prints a NOTICE, but the graph shows doc co-references only.
- **In CI** — `build.yml` is the one job that compiles the formalisation;
  it tars `theories/**/*.glob` into the `theories-glob` artefact.
  `blueprint.yml`'s `build-auditor` downloads that artefact instead of
  paying for a second ~15 min Rocq build on the deploy critical path.

  That download is **pinned to the commit being built**
  (`commit: ${{ github.event.pull_request.head.sha || github.sha }}` — the
  PR *head* SHA, since `github.sha` on a `pull_request` event is an
  ephemeral merge commit no artefact exists for). This is not a nicety:
  the `.glob` byte offsets drive live-snippet extraction as well as the
  graph, so a `.glob` from another revision is a *wrong* input, not merely
  an old one, and an unpinned download makes the build unreproducible.
  `build.yml` (~15 min) is slower than `build-auditor` (~5 min), so on a
  fresh push the pinned artefact does not exist yet; a **separately named**
  `FALLBACK` step then fetches the last successful `main` build and says so
  in a `::warning::`. Reading the step names tells you which revision the
  build was graded against.

### The strict guard

A graph whose edges are *all* doc co-references looks like a dependency
graph and is not one. So when `.glob` data was expected — a theories root
was supplied and the docs reference `.v` files — but the build produced
**zero** `depends` edges, the build **fails loudly** with
`render.GlobDependencyError` instead of publishing the degraded graph.

Strictness is decided by `render.require_glob_deps_default()`:

| `AUDITOR_REQUIRE_GLOB_DEPS` | `CI` set | guard |
|-----------------------------|----------|-------|
| unset | no  | off (a dev checkout legitimately has no `.glob`) |
| unset | yes | **on** |
| `0` / `false` / `no` / `off` | either | off (documented escape hatch) |
| anything else | either | on |

`build_auditor.py` catches `GlobDependencyError` and exits **2** after the
diagnosis, so a rejected build ends in a readable message rather than a
traceback.

#### …and why CI runs it *after* the build, not during it

`combine-and-deploy` is the only job that publishes `/blueprint/` and
`/docs/` too. Gating it on `build-auditor`'s success therefore made the
*entire* site publish hostage to another workflow's artefact: a red
`build.yml`, an expired `theories-glob`, or `actions: read` denied on a
fork PR unpublished the blueprint and coqdoc as collateral.

So `blueprint.yml` inverts the order:

1. build with `AUDITOR_REQUIRE_GLOB_DEPS: '0'` — a degraded graph ships
   behind the explicit "Degraded" banner `templates/graph.html` renders,
   which states plainly that every edge is a doc co-reference;
2. upload the artefact;
3. run `python -m tools.auditor.render --check-graph site/auditor/graph.json`
   (exit `0` ok / `1` degraded / `2` unreadable) as its own step, which
   turns the **job** — and the workflow badge — red;
4. `combine-and-deploy` runs on `always()` and re-checks the assembled
   site itself, falling back to the last successful `auditor-site`
   artefact and hard-failing only if there is no dashboard to deploy at
   all.

The signal stays loud and honest; a degraded graph costs a red badge, not
the site. Locally the guard still raises *during* `render()` — fail fast,
write nothing — which is the right default for a developer.

`graph.json` carries a `meta` block with the provenance behind those
numbers — `glob_expected`, `n_glob_files`/`n_vfiles`, `n_glob_objects`,
`n_depends`, `n_mentions`, `n_cross_tab`, `edges_by_tab` — which the graph
page prints under its legend, including an explicit "Degraded" line when
no `.glob` data was available.

Individual unreadable, empty or half-written `.glob` files (a concurrent
`make` rewrites them in place) are skipped per-file and counted as missing;
only a *total* absence of real edges trips the guard.

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

Combined `ThreeTabDocument` shape (written to `site/auditor/data.json`):

```jsonc
{
  "paper":      { ...Document... },
  "ppl":        { ...Document... },
  "examples":   { ...Document... },
  "build_meta": {"commit": "...", "built_at": "...", "auditor_lines": 4385}
}
```

For backward compatibility the parser also exposes a transitional alias
`TwoTabDocument = ThreeTabDocument` (with `two_tab_to_dict` aliased to
`three_tab_to_dict`); new code should prefer the three-tab names.

A `CoqSnippet` additionally reports its
[live-snippet](#live-snippets-resolved-not-pasted) resolution; all of the
new keys default to the legacy "pasted" state, so consumers written
against the older shape keep working:

```jsonc
{
  "source_file":      "theories/cones/precone.v",
  "source_section":   null,
  "highlighted_html": "<div class=\"highlight coq\">…</div>",
  "line_count":       34,
  "resolved":         true,       // spliced from the sources
  "stale":            true,       // the Markdown paste disagreed
  "source_line":      46,         // 1-based; 0 when unresolved
  "source_end_line":  78,         // 0 unless the text spans the range
  "github_url":       "https://github.com/…/precone.v#L46",
  "coqdoc_url":       "docs/Icones.cones.precone.html",
  "decls":            ["isPrecone", "Precone"]
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
    --paper    docs/PAPER.md \\
    --ppl      docs/PPL.md \\
    --examples docs/EXAMPLES.md \\
    --out      site/auditor/ \\
    --coqproject _CoqProject \\
    --github-repo $GITHUB_REPOSITORY \\
    --commit $GITHUB_SHA \\
    [--strict] \\
    [--check-snippets] [--snippet-report-limit N] \\
    [--template-dir tools/auditor/templates]
```

All three of `--paper`, `--ppl`, and `--examples` are required.

`--strict` mode treats parser warnings as errors and exits with status 1
if any of these conditions trigger:

- a referenced `theories/foo.v` file is not on disk,
- two entries normalise to the same slug,
- an H3 in a paper chapter has no matching overview-table row,
- a table row has a cell count outside `{2, 3}`.

`--check-snippets` prints the *complete*
[live-snippet](#live-snippets-resolved-not-pasted) report (rather than the
first `--snippet-report-limit` lines of each list, default 12) and exits
1 if any snippet declaration could not be resolved from `theories/`.
Live-snippet findings never trip `--strict`: a stale paste is a docs
maintenance signal, not a parser error.

The directory holding `_CoqProject` is the project root, so
`theories/` is resolved relative to it — pointing `--coqproject` at
another checkout resolves snippets against *that* tree.

## Output tree

```
site/auditor/
├── index.html                       triple-tab landing
├── data.json                        combined {paper, ppl, examples, build_meta}
├── graph.html                       interactive dependency graph
├── graph.json                       {nodes, edges, meta} — Cytoscape.js shape
├── static/
│   ├── style.css
│   ├── print.css
│   ├── app.js
│   ├── graph.css
│   ├── graph.js
│   └── pygments.css
├── paper/
│   ├── index.html                   Paper-tab landing
│   ├── data.json                    paper-only export
│   ├── sections/sec-2.html
│   ├── entries/def-2-1.html
│   ├── beyond/<id>.html
│   └── gaps.html
├── ppl/
│   ├── index.html                   PPL-tab landing
│   ├── data.json                    ppl-only export
│   ├── sections/<id>.html
│   ├── entries/<id>.html
│   ├── beyond/<id>.html
│   └── gaps.html
└── examples/
    ├── index.html                   Examples-tab landing
    ├── data.json                    examples-only export
    ├── sections/<id>.html
    ├── entries/<id>.html
    ├── beyond/<id>.html
    └── gaps.html
```

### Examples MD contract

The `docs/EXAMPLES.md` content agent should mirror the same H2 / table /
H3 structure as `docs/PAPER.md`. Practical conventions for that file:

- H2 `Paper § N — Title` is reused as the section heading even though
  these are PPL programs (not paper §§); the slug is still `sec-<N>`.
- Each entry's first column is a paper-style label (`Def 1.1`,
  `Thm 2.2`, …) so the existing slug machinery applies.
- Each Rocq cell references at least one `theories/programs/...` file.
- The `Beyond the paper` chapter holds programs that are not in the
  paper proper (e.g. boolean cascade gallery, infinite mixtures).
- The `What is not formalised` chapter is allowed to be empty (no
  declared gaps).
