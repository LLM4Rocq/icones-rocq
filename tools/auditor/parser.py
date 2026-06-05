"""Three-stage parser for ``AUDITOR.md``.

Stage 1 — lex
    Use ``markdown-it-py`` to split the input into a token stream of
    H1/H2/H3 headings, table blocks, fenced ``coq`` blocks (with a
    provenance comment ``(* theories/path.v *)``), prose, blockquotes.

Stage 2 — group
    Walk the token stream and build hierarchy: H2 sections, optional
    intro / table / detail sub-blocks per H3.  Match overview-table rows
    to H3 detail blocks by normalised label.

Stage 3 — normalise + emit
    Extract structured fields, classify, serialise to a
    :class:`tools.auditor.schema.Document`.
"""

from __future__ import annotations

import html as html_mod
import re
import unicodedata
from dataclasses import dataclass, field
from pathlib import Path

from markdown_it import MarkdownIt
from markdown_it.token import Token
from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import get_lexer_by_name as _get_lexer_by_name

from .classifier import DEFAULT_REGRESSION_ANCHORS, classify
from .coqdoc import CoqdocResolver
from .schema import (
    AxiomAnchors,
    BeyondContrib,
    BuildMeta,
    CoqSnippet,
    CrossRef,
    Document,
    Entry,
    EntryDetail,
    GapEntry,
    NoteBlock,
    RocqFile,
    Section,
)


# -- regexes used across the three stages -----------------------------------

# A H2 such as "Paper § 2 — Cones" / "Paper § 9 — Linear exponential, …".
_H2_PAPER_RE = re.compile(
    r"^Paper\s+§\s*(?P<num>[0-9.]+)\s*[—–-]\s*(?P<title>.+)$",
    re.IGNORECASE,
)
_H2_BEYOND_RE = re.compile(r"^Beyond\s+the\s+paper\b", re.IGNORECASE)
_H2_GAP_RE = re.compile(r"^What\s+is\s+(\*\*)?not(\*\*)?\s+formalised", re.IGNORECASE)
_H2_VERIFY_RE = re.compile(r"^How\s+to\s+verify\b", re.IGNORECASE)

# Paper-label rows in the leftmost overview-table cell:
#   "Def 2.1" / "Lem 2.8 / 2.10" / "Lem 7.20–7.25" / "Fubini (§4)" / "Cat 2"
#   / "Sect 9.2" / "§ 8" / "Thm 5.13" / "(also)" / "Rem 5.1" / "LL `!`"
_LABEL_KIND_RE = re.compile(
    r"^(?P<kind>Def|Thm|Lem|Prop|Cor|Cat|Fubini|Rem|Sect|§)\b\s*(?P<num>[0-9A-Za-z.–—/\s]*)",
    re.IGNORECASE,
)

# Backticked identifier candidates and theories/foo/bar.v paths.
_BACKTICK_RE = re.compile(r"`([^`]+)`")
_VFILE_RE = re.compile(r"theories/[A-Za-z0-9_/]+\.v")
_SECTION_QUAL_RE = re.compile(r"\(Section\s+([A-Za-z0-9_]+)\)")


# -- normalised label -------------------------------------------------------


_MAX_SLUG_LEN = 80


def slugify_label(label: str, max_len: int = _MAX_SLUG_LEN) -> str:
    """Normalise a paper label to a stable slug.

    ``"Def 2.1"`` -> ``"def-2-1"``;
    ``"Lem 2.8 / 2.10"`` -> ``"lem-2-8-2-10"``;
    ``"Lem 7.20–7.25"`` -> ``"lem-7-20-7-25"``;
    ``"§ 8"`` -> ``"sec-8"``;
    ``"Fubini (§4)"`` -> ``"fubini-4"``.

    Long English first-column titles in the "Beyond the paper" tables are
    truncated to ``max_len`` characters (default 80) — the resulting slug
    is still stable as long as the prefix is unique.
    """
    text = unicodedata.normalize("NFKC", label)
    text = text.replace("§", "sec-")
    text = text.casefold()
    # Replace common separators with single hyphens.
    text = re.sub(r"[\s.–—/_]+", "-", text)
    text = re.sub(r"[^a-z0-9-]+", "", text)
    text = re.sub(r"-+", "-", text).strip("-")
    if not text:
        return "item"
    if len(text) > max_len:
        text = text[:max_len].rstrip("-")
    return text


# -- stage 1: lex -----------------------------------------------------------


def lex(source: str) -> list[Token]:
    """Run ``markdown-it-py`` with the GFM-table plugin and return tokens.

    The default ``commonmark`` profile already supports tables and fenced
    code blocks; we only need to enable strikethrough / autolink-ish
    extensions if the document uses them (it does not).
    """
    md = MarkdownIt("commonmark", {"html": True}).enable("table").enable("strikethrough")
    return md.parse(source)


# -- stage 2: group ---------------------------------------------------------


@dataclass
class _TableRow:
    """One row of an overview table — list of raw cell-markdown strings."""

    cells: list[str]


@dataclass
class _RawTable:
    """An overview-style markdown table extracted from the token stream."""

    header: list[str]
    rows: list[_TableRow] = field(default_factory=list)


@dataclass
class _RawSnippet:
    """A fenced ``coq`` block extracted from the token stream.

    The provenance comment ``(* theories/path.v *)`` and any ``Section X``
    qualifier are extracted; the rest is stored verbatim for pygments
    highlighting.
    """

    raw: str
    source_file: str | None
    source_section: str | None


@dataclass
class _H3Block:
    """A H3 detail block (e.g. "### Def 2.1 (`isPrecone` / `Precone`)")."""

    heading: str
    label: str  # normalised — "def-2-1"
    paper_label: str  # the leading "Def 2.1" / "Lem 9.4" / "ARCAT" / "§9.2"
    paragraphs: list[str] = field(default_factory=list)  # raw HTML pieces
    notes: list[NoteBlock] = field(default_factory=list)
    snippets: list[_RawSnippet] = field(default_factory=list)
    tables: list["_RawTable"] = field(default_factory=list)


@dataclass
class _H2Block:
    """A H2 chapter of the document."""

    heading: str
    kind: str  # "paper" | "beyond" | "gap" | "verify" | "preamble" | "intro" | "other"
    # only set for paper-sections:
    paper_section_number: str | None = None
    paper_section_title: str | None = None
    intro_html: str = ""
    notes_html: str = ""
    tables: list[_RawTable] = field(default_factory=list)
    h3_blocks: list[_H3Block] = field(default_factory=list)


def _split_table_row(line: str) -> list[str]:
    """Split a pipe-table row into cells (preserving inline code spans)."""
    # The line starts and ends with `|` in well-formed Markdown; strip them.
    line = line.strip()
    if line.startswith("|"):
        line = line[1:]
    if line.endswith("|"):
        line = line[:-1]
    # Inline backticks may contain '|' — split only on un-escaped, un-quoted
    # pipes.  For AUDITOR.md the worst we see is `\|` (escaped) and pipes
    # inside backticks.  Implement a small state machine.
    cells: list[str] = []
    buf: list[str] = []
    in_code = False
    i = 0
    while i < len(line):
        ch = line[i]
        if ch == "\\" and i + 1 < len(line):
            buf.append(line[i : i + 2])
            i += 2
            continue
        if ch == "`":
            in_code = not in_code
            buf.append(ch)
        elif ch == "|" and not in_code:
            cells.append("".join(buf).strip())
            buf = []
        else:
            buf.append(ch)
        i += 1
    cells.append("".join(buf).strip())
    return cells


def _extract_snippet_provenance(raw: str) -> tuple[str | None, str | None]:
    """Pull the ``(* theories/path.v ... *)`` lead-comment, if any.

    Returns ``(source_file, source_section)`` — either may be None.
    """
    first_lines = raw.lstrip().splitlines()[:2]
    blob = "\n".join(first_lines)
    m_file = _VFILE_RE.search(blob)
    file_ = m_file.group(0) if m_file else None
    m_sec = _SECTION_QUAL_RE.search(blob)
    section = m_sec.group(1) if m_sec else None
    return file_, section


def _strip_label_kind(text: str) -> str:
    """Strip a leading ``"Def 2.1"`` / ``"§ 8"`` etc., keeping the rest as label."""
    return text.strip()


def _parse_h2_heading(heading: str) -> tuple[str, str | None, str | None]:
    """Classify a H2 heading.  Returns ``(kind, section_number, title)``."""
    m = _H2_PAPER_RE.match(heading)
    if m:
        return ("paper", m.group("num"), m.group("title").strip())
    if _H2_BEYOND_RE.match(heading):
        return ("beyond", None, "Beyond the paper")
    if _H2_GAP_RE.match(heading):
        return ("gap", None, "What is not formalised")
    if _H2_VERIFY_RE.match(heading):
        return ("verify", None, "How to verify")
    return ("other", None, heading)


def _h3_paper_label(heading: str) -> str:
    """Return the paper-label prefix of a H3 heading.

    Examples:
        "Def 2.1 (`isPrecone` / `Precone`)" -> "Def 2.1"
        "Lem 2.8 / 2.10 (`invf_omega_continuous`, `diff_omega_continuous`)"
            -> "Lem 2.8 / 2.10"
        "ARCAT (`MeasSubcat`)" -> "ARCAT"
        "Comonad (`der`, `dig`, ...)" -> "Comonad"
        "§9.2 (`lfp_fixpoint`, ...)" -> "§9.2"
    """
    # Strip everything from the first ``(`` (if present).
    paren = heading.find("(")
    label = (heading[:paren] if paren >= 0 else heading).strip()
    return label or heading.strip()


def _inline_to_html(md: MarkdownIt, source: str) -> str:
    """Render an inline-Markdown fragment to HTML (no surrounding <p>)."""
    src = source.strip()
    if not src:
        return ""
    rendered = md.render(src).strip()
    if rendered.startswith("<p>") and rendered.endswith("</p>"):
        rendered = rendered[3:-4]
    return rendered


def group(tokens: list[Token], source: str) -> list[_H2Block]:
    """Walk the token stream and build a list of H2 blocks.

    The first H2 block (kind=``preamble``) collects everything before
    the first H2.  Per H2, we collect:
        - intro Markdown (until the first table or first H3),
        - all overview-tables (we accept tables anywhere in the H2),
        - all H3 detail blocks with paragraphs / notes / snippets.
    """
    md = MarkdownIt("commonmark", {"html": True}).enable("table").enable("strikethrough")
    src_lines = source.splitlines()

    blocks: list[_H2Block] = []
    current = _H2Block(heading="Preamble", kind="preamble")
    blocks.append(current)
    current_h3: _H3Block | None = None
    # buffer of raw-Markdown lines for the current "paragraph slot"
    # (preferring per-token reads, but tokens carry .map which gives line range)

    def render_token_block(tok: Token) -> str:
        """Render a paragraph-or-list block back to HTML by source-line slicing."""
        if tok.map is None:
            return ""
        a, b = tok.map
        snippet = "\n".join(src_lines[a:b])
        return md.render(snippet).strip()

    def push_paragraph(html: str) -> None:
        nonlocal current_h3
        html = html.strip()
        if not html:
            return
        if current_h3 is not None:
            current_h3.paragraphs.append(html)
        else:
            current.intro_html = (current.intro_html + "\n" + html).strip()

    def push_note(html: str) -> None:
        nonlocal current_h3
        html = html.strip()
        if not html:
            return
        nb = NoteBlock(kind="note", html=html)
        if current_h3 is not None:
            current_h3.notes.append(nb)
        else:
            # H2-level blockquotes become notes_html of the section
            current.notes_html = (current.notes_html + "\n" + html).strip()

    def push_snippet(raw: str) -> None:
        nonlocal current_h3
        src_file, src_section = _extract_snippet_provenance(raw)
        s = _RawSnippet(raw=raw, source_file=src_file, source_section=src_section)
        if current_h3 is not None:
            current_h3.snippets.append(s)
        else:
            # Snippets directly under an H2 (Beyond chapter) — keep as a
            # synthetic detail block keyed by None.  We materialise them as
            # part of the H2's notes/intro: parse pulls these into beyond
            # contrib `snippets` instead.
            current.intro_html = (current.intro_html or "").rstrip()
            # We need a sentinel; encode the raw block as a marker we can
            # later split.  Use a hidden div.
            marker = f'<div data-coq-snippet data-source-file="{html_mod.escape(src_file or "")}" data-source-section="{html_mod.escape(src_section or "")}"></div>'
            current.intro_html += "\n" + marker
            current.intro_html += f"\n<pre data-coq-snippet-raw>{html_mod.escape(raw)}</pre>"

    i = 0
    while i < len(tokens):
        tok = tokens[i]
        t = tok.type

        if t == "heading_open" and tok.tag == "h1":
            j = i + 1
            if j < len(tokens) and tokens[j].type == "inline":
                # Skip — preamble heading.
                pass
            i += 1
            continue

        if t == "heading_open" and tok.tag == "h2":
            # finalise: flush any pending H3
            current_h3 = None
            j = i + 1
            text = tokens[j].content if j < len(tokens) else ""
            kind, num, title = _parse_h2_heading(text)
            block = _H2Block(
                heading=text, kind=kind, paper_section_number=num, paper_section_title=title
            )
            blocks.append(block)
            current = block
            # advance past inline + heading_close
            while i < len(tokens) and tokens[i].type != "heading_close":
                i += 1
            i += 1
            continue

        if t == "heading_open" and tok.tag == "h3":
            j = i + 1
            text = tokens[j].content if j < len(tokens) else ""
            paper_label = _h3_paper_label(text)
            h3 = _H3Block(
                heading=text,
                label=slugify_label(paper_label),
                paper_label=paper_label,
            )
            current.h3_blocks.append(h3)
            current_h3 = h3
            while i < len(tokens) and tokens[i].type != "heading_close":
                i += 1
            i += 1
            continue

        if t == "heading_open" and tok.tag in {"h4", "h5", "h6"}:
            # Promote H4 ("#### Code") content into the prose stream.
            j = i + 1
            text = tokens[j].content if j < len(tokens) else ""
            push_paragraph(f"<h4>{html_mod.escape(text)}</h4>")
            while i < len(tokens) and tokens[i].type != "heading_close":
                i += 1
            i += 1
            continue

        if t == "table_open":
            header: list[str] = []
            rows: list[_TableRow] = []
            # advance through table; capture text via raw line slicing
            assert tok.map is not None
            a, b = tok.map
            raw_lines = src_lines[a:b]
            # First non-empty line is the header, second is the separator.
            data_lines = [ln for ln in raw_lines if ln.strip()]
            if data_lines:
                header = _split_table_row(data_lines[0])
                # data_lines[1] is the separator (---|---)
                for ln in data_lines[2:]:
                    rows.append(_TableRow(cells=_split_table_row(ln)))
            table_obj = _RawTable(header=header, rows=rows)
            if current_h3 is not None:
                current_h3.tables.append(table_obj)
            else:
                current.tables.append(table_obj)
            # Skip past the table_close.
            while i < len(tokens) and tokens[i].type != "table_close":
                i += 1
            i += 1
            continue

        if t == "fence" and tok.info.strip().lower() == "coq":
            raw = tok.content
            push_snippet(raw)
            i += 1
            continue

        if t == "fence":
            # other fence (sh / bash / ...) — render as code block in prose
            push_paragraph(f"<pre><code class=\"language-{html_mod.escape(tok.info.strip())}\">{html_mod.escape(tok.content)}</code></pre>")
            i += 1
            continue

        if t == "blockquote_open":
            j = i + 1
            depth = 1
            inner_tokens: list[Token] = []
            while j < len(tokens) and depth > 0:
                if tokens[j].type == "blockquote_open":
                    depth += 1
                elif tokens[j].type == "blockquote_close":
                    depth -= 1
                    if depth == 0:
                        break
                inner_tokens.append(tokens[j])
                j += 1
            # Render the blockquote by slicing source.
            if tok.map is not None:
                a, b = tok.map
                snippet = "\n".join(src_lines[a:b])
                push_note(md.render(snippet))
            i = j + 1
            continue

        if t == "paragraph_open" or t == "bullet_list_open" or t == "ordered_list_open":
            push_paragraph(render_token_block(tok))
            # advance past matching close
            close = {"paragraph_open": "paragraph_close",
                     "bullet_list_open": "bullet_list_close",
                     "ordered_list_open": "ordered_list_close"}[t]
            depth = 1
            j = i + 1
            while j < len(tokens) and depth > 0:
                if tokens[j].type == t:
                    depth += 1
                elif tokens[j].type == close:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            i = j + 1
            continue

        if t == "hr":
            # horizontal rule — boundary marker; consume.
            i += 1
            continue

        # Everything else (html_block, etc.) — render by source slice.
        if tok.map is not None:
            push_paragraph(render_token_block(tok))
        i += 1

    return blocks


# -- stage 3: normalise + emit ----------------------------------------------


def _classify_paper_label_kind(label: str) -> tuple[str, str | None]:
    """Return (kind, number) for a paper label.

    Examples:
        "Def 2.1"          -> ("Def", "2.1")
        "Lem 2.8 / 2.10"   -> ("Lem", "2.8 / 2.10")
        "Cat 6"            -> ("Cat", "6")
        "Fubini (§4)"      -> ("Fubini", "4")
        "ARCAT"            -> ("Other", None)
        "§ 8"              -> ("Other", "8")
        "Sect 9.2"         -> ("Other", "9.2")
        "LL `!`"           -> ("Other", None)
        "(also)"           -> ("Other", None)
    """
    m = _LABEL_KIND_RE.match(label)
    if m:
        kind = m.group("kind").strip().capitalize()
        num_raw = (m.group("num") or "").strip()
        num: str | None = re.sub(r"\s+", " ", num_raw) if num_raw else None
        # Normalise kind capitalisations.
        kind_map = {
            "Def": "Def",
            "Thm": "Thm",
            "Lem": "Lem",
            "Prop": "Prop",
            "Cor": "Cor",
            "Cat": "Cat",
            "Fubini": "Fubini",
            "Rem": "Other",
            "Sect": "Other",
            "§": "Other",
        }
        kind = kind_map.get(kind, "Other")
        return kind, num
    return "Other", None


def _extract_rocq_cell(
    md: MarkdownIt,
    cell_md: str,
) -> tuple[list[str], list[str], str | None]:
    """Parse a Rocq-cell from an overview table.

    Returns (identifiers, file_paths, section_qualifier).
    """
    idents = list(dict.fromkeys(_BACKTICK_RE.findall(cell_md)))
    # Drop entries that look like a v-file path.
    idents = [ident for ident in idents if not ident.endswith(".v")]
    # Drop the source-file backticked candidates and Section qualifiers.
    idents = [ident for ident in idents if not ident.startswith("theories/")]
    idents = [ident for ident in idents if not ident.startswith("Section ")]
    files = list(dict.fromkeys(_VFILE_RE.findall(cell_md)))
    sec_match = _SECTION_QUAL_RE.search(cell_md)
    section = sec_match.group(1) if sec_match else None
    return idents, files, section


_COQ_LEXER = None


def _coq_lexer():
    global _COQ_LEXER
    if _COQ_LEXER is None:
        # Pygments >= 2.20 renamed CoqLexer -> RocqLexer; ``get_lexer_by_name``
        # accepts ``coq`` / ``rocq`` aliases on both old and new versions.
        try:
            _COQ_LEXER = _get_lexer_by_name("coq")
        except Exception:  # noqa: BLE001 — fallback to "rocq" alias
            _COQ_LEXER = _get_lexer_by_name("rocq")
    return _COQ_LEXER


def _highlight_coq(raw: str) -> str:
    """Run Pygments on a Coq block; return HTML wrapped in ``<div class="highlight">``."""
    formatter = HtmlFormatter(nowrap=False, cssclass="highlight coq")
    return highlight(raw, _coq_lexer(), formatter)


def normalise(
    blocks: list[_H2Block],
    *,
    resolver: CoqdocResolver,
    project_root: Path,
    regression_anchors: frozenset[str],
    strict: bool,
    warnings_out: list[str],
) -> Document:
    """Build a Document from the grouped blocks."""
    md = MarkdownIt("commonmark", {"html": True}).enable("table").enable("strikethrough")

    # -- preamble + section bodies ---------------------------------------
    preamble_html = ""
    verify_html = ""
    sections: list[Section] = []
    beyond: list[BeyondContrib] = []
    gaps: list[GapEntry] = []
    headlines_seen: list[str] = []
    seen_slugs: dict[str, str] = {}

    def claim_slug(slug: str, ctx: str) -> str:
        """Disambiguate duplicate slugs by suffixing -2, -3, ..."""
        if slug not in seen_slugs:
            seen_slugs[slug] = ctx
            return slug
        idx = 2
        while f"{slug}-{idx}" in seen_slugs:
            idx += 1
        new = f"{slug}-{idx}"
        warnings_out.append(
            f"duplicate slug '{slug}' (already used by '{seen_slugs[slug]}'); "
            f"renamed second occurrence at '{ctx}' to '{new}'"
        )
        seen_slugs[new] = ctx
        return new

    for blk in blocks:
        if blk.kind == "preamble":
            preamble_html = blk.intro_html
            continue
        if blk.kind == "verify":
            verify_html = blk.intro_html
            continue
        if blk.kind == "other":
            # The "How to read the Rocq references" intro chapter.
            preamble_html = (preamble_html + "\n\n<h2>" + blk.heading + "</h2>\n" + blk.intro_html).strip()
            continue
        if blk.kind == "gap":
            # In gap H2, the single table is the source of truth.
            for tbl in blk.tables:
                for row in tbl.rows:
                    if len(row.cells) < 3:
                        continue
                    paper_label = row.cells[0]
                    label_md = row.cells[0]
                    desc_md = row.cells[1]
                    reason_md = row.cells[2]
                    slug = claim_slug("gap-" + slugify_label(paper_label), paper_label)
                    gaps.append(
                        GapEntry(
                            id=slug,
                            paper_label=label_md,
                            description_html=_inline_to_html(md, desc_md),
                            reason_html=_inline_to_html(md, reason_md),
                        )
                    )
            continue

        # paper or beyond — extract entries from tables + detail blocks
        h3_by_label: dict[str, _H3Block] = {}
        h3_by_ident: dict[str, _H3Block] = {}
        for h3 in blk.h3_blocks:
            # Only register H3 blocks WITHOUT their own tables as detail
            # blocks of overview-table rows.  An H3 with its own table is
            # a structural sub-section (the "Beyond the paper" convention).
            if not h3.tables:
                h3_by_label[h3.label] = h3
                # Index by every backticked identifier in the H3 heading —
                # the convention is to list the lemma/definition names in
                # parens.  Lets us match e.g. table row "LL `!`" with idents
                # {Bang, nl, lin, lin_beta, lin_unique} against H3
                # "Linear exponential `!` (`Bang`, `nl`, ...)".
                for ident in _BACKTICK_RE.findall(h3.heading):
                    if ident and not ident.startswith("theories/"):
                        h3_by_ident.setdefault(ident, h3)

        section_id: str | None = None
        if blk.kind == "paper" and blk.paper_section_number:
            section_id = "sec-" + slugify_label(blk.paper_section_number)
            section_id = claim_slug(section_id, blk.heading)

        entries: list[Entry] = []

        for tbl in blk.tables:
            for row in tbl.rows:
                if not row.cells:
                    continue
                if len(row.cells) == 3:
                    paper_label = row.cells[0]
                    statement_md = row.cells[1]
                    rocq_md = row.cells[2]
                elif len(row.cells) == 2:
                    paper_label = row.cells[0]
                    statement_md = ""
                    rocq_md = row.cells[1]
                else:
                    if strict:
                        warnings_out.append(
                            f"row with {len(row.cells)} cells in '{blk.heading}': {row.cells!r}"
                        )
                    continue
                statement_html = _inline_to_html(md, statement_md)
                idents, files, sec_qual = _extract_rocq_cell(md, rocq_md)
                rocq_html_unused = _inline_to_html(md, rocq_md)  # noqa: F841 (future use)

                # Slug derivation: use the H3 label if matched, else from the paper label.
                base = slugify_label(paper_label)
                detail = None
                cross_refs: list[CrossRef] = []
                matched_h3_key: str | None = None
                if base in h3_by_label:
                    matched_h3_key = base
                else:
                    # Fuzzy 1: the H3 may carry a longer label like
                    # "Def 4.1 / 4.3" or "Fubini" while the table row is
                    # just "Def 4.1" / "Fubini (§4)".  Find the H3 whose
                    # slug starts with the row slug, or vice versa, with a
                    # matching kind+number prefix to avoid false matches.
                    for k in list(h3_by_label):
                        if k.startswith(base + "-") or base.startswith(k + "-"):
                            matched_h3_key = k
                            break
                    if matched_h3_key is None:
                        # Fuzzy 2: match by shared backticked identifier.
                        # Used for table-row "(also)" vs H3 "§9.2 (`lfp_…`)",
                        # and table-row "LL `!`" vs H3 "Linear exponential `!`".
                        for ident in idents:
                            cand = h3_by_ident.get(ident)
                            if cand is not None and cand.label in h3_by_label:
                                matched_h3_key = cand.label
                                break
                if matched_h3_key is not None:
                    h3 = h3_by_label.pop(matched_h3_key)
                    detail_html = "\n".join(h3.paragraphs).strip()
                    snippets = [
                        CoqSnippet(
                            source_file=s.source_file or "",
                            source_section=s.source_section,
                            highlighted_html=_highlight_coq(s.raw),
                        )
                        for s in h3.snippets
                    ]
                    detail = EntryDetail(
                        prose_html=detail_html, notes=h3.notes, snippets=snippets
                    )

                slug = claim_slug(base, paper_label)
                kind, number = _classify_paper_label_kind(paper_label)
                section_kind = "paper" if blk.kind == "paper" else "beyond"
                status = classify(
                    paper_label=paper_label,
                    section_kind=section_kind,
                    statement_html=statement_html,
                    regression_anchors=regression_anchors,
                )
                # Cross-ref scrape: look for "see *Beyond the paper* below"
                # in either column (a few Section-4 / Section-5 rows defer
                # the SAFT material to Beyond rather than spelling it out).
                combined_text = statement_md + " " + rocq_md
                if re.search(r"Beyond\s+the\s+paper", combined_text, re.IGNORECASE):
                    cross_refs.append(
                        CrossRef(kind="beyond", target="beyond", label="Beyond the paper")
                    )

                rocq_files: list[RocqFile] = []
                for vfile in files:
                    on_disk = (project_root / vfile).is_file()
                    if strict and not on_disk:
                        warnings_out.append(
                            f"file '{vfile}' referenced in '{paper_label}' but not on disk"
                        )
                    rocq_files.append(
                        RocqFile(
                            path=vfile,
                            section=sec_qual,
                            github_url=resolver.github_url(vfile),
                            coqdoc_url=resolver.coqdoc_url(vfile),
                            coqdoc_anchor=None,
                        )
                    )

                if "regression-anchor" in status:
                    headlines_seen.append(slug)

                paper_section_id = section_id or (
                    "beyond" if blk.kind == "beyond" else slugify_label(blk.heading)
                )
                entry = Entry(
                    id=slug,
                    paper_label=paper_label,
                    paper_kind=kind,
                    paper_number=number,
                    paper_section_id=paper_section_id,
                    statement_html=statement_html,
                    rocq_idents=idents,
                    rocq_files=rocq_files,
                    status=status,
                    detail=detail,
                    cross_refs=cross_refs,
                )
                entries.append(entry)

        # Any remaining (unmatched) H3 blocks become standalone entries —
        # this covers H3-only items inside "Beyond the paper" (no table row).
        for left_label, h3 in list(h3_by_label.items()):
            # Skip if the H3 looks like a section header reuse.
            if strict:
                # In a paper section, ALL H3 blocks should match a table row.
                # If not, surface as a warning.
                if blk.kind == "paper":
                    warnings_out.append(
                        f"H3 block '{h3.heading}' in section '{blk.heading}' has no matching table row"
                    )
            paper_label = h3.paper_label
            kind, number = _classify_paper_label_kind(paper_label)
            slug = claim_slug(slugify_label(paper_label), paper_label)
            detail_html = "\n".join(h3.paragraphs).strip()
            snippets = [
                CoqSnippet(
                    source_file=s.source_file or "",
                    source_section=s.source_section,
                    highlighted_html=_highlight_coq(s.raw),
                )
                for s in h3.snippets
            ]
            section_kind = "paper" if blk.kind == "paper" else "beyond"
            status = classify(
                paper_label=paper_label,
                section_kind=section_kind,
                statement_html=detail_html,
                regression_anchors=regression_anchors,
            )
            paper_section_id = section_id or (
                "beyond" if blk.kind == "beyond" else slugify_label(blk.heading)
            )
            entries.append(
                Entry(
                    id=slug,
                    paper_label=paper_label,
                    paper_kind=kind,
                    paper_number=number,
                    paper_section_id=paper_section_id,
                    statement_html="",
                    rocq_idents=[],
                    rocq_files=[],
                    status=status,
                    detail=EntryDetail(prose_html=detail_html, notes=h3.notes, snippets=snippets),
                    cross_refs=[],
                )
            )

        if blk.kind == "paper":
            assert section_id is not None
            sections.append(
                Section(
                    id=section_id,
                    paper_section=f"§ {blk.paper_section_number} — {blk.paper_section_title}",
                    paper_section_number=blk.paper_section_number or "",
                    title=blk.paper_section_title or "",
                    intro_html=blk.intro_html,
                    entries=entries,
                    notes_html=blk.notes_html,
                )
            )
        elif blk.kind == "beyond":
            # Build one BeyondContrib PER H3 sub-heading in the Beyond
            # chapter; entries come from the per-H3 overview tables (if
            # any), and prose/snippets fill the contribution's body.
            for h3 in blk.h3_blocks:
                contrib_id = claim_slug("beyond-" + slugify_label(h3.paper_label), h3.heading)
                contrib_entries: list[Entry] = []
                for tbl in h3.tables:
                    for row in tbl.rows:
                        if not row.cells:
                            continue
                        if len(row.cells) == 3:
                            paper_label = row.cells[0]
                            statement_md = row.cells[1]
                            rocq_md = row.cells[2]
                        elif len(row.cells) == 2:
                            paper_label = row.cells[0]
                            statement_md = ""
                            rocq_md = row.cells[1]
                        else:
                            continue
                        statement_html = _inline_to_html(md, statement_md)
                        idents, files, sec_qual = _extract_rocq_cell(md, rocq_md)
                        slug = claim_slug(slugify_label(paper_label), paper_label)
                        kind, number = _classify_paper_label_kind(paper_label)
                        status = classify(
                            paper_label=paper_label,
                            section_kind="beyond",
                            statement_html=statement_html,
                            regression_anchors=regression_anchors,
                        )
                        rocq_files = []
                        for vfile in files:
                            if strict and not (project_root / vfile).is_file():
                                warnings_out.append(
                                    f"file '{vfile}' referenced in '{paper_label}' "
                                    f"but not on disk"
                                )
                            rocq_files.append(
                                RocqFile(
                                    path=vfile,
                                    section=sec_qual,
                                    github_url=resolver.github_url(vfile),
                                    coqdoc_url=resolver.coqdoc_url(vfile),
                                    coqdoc_anchor=None,
                                )
                            )
                        contrib_entries.append(
                            Entry(
                                id=slug,
                                paper_label=paper_label,
                                paper_kind=kind,
                                paper_number=number,
                                paper_section_id=contrib_id,
                                statement_html=statement_html,
                                rocq_idents=idents,
                                rocq_files=rocq_files,
                                status=status,
                                detail=None,
                                cross_refs=[],
                            )
                        )
                contrib_snippets = [
                    CoqSnippet(
                        source_file=s.source_file or "",
                        source_section=s.source_section,
                        highlighted_html=_highlight_coq(s.raw),
                    )
                    for s in h3.snippets
                ]
                beyond.append(
                    BeyondContrib(
                        id=contrib_id,
                        title=h3.paper_label,
                        intro_html="\n".join(h3.paragraphs),
                        entries=contrib_entries,
                        snippets=contrib_snippets,
                        notes_html="\n".join(n.html for n in h3.notes),
                    )
                )
            # H2-level entries (rows belonging to no H3) and the chapter
            # intro live in a synthetic "overview" contrib if any exist.
            if entries:
                beyond.insert(
                    0,
                    BeyondContrib(
                        id=claim_slug("beyond-overview", blk.heading),
                        title="Overview",
                        intro_html=blk.intro_html,
                        entries=entries,
                        snippets=[],
                        notes_html=blk.notes_html,
                    ),
                )

    return Document(
        preamble_html=preamble_html,
        sections=sections,
        beyond=beyond,
        gaps=gaps,
        verify_instructions_html=verify_html,
        axiom_anchors=AxiomAnchors(
            regression="Thm 6.5", headlines=list(dict.fromkeys(headlines_seen))
        ),
        build_meta=BuildMeta(commit="", built_at="", auditor_lines=0),
    )


# -- top-level driver -------------------------------------------------------


def parse(
    source: str,
    *,
    resolver: CoqdocResolver,
    project_root: Path,
    regression_anchors: frozenset[str] = DEFAULT_REGRESSION_ANCHORS,
    strict: bool = False,
) -> tuple[Document, list[str]]:
    """Parse the AUDITOR.md source.  Returns ``(document, warnings)``."""
    warnings_out: list[str] = []
    tokens = lex(source)
    blocks = group(tokens, source)
    doc = normalise(
        blocks,
        resolver=resolver,
        project_root=project_root,
        regression_anchors=regression_anchors,
        strict=strict,
        warnings_out=warnings_out,
    )
    return doc, warnings_out


def parse_file(
    path: str | Path,
    *,
    resolver: CoqdocResolver,
    project_root: Path,
    regression_anchors: frozenset[str] = DEFAULT_REGRESSION_ANCHORS,
    strict: bool = False,
) -> tuple[Document, list[str]]:
    """Parse a file on disk.  Convenience wrapper around :func:`parse`."""
    text = Path(path).read_text(encoding="utf-8")
    doc, warns = parse(
        text,
        resolver=resolver,
        project_root=project_root,
        regression_anchors=regression_anchors,
        strict=strict,
    )
    doc.build_meta.auditor_lines = text.count("\n") + (0 if text.endswith("\n") else 1)
    return doc, warns


__all__ = [
    "parse",
    "parse_file",
    "slugify_label",
    "lex",
    "group",
    "normalise",
]
