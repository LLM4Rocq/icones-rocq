"""Status-flag classifier for parser-extracted entries.

The status set is:
- ``axiom-free``         : default for paper-§ H2 sections.
- ``beyond-paper``       : entries inside the "Beyond the paper" H2.
- ``gap``                : entries inside "What is not formalised".
- ``regression-anchor``  : explicit hard-coded list (see DEFAULT_REGRESSION_ANCHORS).
- ``discharged-deferred``: textual heuristic (see DISCHARGED_PATTERNS).

The classifier is deliberately stateless and pure.
"""

from __future__ import annotations

import re

# By spec we start with just Thm 6.5 — the regression anchor lemma
# Skern_to_ICones_fully_faithful — as the hardcoded set.
DEFAULT_REGRESSION_ANCHORS: frozenset[str] = frozenset(
    {
        "Thm 6.5",
    }
)

# Heuristic for "discharged previously-deferred" lemma phrasing.
DISCHARGED_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"previously[- ]deferred", re.IGNORECASE),
    re.compile(r"deferred .*?(now )?discharged", re.IGNORECASE),
    re.compile(r"discharged( as|d as)? the (previously[- ]deferred|follow[- ]up)", re.IGNORECASE),
)


def classify(
    *,
    paper_label: str,
    section_kind: str,
    statement_html: str,
    regression_anchors: frozenset[str] = DEFAULT_REGRESSION_ANCHORS,
) -> list[str]:
    """Compute the status flags for a single entry.

    Args:
        paper_label: verbatim label like "Thm 6.5", "Def 2.1".
        section_kind: one of ``"paper"``, ``"beyond"``, ``"gap"`` —
            the structural origin of the entry.
        statement_html: HTML rendering of the statement column (for heuristics).
        regression_anchors: a set of labels that should be tagged
            ``regression-anchor``.

    Returns:
        A subset of the allowed status strings.  Order is stable.
    """
    flags: list[str] = []
    if section_kind == "paper":
        flags.append("axiom-free")
    elif section_kind == "beyond":
        flags.append("beyond-paper")
    elif section_kind == "gap":
        flags.append("gap")
        # gap entries are not axiom-free; skip the other heuristics
        return flags
    else:
        # unknown section_kind — leave empty rather than guess
        pass

    if paper_label in regression_anchors:
        flags.append("regression-anchor")

    for pat in DISCHARGED_PATTERNS:
        if pat.search(statement_html):
            flags.append("discharged-deferred")
            break

    return flags
