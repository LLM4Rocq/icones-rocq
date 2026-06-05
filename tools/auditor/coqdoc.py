"""coqdoc URL resolver and GitHub source-file URL builder.

Reads the project's ``_CoqProject`` to learn the logical name binding
(``-Q theories Icones``), then maps every ``theories/foo/bar.v`` to the
coqdoc page ``Icones.foo.bar.html``.

Source-file GitHub links are built from a ``--github-repo`` argument
(``LLM4Rocq/icones-rocq``) and a commit SHA.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class CoqProjectBinding:
    """One ``-Q phys logical`` (or ``-R``) binding from ``_CoqProject``."""

    physical: str  # "theories"
    logical: str  # "Icones"


_BINDING_RE = re.compile(r"^\s*-([QR])\s+(\S+)\s+(\S+)\s*$")


def parse_coqproject(coqproject_path: str | Path) -> list[CoqProjectBinding]:
    """Extract -Q / -R bindings from a _CoqProject file.

    Lines starting with ``#`` and blank lines are ignored.
    """
    path = Path(coqproject_path)
    bindings: list[CoqProjectBinding] = []
    if not path.is_file():
        return bindings
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        m = _BINDING_RE.match(stripped)
        if m:
            bindings.append(CoqProjectBinding(physical=m.group(2), logical=m.group(3)))
    return bindings


class CoqdocResolver:
    """Resolve ``theories/foo/bar.v`` paths to coqdoc URLs and GitHub URLs."""

    def __init__(
        self,
        *,
        bindings: list[CoqProjectBinding],
        github_repo: str,
        commit: str,
        coqdoc_base: str = "docs/",
    ) -> None:
        self._bindings = bindings
        self._github_repo = github_repo.strip().strip("/")
        self._commit = commit or "main"
        # coqdoc lives under <site>/docs/ in the combined deployment;
        # rendered pages link relative to the auditor root.
        self._coqdoc_base = coqdoc_base.rstrip("/") + "/"

    # -- coqdoc -----------------------------------------------------------

    def coqdoc_url(self, vfile: str, anchor: str | None = None) -> str | None:
        """Return the coqdoc URL for a path of the form ``physical/.../X.v``.

        Returns None if no binding matches.
        """
        if not vfile.endswith(".v"):
            return None
        for b in self._bindings:
            phys = b.physical.rstrip("/") + "/"
            if vfile.startswith(phys):
                rel = vfile[len(phys) :]
                rel = rel[:-2]  # strip ".v"
                parts = [b.logical, *rel.split("/")]
                url = f"{self._coqdoc_base}{'.'.join(parts)}.html"
                if anchor:
                    url = f"{url}#{anchor}"
                return url
        return None

    # -- GitHub -----------------------------------------------------------

    def github_url(self, vfile: str, line: int | None = None) -> str:
        """Return a GitHub blob URL for ``vfile`` at ``self._commit``.

        The path is taken as repository-relative (no quoting).
        """
        if not self._github_repo:
            # Best-effort — return the raw relative path.
            return vfile
        url = f"https://github.com/{self._github_repo}/blob/{self._commit}/{vfile}"
        if line is not None and line > 0:
            url = f"{url}#L{line}"
        return url
