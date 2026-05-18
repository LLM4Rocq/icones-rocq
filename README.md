# Icones — Integration in Cones, formalized in Rocq

A Rocq/mathcomp-analysis formalization of *Integration in Cones* by Thomas Ehrhard
and Guillaume Geoffroy ([LMCS 21:1, 2025](https://lmcs.episciences.org/15021),
[arXiv:2212.02371](https://arxiv.org/abs/2212.02371)).

## Status

Early development. See [`PLAN.md`](./PLAN.md) for scope, milestones, and the
strategic decisions guiding the formalization. The current target is the MVP:
a faithful formalization of paper §2 – §4 + §5.1 + §6, culminating in
Theorem 6.5 (the substochastic-kernel category `Skern` embeds fully and
faithfully into `ICones`).

## Build

Requires:

- Rocq 9.1+ (tested on 9.1.1)
- `rocq-mathcomp` 2.5+
- `rocq-mathcomp-analysis` 1.16+
- `rocq-hierarchy-builder` 1.10+
- `rocq-elpi` 3.3+

Install dependencies from the released opam repository:

```bash
opam install rocq-mathcomp-analysis rocq-hierarchy-builder
```

Build:

```bash
make
```

## Layout

```
theories/
├── prelude/          -- classical-logic + ereal/nonneg helpers + ω-cpo
└── cones/            -- precone, cone, category Cones (paper §2)
```

Further sub-directories (`mcones/`, `icones/`, `homs/`, `kernels/`) appear as
the corresponding milestones M2–M5 land.

## License

MIT. See [`LICENSE`](./LICENSE).

## Paper sources

The paper PDF and an extracted text rendering live under `paper/`:

- `paper/icones.pdf` (1 MB)
- `paper/icones.txt` (252 KB, 98 pages of UTF-8)

The extracted text is the canonical reference inside the Rocq sources;
proofs annotate the paper section and lemma number they correspond to.
