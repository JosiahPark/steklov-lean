# arXiv preprint

This folder holds the manuscript that the Lean project checks:

> **Edge spectral invariants and second-order Steklov asymptotics for the regular tetrahedron**, Josiah Park.

Put the arXiv source (`.tex`, `.bib`, figures) and the compiled PDF here. Add the arXiv identifier and link
here once it has been assigned.

- arXiv: [2611.02733v1](https://arxiv.org/abs/2611.02733v1) (math.SP, submitted 2026-11-02)
- Files here, downloaded from arXiv: `2611.02733v1.pdf` (compiled PDF), `steklov_tetrahedron.tex` and
  `00README.json` (the contents of the arXiv source archive `arXiv-2611.02733v1.tar.gz`).

The Lean files in `SteklovAudit/` formalize only the checkable parts of the manuscript. The main theorem
(Theorem 1.3 / 11.1) is **not** proved in Lean: it is conditional on the named hypotheses `[H1]`–`[H6]`
listed in `verification/STATUS.md`.
