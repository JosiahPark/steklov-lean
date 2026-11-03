# Steklov tetrahedron: Lean verification

This Lean 4 + Mathlib (v4.35.0) project formalizes the checkable lemmas behind
"Edge spectral invariants and second-order Steklov asymptotics for the regular tetrahedron".
GitHub Actions rebuilds it and audits its axioms on every push, and every 6 hours as a safety check.

## What is and is not verified

- **Submitted to Lean** (see `verification/STATUS.md` for which ones actually pass): 130 theorems
  from the hourly runs through run 23. They cover tetrahedron counts and area, the half-angle
  identity, scale exponents, window arithmetic, finite spectral-trace localization, discrete and
  truncated Duhamel identities, finite Hilbert-Schmidt tail and spectral-gap bounds, off-band
  iteration, the Section 7 barrier inequalities, the spectral-sandwich budget, Section 9 scale and
  cell budgets, Section 10 nonreturn algebra, Section 11 partition and counting bounds, and the
  two-scale limit deductions. Several modules are deliberate obstructions (counterexamples showing
  what a uniform estimate cannot follow from).
- **Not checked:** the main theorem. `sharp_integer_law_of_two_scale` and
  `sharp_real_law_of_two_scale` assume the uniform two-scale bound as a hypothesis. Lean has no
  definition of the Dirichlet-to-Neumann operator, so the open gaps (7.2), (7.29), (7.38)/(7.45)
  and (9.1) are outside what this project proves.

## Layout

- `SteklovAudit.lean`: all Lean modules in one file, one commented section per original module.
- `axiom_audit.py`: after `lake build`, runs `#print axioms` on every theorem and fails on `sorry` or on
  non-standard axioms. It writes `verification/STATUS.md` and `verification/STATUS.json`.
- `.github/workflows/lean.yml`: builds and audits the project, then commits the status whenever it changes.

## Running locally

With elan installed and network access to the Mathlib cache:

```
lake exe cache get && lake build && python3 axiom_audit.py
```
