# Roadmap for the hourly formalize task

The :07 task does the FIRST unchecked item below, one item per run. When the build for that
item passes, the next run ticks it (`- [ ]` -> `- [x]`) in the same commit as its next item.
If the build is failing, fixing it comes before any new item.
`- [~]` means the interactive session already wrote the item and it is waiting for CI: if
`verification/STATUS.md` shows it compiled, tick it (`[~]` -> `[x]`) and move on; if it failed,
fixing it is the next item. Never redo a `[~]` item from scratch.

Every new file goes in `SteklovAudit/`, starts with `import Mathlib`, states in its docstring
what it does NOT prove, and uses no `sorry`, `axiom` or other escape hatch.

## A. Checklist for Lemma 7.1' (uniform localized Hilbert–Schmidt bound)

The written proof is in the Claude Doc "Uniform localized Hilbert–Schmidt bound (7.2')".
Put these in `SteklovAudit/UniformHS71.lean` (one item per run, appended to that file).

- [x] A1. (λ⁻¹ + L)² ≤ (1 + L)² for λ ≥ 1, L ≥ 0.
- [x] A2. C(1 + λL)² · λ⁻² = C(λ⁻¹ + L)² for λ > 0.
- [x] A3. For λ > 0: t/λ ≤ L ↔ t ≤ λL, and the resulting equality of spectral indicator
      sums over a finite spectrum (1_[0,L](λ⁻¹T) = 1_[0,λL](T)).
- [x] A5. λ⁻¹ · C · (λ · G) = C · G for λ > 0 (gradient-scaling cancellation).
- [x] A6. Finite-dimensional: for a symmetric projection matrix P and a diagonal 0 ≤ η ≤ 1_F,
      Tr(η P η) ≤ Tr(1_F P 1_F). (Use Matrix and Matrix.trace, or spectral coordinates.)
- [x] A7. Finite-dimensional: Frobenius norm of X * Y ≤ Frobenius(X) * operator-norm(Y), or
      in spectral coordinates with Y diagonal: hs2 (X i j * y j) ≤ hs2 X * (sup |y|)².
- [x] A8. ∫₀¹ s^(2β−2) ds = 1/(2β−1) for β > 1/2, and ∫₀¹ s^(2μ−1) ds = 1/(2μ) for μ > 0.
- [x] A9. Σ_{j≥1} 2^(−4j) = 1/15 (tsum), or the finite partial sums ≤ 1/15.
- [x] A10. Finite-dimensional pointwise criterion: if |Σ_k T i k f k| ≤ w i · ‖f‖ for all f,
      then Σ_{i,k} (T i k)² ≤ Σ_i (w i)².
- [x] A11. For L ≥ 1, 0 ≤ w, 4w < L, C ≥ 0: (2/L) · Σ_{n<N} (2w/L)ⁿ · C(1+L+w) ≤ 12C.

## B. Abstract operator layer (spectral coordinates at a finite cutoff)

Build on `SteklovAudit/AbstractTransfer.lean` (namespace `SteklovAudit.AbstractTransfer`).
Each item is a new file `SteklovAudit/AbstractTransferB<n>.lean` importing Mathlib and
re-using the definitions (`Data`, `Data.K`, `hs2`, `PDEInputs`) by importing
`SteklovAudit.AbstractTransfer`.

- [x] B1. Spectral data, defect, Lipschitz transfer, trace transfer, off-band bound,
      named PDE inputs, and the naive O(L²) trace comparison (`AbstractTransfer.lean`).
- [x] B2. Duhamel with the time factor, entrywise: ‖exp(i t x) − exp(i t y)‖ ≤ |t| · |x − y|
      for real t, x, y (complex exponential), and the HS form
      ‖e^{itA} J − J e^{itB}‖²_HS ≤ t² ‖K‖²_HS in spectral coordinates.
- [x] B3. Energy splitting: split pairs (i, j) by max(a i, b j) ≤ M versus > M. Add a named
      tail hypothesis `tail : hs2 (K restricted to energies > M) ≤ τ(M)` and prove the trace
      comparison is ≤ Lip(f) · (low-energy part + high-energy part) with explicit terms.
- [x] B4. Time-factor cancellation: for a smoothed step F_S whose difference quotient is
      bounded by S·c (a hypothesis), show the cumulative comparison is bounded by
      c·S·(C(1+M)·√(mass) + √τ(M)·√(mass)); then state exactly which growth of τ and choice
      of M = M(L) makes it o(L). This is the heart of (7.29).
- [x] B5. Connect B4 to `SteklovAudit.sharp_real_law_of_two_scale`: named inputs + tail
      hypothesis ⇒ `HasRealTwoScaleBound`, hence `HasSharpRealLaw`.
- [x] B6. Band part of Lemma 5.1 in spectral coordinates (window counting from band and
      off-band pieces), using `offband_window_bound`.

## C. Statement-first audit: main theorem from named hypotheses, then shrink the list

`SteklovAudit/MainConditional.lean` proves Theorem 11.1 / (11.4), with the paper's constants, from
the ledger `Thm111Inputs` (hypotheses tagged `[H1]`..`[H6]`). `axiom_audit.py` counts them in
STATUS.md. Every item below should either remove a hypothesis, replace one by strictly weaker
named inputs, or check a definition. Never add a hypothesis without removing a stronger one.

- [x] C1. `MainConditional.lean`: ledger H1–H6, `theorem_11_1_of_inputs`, `formula_11_4_of_inputs`,
      non-vacuity (`nonvacuous`) and nontriviality (`conclusion_nontrivial`).
- [x] C2. Definition check for `dihedralCoeff`: prove the integrand of (1.4) is integrable on
      (0, ∞) for 0 < α < π (bounded near 0, ≤ 4e^{−2αv} for large v), so the Bochner integral is
      not Mathlib's junk value 0. File `SteklovAudit/DihedralIntegrable.lean`.
- [x] C3. Right-angle calibration: `dihedralCoeff (π/2) = 1/(2π)` (∫₀^∞ sech(πv) dv = 1/2).
- [x] C4. Shrink H5: state (7.38)/(7.45) (model edge law) and the cumulative comparison o(L)
      (from B4/B5) as two named inputs and prove `[H5 edge]` from them.
- [ ] C5. Shrink H1/H2: finite-dimensional trace linearity of a squared partition,
      Tr(P) = Σ_k Tr(χ_k P χ_k) when Σ_k χ_k² = 1 (diagonal χ_k), and additivity of the area
      coefficients; then derive `[H1]` and `[H2]` from a partition structure.
- [ ] C6. Shrink H3: Σ_e ∫ q_e² = 6a − O(ε) from cutoff support lengths (interval arithmetic).

## Not attempted here

Constructing the Dirichlet-to-Neumann operator, Sobolev traces on Lipschitz domains, and the
PDE estimates (2.2), (5.5), (7.1), (7.15), propagation (9.1). These stay named hypotheses.
