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
- [x] C5. Shrink H1/H2: finite-dimensional trace linearity of a squared partition,
      Tr(P) = Σ_k Tr(χ_k P χ_k) when Σ_k χ_k² = 1 (diagonal χ_k), and additivity of the area
      coefficients; then derive `[H1]` and `[H2]` from a partition structure.
- [x] C6. Shrink H3 (`SteklovAudit/EdgeLength.lean`): Σ_e ∫ q_e² = 6a − O(ε) from cutoff support lengths (interval arithmetic).
- [x] C7. Definition sanity for (1.4) in `SteklovAudit/DihedralSanity.lean`: `dihedralCoeff π = 0`,
      strict positivity of the integrand and `0 < dihedralCoeff α` for 0 < α < π (so the linear
      coefficient `6 a c_{α₀}` is nonzero), `cos α₀ = 1/3`, `α₀ < π/2`.
- [x] C8. Non-vacuity of the C6 ledger in `SteklovAudit/LedgerNonvacuousC6.lean`: an explicit
      `Thm111InputsC6` instance (one coordinate, trivial edge cutoffs) and `nonvacuous_C6`.
- [x] C9. Quantitative edge coefficient in `SteklovAudit/DihedralBounds.lean`:
      `dihedralCoeff α ≤ 4(π − α) / (π α²)` for 0 < α < π, from `DihedralIntegrable.integrand_bound`
      and ∫₀^∞ e^{−αv} dv = 1/α; specialize at α₀.
- [x] C10. Monotonicity in `SteklovAudit/DihedralBounds.lean`: the integrand of (1.4) is
      antitone in α on (0, π) for each v > 0, hence `dihedralCoeff` is antitone on (0, π);
      with C3 this gives `dihedralCoeff α₀ ≥ 1/(2π)` since α₀ < π/2.
- [ ] C11. Numeric bracket for the edge coefficient (new file `SteklovAudit/DihedralBracket.lean`):
      `π/3 < α₀` (arccos is strictly antitone and arccos(1/2) = π/3), hence with C9 (the bound
      4(π − α)/(π α²) is antitone in α) `dihedralCoeff α₀ ≤ 24/π²`; together with C10,
      `1/(2π) ≤ c_{α₀} ≤ 24/π²`.

## D. Consistency checks on the conclusion, and the paper's form of the inputs

Written by an interactive session (2026-11-04). Each file compiled on branch `claude/roadmap-d`
(STATUS there: PASS 278/278) before being copied to main unchanged. None of these items proves
any of `[H1]`–`[H6]` or the main theorem.

- [x] D1. Sign of `c_α` and `c_π = 0`: covered by C7 (`DihedralSanity.lean`); no separate file.
- [x] D2. `c_α` antitone and `c_{α₀} ≥ 1/(2π)`: covered by C10 (`DihedralBounds.lean`); no separate file.
- [~] D3. Uniqueness of the coefficients (`SteklovAudit/SharpLawUnique.lean`): two sharp laws for
      the same `N` have the same `(A, B)`; so the edge invariant `c` in (11.4) is determined by the
      counting function (`edge_invariant_determined`), and with `a, c ≠ 0` the two-term law excludes
      the one-term law (`not_one_term_law`).
- [~] D4. Scaling consistency (`SteklovAudit/ScalingLaw.lean`): with `N_a(L) = N_1(aL)` (eigenvalues
      scale like 1/a; this relation is assumed, not proved), the law with the paper's constants at
      side 1 holds iff it holds at side `a > 0` (`law_scaling_iff`). Checks the `a²` and `a` factors.
- [~] D5. `[H4 vertex]` in the paper's form (`SteklovAudit/VertexLog.lean`): `log L ≤ 2√L`, and the
      (7.49) bound `C_V ε L + K(log L + 1)` implies the `[H4]` form; ledger `Thm111InputsD5`
      (C6 ledger with H4 in the (7.49) form), `toC6`, `theorem_11_1_of_D5`. A restatement, not a
      weakening: the hypothesis count is unchanged.
- [~] D6. Non-vacuity of the D5 ledger (`SteklovAudit/LedgerNonvacuousD5.lean`), reusing the C8 witness.
- [~] D7. Real law ⇒ integer-level law (`SteklovAudit/RealToIntegerLaw.lean`):
      `HasSharpRealLaw N A B → HasSharpTwoTermLawOnIntegers (n ↦ N(n+1)) A B`, and the ledger gives the
      integer-level law with the paper's constants. The converse is not claimed.

## Not attempted here

Constructing the Dirichlet-to-Neumann operator, Sobolev traces on Lipschitz domains, and the
PDE estimates (2.2), (5.5), (7.1), (7.15), propagation (9.1). These stay named hypotheses.
