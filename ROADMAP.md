# Roadmap for the hourly formalize task

The :07 task does the FIRST unchecked item below, one item per run. When the build for that
item passes, the next run ticks it (`- [ ]` -> `- [x]`) in the same commit as its next item.
If the build is failing, fixing it comes before any new item.
`- [~]` means the interactive session already wrote the item and it is waiting for CI: if
`verification/STATUS.md` shows it compiled, tick it (`[~]` -> `[x]`) and move on; if it failed,
fixing it is the next item. Never redo a `[~]` item from scratch.
`- [-]` means deferred: skip it; it is not the next item.

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
- [x] C11. Numeric bracket for the edge coefficient (new file `SteklovAudit/DihedralBracket.lean`):
      `π/3 < α₀` (arccos is strictly antitone and arccos(1/2) = π/3), hence with C9 (the bound
      4(π − α)/(π α²) is antitone in α) `dihedralCoeff α₀ ≤ 24/π²`; together with C10,
      `1/(2π) ≤ c_{α₀} ≤ 24/π²`.

## D. Consistency checks on the conclusion, and the paper's form of the inputs

Written by an interactive session (2026-11-04). Each file compiled on branch `claude/roadmap-d`
(STATUS there: PASS 278/278) before being copied to main unchanged. None of these items proves
any of `[H1]`–`[H6]` or the main theorem.

- [x] D1. Sign of `c_α` and `c_π = 0`: covered by C7 (`DihedralSanity.lean`); no separate file.
- [x] D2. `c_α` antitone and `c_{α₀} ≥ 1/(2π)`: covered by C10 (`DihedralBounds.lean`); no separate file.
- [x] D3. Uniqueness of the coefficients (`SteklovAudit/SharpLawUnique.lean`): two sharp laws for
      the same `N` have the same `(A, B)`; so the edge invariant `c` in (11.4) is determined by the
      counting function (`edge_invariant_determined`), and with `a, c ≠ 0` the two-term law excludes
      the one-term law (`not_one_term_law`).
- [x] D4. Scaling consistency (`SteklovAudit/ScalingLaw.lean`): with `N_a(L) = N_1(aL)` (eigenvalues
      scale like 1/a; this relation is assumed, not proved), the law with the paper's constants at
      side 1 holds iff it holds at side `a > 0` (`law_scaling_iff`). Checks the `a²` and `a` factors.
- [x] D5. `[H4 vertex]` in the paper's form (`SteklovAudit/VertexLog.lean`): `log L ≤ 2√L`, and the
      (7.49) bound `C_V ε L + K(log L + 1)` implies the `[H4]` form; ledger `Thm111InputsD5`
      (C6 ledger with H4 in the (7.49) form), `toC6`, `theorem_11_1_of_D5`. A restatement, not a
      weakening: the hypothesis count is unchanged.
- [x] D6. Non-vacuity of the D5 ledger (`SteklovAudit/LedgerNonvacuousD5.lean`), reusing the C8 witness.
- [x] D7. Real law ⇒ integer-level law (`SteklovAudit/RealToIntegerLaw.lean`):
      `HasSharpRealLaw N A B → HasSharpTwoTermLawOnIntegers (n ↦ N(n+1)) A B`, and the ledger gives the
      integer-level law with the paper's constants. The converse is not claimed.
- [x] D8. The converse of D7 fails (`SteklovAudit/GridLaw.lean`): the monotone step function
      `A⌊L⌋₊²` (`A > 0`) has the integer-level law `(A, 0)` exactly but `HasSharpRealLaw` for no `B`
      (`step_integer_law`, `step_not_real_law`). Compiled on branch `claude/roadmap-e`.
- [x] D9. The converse with monotonicity and fine grids (`SteklovAudit/GridLaw.lean`): a monotone `N`
      with the law along every grid `k/m` has the real-parameter law (`real_law_of_fine_grids`).
      Compiled on branch `claude/roadmap-e`.

## E. Results from continuations 25–43 (combined archive, 2026-11-04)

The continuations proved several finite-dimensional facts on paper but only wrote scalar Lean
fragments, never compiled. E1–E2 state the operator-level results in the spectral coordinates of
`AbstractTransfer` and prove them; E3 brings the scalar fragments in under CI.

E4–E7 were written on main by the formalize run of 16:58 UTC (commits c718c10, 196a6b0); with the
E6 fix (c44fad3) all of E1–E7 compiled (STATUS PASS 341/341, 17:10 UTC). An interactive session wrote independent versions on branch `claude/roadmap-e` at the
same time; the parts that add something are E11–E13 below (and D8–D9).

- [x] E1. `SteklovAudit/SpectralCounting.lean`: `window_gap_leakage` (cont. 25), `weighted_leakage`
      (cont. 42), `counting_transfer` N_B(L) ≤ N_A(L+δ) + E + δ⁻²‖K P‖² (cont. 30/39),
      `counting_two_sided` (cont. 32), `threshold_instability` (cont. 33: J = I, ‖K‖²_HS = 1/n,
      counts differ by n, so δ > 0 is necessary), `trace_rank_amplification` (cont. 27).
      Cont. 43's Lipschitz HS transfer is already `AbstractTransfer.transfer_hs`.
- [x] E2. `SteklovAudit/FixedScaleTauberian.lean`: monotone sandwich for finite kernels and
      `sharp_law_of_shrinking_scales` (cont. 36–41): smoothed sharp law with the same A, B at each
      of a sequence of fixed widths σ_n → 0 gives the sharp law for N. No uniformity in n needed.
- [x] E3. The 17 scalar modules `Section7*/Section9*/Section11*` from continuations 25–43, with
      compile fixes (import order, missing `import Mathlib`, a duplicate name renamed to
      `weighted_gap_square`, `positivity` steps that needed hypotheses). Two tautologies whose
      hypothesis equals the conclusion were removed (`shifted_model_squeeze`,
      `transfer_budget_power`).
- [x] E4. `cone_ball_window` (Section5Scaling, in `SteklovAudit.lean`) has a hypothesis identical
      to its conclusion. Restate it so it proves something, or delete it; add a check to
      `axiom_audit.py` that flags any theorem whose proof is just a hypothesis name.
- [x] E5. Continuation 35 counterexample, discrete part: for N(x) = ⌊10x² + x sin 2πx⌋ show
      N(k + 1/4) − 10(k + 1/4)² ≥ k (so N is not 10L² + o(L)), while F' > 0 on [1, ∞).
      One fixed smoothing width cannot give the sharp law; E2 needs widths → 0.
- [x] E6. Asymptotic form of E1: if the model count is aL² + bL + o(L), the isometry defects are
      o(L) and ‖K P‖²_HS = O(L^α) with α < 1, then δ = L^(−β), 0 < β < (1−α)/2, gives the same
      law for the other count (cont. 33/34). State it for a family of finite cutoffs indexed by L.
- [x] E7. Continuation 29 identification budget in coordinates:
      |N_B − N_A| ≤ ‖P_B − J P_A J*‖₁ + |Tr P_A(I − J*J)|, with the note that the signed trace
      can cancel; use the diagonal form Σ_{a_i ≤ L} (1 − ‖J e_i‖²) instead.
- [x] E8. `SteklovAudit/PowerShiftTransfer.lean`: the shift δ(L) = L^(−β) in E6. With
      ‖K P‖²_HS ≤ C L^α (named input `hH`), β > 0 and α + 2β < 1, the HS term δ⁻²‖K P‖² is
      ≤ C L^(α+2β) = o(L), so `sharp_law_transfer_power` gives the sharp law for N_B.
- [x] E8. `SteklovAudit/RpowScale.lean`: E6 at the concrete scale δ = L^(−β): if 0 ≤ ‖K P‖²_HS ≤ C L^α,
      α ≥ 0, β > 0, α + 2β < 1, then δ⁻²‖K P‖²_HS = o(L), and `sharp_law_transfer_rpow` gives the
      sharp law for the other count.
- [x] E9. Smoothing half of continuation 35: the smoothed count of `FloorCounterexample.Nc` at one
      fixed width has the sharp law 10L² + o(L); with `not_sharp` this shows one fixed width cannot
      give the sharp law (E2 needs widths → 0). Written in `SteklovAudit/FixedWidthSmoothing.lean`
      (two-point kernel ±1/4 at width 1; `smoothed_sharp_law`, `fixed_width_insufficient`).
- [x] E10. Trace-norm form of E7: |Tr X| ≤ Σ_i |X i i| ≤ ‖X‖₁ in coordinates, giving
      |N_B − N_A| ≤ ‖P_B − J P_A Jᵀ‖₁ + Σ_{a_i ≤ L} |1 − ‖J e_i‖²|. Written in
      `SteklovAudit/TraceNormBudget.lean` (`identification_budget_traceNorm`, `identification_budget_diag`);
      ‖X‖₁ enters through the named dual hypothesis `hdual` (|Tr(D X)| ≤ t for diagonal contractions D),
      since the trace norm and its duality are not formalized.
- [x] E11. `SteklovAudit/FixedWidthCounterexample.lean`: E5 for every `B` (`not_sharp_law`: `N` is not
      10L² + BL + o(L) for any `B`, since `N − 10L²` is about `+L` at `k + 1/4` and `−L` at `k + 3/4`),
      and `N` monotone on [1, ∞) (`F_strictMonoOn`, `N_monotoneOn`). Note: at `k + 1/4`,
      `N − 10x² = k − 5/8`, so E5's "≥ k" holds only as "≥ k − 1". Compiled on `claude/roadmap-e`.
- [x] E12. `SteklovAudit/AsymptoticTransfer.lean`: E6/E8 with the lower inequality in the raw form
      `counting_two_sided` gives (threshold `L − δ`, error terms evaluated at `L − δ`), δ = L^(−β);
      `law_of_shifted_bounds`, `asymptotic_transfer`. Compiled on `claude/roadmap-e`.
- [x] E13. `SteklovAudit/IdentificationBudgetData.lean`: E7 for `AbstractTransfer.Data`
      (`budget_identity`, `budget_bound`, `defect_terms_nonneg`) and an explicit cancellation example
      (`signed_trace_cancels`: signed defect 0, absolute defect 2). Compiled on `claude/roadmap-e`.

## H. The hypothesis ledger (reference only: no items here)

`SteklovAudit/MainConditional.lean` proves Theorem 11.1 / (11.4) from the six named hypotheses below
(`Thm111Inputs`; STATUS.md counts them as `named_hypotheses`). This section has no checkboxes and the :07 task
does not work on it directly. Work that weakens or restates an `[H…]` goes in section C or D; the "Lean so
far" column records what those items did. None of H1–H6 is proved for the Steklov operator of the
tetrahedron, so the main theorem stays conditional. Gaps (7.2), (7.29), (7.38)/(7.45) and (9.1) are open.

| H | Paper | Says | Lean so far | Still open | Related paper proofs |
|---|---|---|---|---|---|
| H1 splitting | §11.2 | `N = V + E + F`: trace linearity of the squared partition | C5: Tr P = Σ_k Tr(χ_k P χ_k) when Σ χ_k² = 1, in finite dimensions; H1 derived from a partition structure | A squared partition for the actual spectral projector | R01.1, R02.1, R13.1, R14.1, R15.1 |
| H2 area | §11.2 | The area coefficients add to √3 a²/(4π) | C5: additivity of the area coefficients | The area terms for the actual operator | R01.1 |
| H3 length | §11.2 (vertex cutoffs) | Edge length kept by the vertex cutoffs is 6a + O(ε) | C6: from the cutoff support lengths (interval arithmetic) | The cutoffs themselves | — |
| H4 vertex | (7.49) | Vertex part, error O(εL) + o(L) | D5: the (7.49) form C_V εL + K(log L + 1) implies H4 (a restatement; the count is unchanged) | (7.49) itself | — |
| H5 edge | (11.3) | Edge part, error C_ε γ L + o(L) | C4: from the model edge law (7.38)/(7.45) and a cumulative comparison o(L) (B4/B5, with a named tail hypothesis); A: Lemma 7.1′ replaces (7.2); E1/E6/E8: counting transfer at shift δ = L^(−β) when ‖K P‖²_HS = O(L^α), α < 1 | (7.2) for the DtN operator (replaced by 7.1′, whose PDE inputs are not proved), (7.29), (7.38)/(7.45), (9.1) | R16.2, R20.2, R25.1, R27.1, R29.1, R30.1, R32.1, R32.2, R33.1, R33.2, R37.1, R39.1 |
| H6 face | Lemma 7.4, §10.2 | Face part: zero linear coefficient, error o(L) | Nothing beyond the ledger | Lemma 7.4 and §10.2 | R26.1, R26.2 |

## R. Paper proofs from the hourly runs that are not yet in Lean

`docs/paper-proofs/` records 57 results (R01.1–R43.2) proved on paper in the hourly run reports: 20
formalized, 2 partly, 30 scalar fragments only, 5 not formalized. The items below are the parts that are
not formalized and can be stated in finite spectral coordinates. Each is a new file in `SteklovAudit/`
importing Mathlib (and `SteklovAudit.AbstractTransfer` where it reuses `Data`, `hs2`). Like sections D and
E, none of them proves any `[H…]` or the main theorem. R04.4 (Duhamel for unbounded generators) is not
listed: its finite-dimensional analogue is `AbstractTransfer.duhamel_hs` (B2), and the unbounded version
belongs under "Not attempted here". The smoothing half of R35.1 is E9. Lifting the 30 scalar-fragment
results to the operator level is not queued; pick from the index in `docs/paper-proofs/README.md` when R1–R5
are done.

- [x] R1. R43.2(ii), `SteklovAudit/HSNoTrace.lean`: on `Fin n` (n ≥ 1), `T = n⁻¹ I` has `hs2 T = 1/n` and
      `Tr T = 1`, so the HS norm tends to 0 while the trace does not; and `T` attains equality in
      |Tr T| ≤ √rank · ‖T‖_HS (compare `trace_rank_amplification`).
- [x] R2. R42.1(ii)–(iii), `SteklovAudit/LeakageLayerCake.lean`: (ii) for s > 0,
      Σ_{a_i ≤ L} Σ_{b_j ≥ L+s} J_ji² ≤ s⁻² Σ_{a_i ≤ L} Σ_j K_ji² (from `window_gap_leakage` plus the
      sub-sum step); (iii) the layer cake ∫₀^∞ 2t · 1[x > t] dt = max(x, 0)² for real x, summed to
      ∫₀^∞ 2t H(t) dt = Σ (b_j − L)₊² J_ji² with H(t) = Σ_{a_i ≤ L} Σ_{b_j > L+t} J_ji².
- [x] R3. R27.2 in coordinates, `SteklovAudit/PropagatorTrace.lean`: for a rank-r coordinate projection P,
      |Tr(P U(t) P)| ≤ √r · |t| · ‖K‖_HS with U(t) entrywise (e^{itb_j} − e^{ita_i}) J_ji; combine
      `trace_rank_amplification` with `duhamel_hs`.
- [x] R4. R21.2 in coordinates, `SteklovAudit/MultiChartTrace.lean`: charts J_i with Σ J_iᵀ J_i = I give
      |Tr e^{itA} − Σ_i Tr(J_iᵀ e^{itB_i} J_i)| ≤ √dim · |t| · (Σ_i ‖K_i‖²_HS)^{1/2}; sharpness example
      A = 0, B = I, J = I on ℂⁿ (discrepancy n|1 − e^{it}|).
- [-] R5. (Deferred 2026-11-05 in favour of section F.) R20.1, discrete kernel first, `SteklovAudit/WindowMassSmoothing.lean`: if N is nondecreasing,
      N = 0 on (−∞, 0) and N(k+1) − N(k) ≤ A(V(k+1) + 1) for integers k ≥ 0 (V ≥ 0), then for a finite kernel
      ρ = Σ_m w_m δ_{s_m} with Σ w_m = 1 and L ≥ 1,
      |N(L) − Σ_m w_m N(L − s_m)| ≤ A (V(L+1) + 1) · Σ_m |w_m| (|s_m| + 3)².
      The Schwartz-kernel version is optional.

## S. Paper statements outside the ledger (interactive session, 2026-11-04)

Elementary steps of the paper that are not part of `Thm111Inputs`. All four compiled in CI (STATUS PASS 421/421,
2026-11-04 19:18 UTC; 50 theorems). None proves any `[H…]`.

- [x] S1. `SteklovAudit/SectorTrace.lean` (§3.1–3.2): endpoint matrix (3.2) → multipliers (3.6)
      (`endpoint_eigen_plus/minus`); gamma step of (3.4), `π Γ(1/2−iv)Γ(1/2+iv)/4 = π²/(4 cosh πv)`;
      rank-one weight in (3.8); parity signs; the (3.8) and (3.9) integrands; `dihedralCoeff` in the
      coth form of (3.9); the integrand tends to (π−α)/α at 0. Not proved: (3.4) for `K_{iv}`, trace class.
- [x] S2. `SteklovAudit/EdgeMomentum.lean` (§3.3): (3.13) from the spectral-shift formula (3.10) taken as a
      hypothesis for each momentum: `∫₀^∞ dk ∫₀^∞ ∂_b φ(k/b) ξ(b) db = (∫ξ)(∫φ)` (Fubini with the
      integrability of (3.12), substitution, integration by parts), `formula_3_13`.
- [x] S3. `SteklovAudit/RieszMeans.lean` (§8, (1.9)): (8.4) for a finite nonnegative spectrum; for monotone
      `N` with the sharp law, every Riesz mean of order r > 0 obeys (1.9); `riesz_of_inputs` gives (1.9) with
      the paper's constants from the ledger; at r = 1 the coefficients are √3a²/(12π) and 3ac.
- [x] S4. `SteklovAudit/DihedralThird.lean`: `c_{π/3} = 2√3/(3π)` (closed form via an arctan
      antiderivative), hence with C10/C11 `1/(2π) ≤ c_{α₀} ≤ 2√3/(3π)` and `0.158 < c_{α₀} < 0.368`
      (improves C11's 24/π²). The decimals of (1.5) are still not certified.
- [x] S5. `SteklovAudit/HeatFiber.lean` (§4): Lemma 4.1's convolution is exactly `C C' B(q,q) u^(2q−1) e^{−cu}`
      (Beta scaling; `B(q,q)` convergent for 0 < q ≤ 1); (4.5) ⇒ the trace norm is integrable in `u` with
      `∫ ≤ K c^{−2q} Γ(2q)`, so `M_α < ∞`; (4.7) scaling `(1/2π)∫ f(t|k|) dk = M_α/t`; (4.9) ⇒ edge term of
      (4.10) by dominated convergence; (4.11) integral `∫₀^∞ dv/(1 + k cosh v) ≤ 2 log(2/k)`.
- [x] S6. `SteklovAudit/WindowBounds.lean` (§5): (5.2) strip-trace increment `≤ 2Cγ(L₂² − L₁²)`; (5.9)
      `∫_{L/2}^{2L} t/((t−L)² + w²) ≤ 2πL/w`; `‖S_o‖ ≤ 2/L`; (5.10) absorption `‖X‖ ≤ 4‖K‖/L` when `L > 4w`.
- [x] S7. `SteklovAudit/RieszCounterexample.lean` (§8, end): `N(L) = ⌊A L² + B L + ε L sin L⌋` (0 < ε < 2A,
      adjusted on a bounded interval) is monotone, obeys every positive Riesz law with coefficients `A, B`
      (`Nc_riesz`, via `|∫₀^L (L−u)^(r−1) u sin u| ≤ 2L + L^r + L/r`), and has no sharp law `A L² + B'L + o(L)`
      for any `B'` (`Nc_not_sharp`). With S3 (sharp ⇒ Riesz) this shows Riesz laws are strictly weaker.
      The heat expansion (8.1) for the example is not formalized.

## F. One analytic bottleneck: (7.29), the H5b comparison (from 2026-11-05)

Change of priority after the 2026-11-05 repository assessment. Sections A–E, R and S built a supporting
library (488 declarations compiled at 02:12 UTC), while the number of ledger inputs proved for the actual
Steklov operator stayed at 0 of 6. New auxiliary items are no longer queued. The target is one input:
H5b `compare` in `Thm111InputsC4` (`EdgeFromModel.lean`), the cumulative comparison (7.29): the true
edge-localized count differs from the model count by o(L). B4/B5 reduce it to named inputs; F turns that
reduction into one checked statement and keeps a status for each input in the table below.

A milestone is a table row moving to "proved on paper, reviewed", or a row replaced by a strictly weaker
input. A new abstract consequence is not a milestone.

- [x] F1. `SteklovAudit/H5Compare.lean`: `def H5bTarget` (exactly the type of `Thm111InputsC4.compare`
      for given `E Emod`), a structure `H5bInputs` with one named field per table row, and
      `h5b_of_inputs` proved by chaining `cumulative_transfer_bound` and `little_o_of_vanishing_tail`
      (`AbstractTransferB.lean`). If the chain needs anything not listed, add it as a separate named
      field and a new table row; never fold it into another field.
- [x] F2. Same file: `H5bInputs` is satisfiable (explicit witness), and no field is the target in
      disguise (no field states a bound on `E − Emod` at scale L). Then `Thm111InputsF` =
      `Thm111InputsC4` with `compare` replaced by `H5bInputs`, and `theorem_11_1_of_F`.
- [x] F3. `axiom_audit.py` / STATUS.md: report "library declarations checked" and "ledger inputs proved
      for the actual operator" (0 of 6 today) as separate numbers, and record the last passing commit
      SHA next to the current build result. Test on a branch before main.
      Written 2026-11-05 07:20 UTC on branch `claude/f3-audit` (commit 9731a41; only `axiom_audit.py`
      changed). Next run: if `verification/STATUS.md` on that branch is PASS and shows the commit,
      last passing commit, "Library declarations checked" and "Ledger inputs proved for the actual
      operator: 0 of 6" lines, copy `axiom_audit.py` from the branch to main unchanged and tick F3.
      Note: STATUS.json now contains the commit SHA, so CI commits a status update on every push.
      Ticked 2026-11-05 08:1x UTC: branch STATUS PASS 494/494 at 9731a41 with all four lines;
      `axiom_audit.py` copied to main unchanged (main's copy equalled the branch parent's).

When F1–F3 are ticked, the formalize task does not go idle (changed 2026-11-05): once no unchecked item is left
anywhere, it writes new items in section G aimed at the table below.

| Input (field of `H5bInputs`) | Paper | Lean shape taken from | Status |
|---|---|---|---|
| Localized spectral mass at each cutoff | (2.2) | `PDEInputs.mass` | not recorded (Josiah to fill) |
| Uniform localized HS defect bound | Lemma 7.1′ (replaces (7.2)) | `PDEInputs.defect` | written proof in the Claude Doc; concrete inequalities checked (section A); PDE inputs unproved; not reviewed |
| High-energy defect tail τ(M), σ(M) → 0 | (7.29) proof | B4/B5 tail hypothesis | open |
| Low-energy defect bound κ | (7.29) proof | B4 low-energy hypothesis | open |
| Lipschitz-type bounds Λ, λ for the smoothed counting function | §7 | B3/B4 | not recorded (Josiah to fill) |
| Finite cutoff → continuous model spectrum | §7 | not formalized (B1 docstring) | open; to be stated as its own field in F1 |
| Propagation (9.1) | §9 | — | open; whether it enters H5b or only the model law H5a is to be confirmed |

## G. Next items toward the F table (from 2026-11-05)

Added by an interactive session on 2026-11-05. When no unchecked item is left, the formalize task appends new G
items (G2, G3, ...) aimed at the F table; it does not queue library results that move no row.

- [x] G1. `SteklovAudit/TwoParameterSmoothing.lean` (continuation 54; lifts R38.1 from scalar fragments):
      `error_budget` and `sharp_law_of_two_parameter_smoothing`: if (A) `|N L − S_δ L| ≤ CδL + C` for L ≥ 1
      with one C for all δ ≤ δ₀, (B) for each δ eventually `|S_δ L − (AL² + BL)| ≤ (ω(δ) + η)L` for every
      η > 0 with the same A, B, and (C) ω(δ) → 0 as δ ↓ 0, then `HasSharpRealLaw N A B`. Written and pushed
      to main uncompiled by the interactive session (the continuation had no compiler). Next run: if STATUS
      shows it compiled, tick it; if not, fixing it is the next item. It records the shape a smoothed-count
      route to the H5b row "Lipschitz-type bounds Λ, λ for the smoothed counting function" must take: the
      sharp-to-smoothed error must be Cδ·L with C uniform in δ, and the smoothed coefficients must not
      depend on δ. It does not prove (A), (B) or (C) for the tetrahedron.
      Ticked by the formalize task 2026-11-05: STATUS PASS 496/496 at 46331e9, both theorems verified.

G2–G5 written by the formalize task on 2026-11-05 (after G1 was ticked). Each serves the F table; none
claims a row is proved for the actual operator.

- [x] G2. `SteklovAudit/H5Split.lean`: split H5b into a statement free of `E, Emod` plus the cutoff row.
      `def TraceLittleO` (for the data `D`, test `F` of an `H5bInputs`: the trace sum
      `∑ i, ∑ j, (F a i − F b j) J i j ^ 2` is eventually `≤ η L` for every η > 0). Prove
      `trace_little_o_of_rows` from the fields `pde`, `tail`, `tailVanish`, `lowDefect`, `lipHi`, `lipLo`,
      `lamVanish` only (reuse the B4/B5 chain of `h5b_of_inputs`), and `h5b_of_cutoff_and_trace`
      (cutoff + discVanish + TraceLittleO ⇒ `H5bTarget`). Records that rows 2–5 yield a statement that
      never mentions `E − Emod`, so all of F2's "target in disguise" content sits in the cutoff row.
      Ticked by the formalize task 2026-11-05: STATUS PASS 500/500 at da456f0, all three theorems verified.
- [x] G3. `SteklovAudit/H5CutoffSmoothed.lean`: replace `cutoff` + `discVanish` by a strictly weaker
      two-parameter input, using G1. `structure CutoffRowδ`: for each δ ∈ (0, δ₀] a cutoff with test `F δ`
      and `|(E − Emod) − trace(F δ)| ≤ C δ L + C` (one `C` for all δ, L ≥ 1), and for each δ the trace is
      `≤ (ω δ + η) L` eventually, with ω δ → 0. Prove `target_of_cutoffRowδ` (via
      `sharp_law_of_two_parameter_smoothing`-style argument, or directly) and `cutoffRowδ_of_cutoff`
      (the F1 row implies the new one), so the new row is no stronger than the old one.
      Written by the formalize task 2026-11-05 (uncompiled at push): `CutoffRowδ`, `target_of_cutoffRowδ`,
      `cutoffRowδ_of_inputs` (a `def`), plus the F2-style audit `cutoffRowδ_iff_target`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-05: STATUS PASS 502/502 at 9fa2d81, `target_of_cutoffRowδ` and
      `cutoffRowδ_iff_target` verified.
- [x] G4. `SteklovAudit/H5TailAudit.lean`: the tail and low-energy rows are genuine inputs.
      `hs2_mask_split` (`hs2 K = hs2 (mask p K) + hs2 (mask (¬p) K)`, so `tail` and `lowDefect` together
      bound exactly the full defect), and `defect_not_imp_tail`: an explicit family of `Data` satisfying
      `PDEInputs` for every L but whose high-energy masked defect does not tend to 0 uniformly in L
      (so `tailVanish` does not follow from `PDEInputs.defect`; the row stays a separate input).
      Written by the formalize task 2026-11-05 (uncompiled at push, commit 5155c4e): `hs2_mask_split`,
      `defect_le_tail_add_low`, `counterData` (a = L+1, b = L, J = 1+L on Fin 1), `counterData_pde`,
      `counterData_hi_mask`, `defect_not_imp_tail`, `tail_row_fails`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-05: STATUS PASS 509/509 at 282d63b, all seven theorems verified.
- [x] G5. `SteklovAudit/H5LipRows.lean`: reduce the Lipschitz rows to derivative bounds.
      `lipHi_of_deriv_bound`: if `F` is differentiable with `‖deriv F x‖ ≤ Λ0` for all x, the `lipHi`
      inequality holds; `lipLo_of_deriv_bound_le`: if `‖deriv F x‖ ≤ lam` on `Set.Iic M`, the `lipLo`
      inequality holds for low-energy pairs (both energies ≤ M). Use
      `Convex.norm_image_sub_le_of_norm_deriv_le` (`convex_univ`, `convex_Iic`). This states the row
      "Lipschitz-type bounds Λ, λ" as a derivative bound on the smoothed counting function.
      Written by the formalize task 2026-11-05 (uncompiled at push): `abs_sub_le_of_deriv_bound`,
      `abs_sub_le_of_deriv_bound_Iic`, `lipHi_of_deriv_bound`, `le_of_not_hiE`, `lipLo_of_deriv_bound_le`,
      `hΛ0_of_deriv_bound`, `lipHi_field`, `lipLo_field`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-05: STATUS PASS 517/517 at 632bf9d, all eight theorems verified.

G6–G9 written by the formalize task on 2026-11-05 (after G5 was ticked). Each serves the F table; none
claims a row is proved for the actual operator.

- [x] G6. `SteklovAudit/H5WindowProfile.lean`: the Lipschitz rows for a test that is a fixed profile
      translated to the energy window, `F ε γ L x = φ (x - L)`. Hypotheses on `φ` only: differentiable,
      `|deriv φ t| ≤ Λ0` for all t, and a left-tail bound `∀ R t, t ≤ -R → |deriv φ t| ≤ ψ R` with
      `ψ R → 0` as `R → ∞`. Prove `lipHi_of_profile` (via G5's `lipHi_of_deriv_bound`) and
      `lipLo_of_profile`: for L ≥ M + R, low-energy pairs satisfy the `lipLo` inequality with constant
      `ψ R` (derivative of `x ↦ φ (x - L)` on `Set.Iic M` is bounded by `ψ R`; use
      `deriv_comp_sub_const` or `HasDerivAt.comp_sub_const`). Records the row "Λ, λ" as a property of
      one fixed profile, independent of the operator.
      Written by the formalize task 2026-11-05 (uncompiled at push, commit 3f352a5): `hasDerivAt_shift`,
      `deriv_shift`, `differentiable_shift`, `lipHi_of_profile`, `lipLo_of_profile`, `lipHi_field_profile`,
      `lipLo_field_profile`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-05: STATUS PASS 531/531 at 2a5797d, all seven theorems verified.
- [x] G7. Same file: `lamVanish_of_profile`: with `lam ε γ M L := ψ (L - M)` (clamped to be ≥ 0, e.g.
      `max (ψ (L - M)) 0` for L > M and `Λ0` otherwise), the fields `hlam`, `lipLo` and `lamVanish` of
      `H5bInputs` hold for the translated profile. Bundle as `structure ProfileLipRows` and
      `lipGroup_of_profile` returning the five fields `hΛ0`, `lipHi`, `hlam`, `lipLo`, `lamVanish`.
      This replaces the row "Lipschitz-type bounds Λ, λ" by "the window profile has bounded derivative
      with vanishing left tail" when the smoothed count has this translated form (to be checked on paper).
      Written by the formalize task 2026-11-05 (uncompiled at push): `profLam` (`max (ψ (L - M)) 0` if
      `M ≤ L`, else `Λ0`), `profLam_nonneg`, `lipLo_profLam`, `profLam_vanish`, `eventually_le_of_tendsto`,
      `ProfileLipRows`, `lipGroup_of_profile`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-05: STATUS PASS 536/536 at f568283, all five G7 declarations verified.
- [x] G8. Same file (or `SteklovAudit/H5WindowWitness.lean`): non-vacuity of G6/G7. `φ := Real.arctan`
      satisfies the profile hypotheses with `Λ0 = 1`, `ψ R = 1 / (1 + R ^ 2)` for R ≥ 0 (`Real.deriv_arctan`
      or `Real.hasDerivAt_arctan`), and `arctan_profile_nonjunk`: the resulting test is non-constant
      (`φ 1 - φ 0 ≠ 0`), so the row is not satisfied by a trivial test.
      Written by the formalize task 2026-11-05 in `SteklovAudit/H5WindowWitness.lean` (uncompiled at push):
      `arctan_hasDerivAt'`, `arctan_deriv_eq`, `arctan_differentiable'`, `arctan_deriv_le_one`, `arctanTail`
      (`1 / (1 + (max R 0) ^ 2)`, so `htail` holds for every R), `arctan_tail`, `arctanTail_small`,
      `arctanProfile : ProfileLipRows`, `arctan_lipGroup`, `arctan_profile_nonjunk`, `arctan_shift_nonconst`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-06: STATUS PASS 545/545 at ca90967, all G8 declarations verified.
- [x] G9. `SteklovAudit/H5TailRate.lean`: reduce `tailVanish` to a decay rate. `tailVanish_of_power`: if
      `τ ε γ M ≤ C ε γ / M` for all M ≥ 1 (C ≥ 0), then the
      `tailVanish` field holds; and `tail_rate_not_target`: this hypothesis mentions neither `E` nor
      `Emod` (state it as a `Prop` on `τ` alone, so the F2 disguise audit applies by construction).
      Records the shape a paper bound for the high-energy tail row must take.
      Written by the formalize task 2026-11-06 (uncompiled at push): `TailRate` (a `Prop` on `τ`, `C` only),
      `div_le_of_rate`, `tailVanish_of_power`, `tailVanish_field`, `invRate`, `invRate_vanish`,
      `not_target_double`, `tail_rate_not_target` (rate satisfiable while `H5bTarget` fails for E = 2L,
      Emod = 0). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-06: STATUS PASS 552/552 at 053e020, all seven G9 theorems verified.

G10–G13 written by the formalize task on 2026-11-06 (after G9 was ticked). Each serves the F table; none
claims a row is proved for the actual operator.

- [x] G10. `SteklovAudit/H5LowMass.lean`: reduce the low-energy defect row κ to a low-energy mass bound on
      `J`. Low pairs have `max (a i) (b j) ≤ M`; with nonnegative energies (`0 ≤ a i`, `0 ≤ b j`, true for
      Steklov eigenvalues) this gives `|a i - b j| ≤ M`, hence `|K i j| ≤ M * |J i j|`. Prove
      `abs_sub_le_of_low` (`0 ≤ x`, `0 ≤ y`, `max x y ≤ M` ⇒ `|x - y| ≤ M`), `low_K_sq_le`, and
      `lowDefect_of_lowMass`: if `hs2 (mask (¬ hiE D M) J) ≤ m M` then
      `hs2 (mask (¬ hiE D M) D.K) ≤ M ^ 2 * m M`; plus `lowDefect_field` in the exact shape of
      `H5bInputs.lowDefect` with `κ2 ε γ M := M ^ 2 * m ε γ M`. Replaces the row "low-energy defect bound κ"
      by "the identification `J` has L-uniform mass on energies ≤ M" (a statement on `J`, not on `K`).
      Written by the formalize task 2026-11-11 (uncompiled at push, commit c63ec0f): `abs_sub_le_of_low`,
      `low_K_sq_le`, `low_mask_K_sq_le`, `hs2_low_K_le`, `lowDefect_of_lowMass`, `lowDefect_field`. Next run:
      tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-11: STATUS PASS 558/558 at 3eabe21, all six G10 theorems verified.
- [x] G11. Same file: the low-mass input is a genuine input and is not the target in disguise.
      `lowMass_not_of_pde`: an explicit family (`Fin 1`, a = b = 0, J = 1 + L) satisfies `PDEInputs` for
      every L (Cm = 1, Ck = 0) but `hs2 (mask (¬ hiE D 1) J)` is unbounded in L, so the low-mass row does not
      follow from `PDEInputs.mass`; and `lowMass_satisfiable` (J = 0 witness, m = 0). The hypothesis is a
      `Prop` on `D` and `m` only and mentions neither `E` nor `Emod`.
      Written by the formalize task 2026-11-11 (uncompiled at push, commit d0660b5): `LowMass`,
      `lowDefect_of_LowMass`, `hs2_one`, `lowCounter`, `lowCounter_nonneg`, `lowCounter_pde`,
      `lowCounter_low_mass`, `lowMass_not_of_pde`, `lowMass_row_fails`, `lowMass_of_J_zero`, `zeroData`,
      `lowMass_satisfiable`, `lowMass_not_target` (reuses G9's `not_target_double`; the file now imports
      `SteklovAudit.H5TailRate`). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-11: STATUS PASS 574/574 at 0d76599, all G11 theorems verified.
- [x] G12. `SteklovAudit/H5MassRow.lean`: reduce the mass row (2.2) to a Bessel bound plus a Weyl count.
      `mass_of_bessel_count`: if `∀ i, ∑ j, J i j ^ 2 ≤ 1` and `(Fintype.card ι : ℝ) ≤ Cw * (1 + L) ^ 2`, then
      `hs2 J ≤ Cw * (1 + L) ^ 2` (`Finset.sum_le_sum`, `Finset.sum_const`, `Finset.card_univ`);
      `pde_of_bessel_count`: the same with a defect bound gives `PDEInputs D L Cw Ck`; and
      `bessel_count_nonjunk`: a witness on `Fin 2` with `J` the identity matrix. Records the row
      "localized spectral mass" as (rows of `J` have norm ≤ 1) + (eigenvalue count below the cutoff is
      O(L²)); neither is proved for the tetrahedron.
      Ticked by the formalize task 2026-11-11: STATUS PASS 574/574 at 0d76599, `sum_one_eq_card`,
      `mass_of_bessel_count`, `pde_of_bessel_count`, `idJ_row`, `idJ_hs2`, `bessel_count_nonjunk` verified.
- [ ] G13. `SteklovAudit/H5WeakRows.lean`: assemble G9 + G10. `structure H5bWeakInputs` = `H5bInputs` with
      `tailVanish` replaced by `TailRate τ Cτ` (G9) and `κ2`, `lowDefect` replaced by a low-mass bound
      `m` on `J` plus nonnegative energies (G10). Prove `H5bWeakInputs.toInputs : H5bInputs E Emod` (a `def`)
      and `h5b_of_weak : H5bTarget E Emod` via `h5b_of_inputs`. Records the F table with two rows replaced
      by the weaker named inputs; the `cutoff` row and `pde` are unchanged.
      Written by the formalize task 2026-11-11 (uncompiled at push, commit 65b3c7f): `H5bWeakInputs`
      (fields `Cτ`, `tailRate`, `ha`, `hb`, `m`, `lowMass` replace `tailVanish`, `κ2`, `lowDefect`),
      `H5bWeakInputs.toInputs`, `toInputs_κ2`, `toInputs_disc`, `h5b_of_weak`. Next run: tick if STATUS
      shows it compiled.

## Not attempted here

Constructing the Dirichlet-to-Neumann operator, Sobolev traces on Lipschitz domains, and the
PDE estimates (2.2), (5.5), (7.1), (7.15), propagation (9.1). These stay named hypotheses.
