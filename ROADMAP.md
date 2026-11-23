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
- [x] S8. `SteklovAudit/WedgeChannel.lean` (continuation 176, 2026-11-10; added by the interactive session
      2026-11-15, uncompiled at push): scalar part of the two-channel wedge bounds. `channel_sum`,
      `channel_difference`; `sinh_le_mul_cosh`, `mul_cosh_le`; 176.2 `tanh_le_id`, `div_one_add_le_tanh`,
      `inv_le_coth`, `coth_le_one_add_inv`; multiplier form `m_mul_inv`, `sym_lower`, `sym_upper`, `anti_lower`,
      `anti_upper`, `channel_lower`; 176.3 scalar step `antisym_physical`. The eigenvalue step of 176.1 is S1's
      `endpoint_eigen_minus/plus`. Not proved: the variational Theorem 176.1, anything about `t`-integrals, the
      `m = 0` extensions. Moves no `[H…]` input and no F row. Record: `docs/paper-proofs/continuation-176.md`.
      Ticked by the interactive session 2026-11-15: STATUS PASS 846/846 at 47cc6aa (after fixing
      `Set.left_mem_Ici`), all 15 `WedgeChannel` theorems verified.

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
- [x] G13. `SteklovAudit/H5WeakRows.lean`: assemble G9 + G10. `structure H5bWeakInputs` = `H5bInputs` with
      `tailVanish` replaced by `TailRate τ Cτ` (G9) and `κ2`, `lowDefect` replaced by a low-mass bound
      `m` on `J` plus nonnegative energies (G10). Prove `H5bWeakInputs.toInputs : H5bInputs E Emod` (a `def`)
      and `h5b_of_weak : H5bTarget E Emod` via `h5b_of_inputs`. Records the F table with two rows replaced
      by the weaker named inputs; the `cutoff` row and `pde` are unchanged.
      Written by the formalize task 2026-11-11 (uncompiled at push, commit 65b3c7f): `H5bWeakInputs`
      (fields `Cτ`, `tailRate`, `ha`, `hb`, `m`, `lowMass` replace `tailVanish`, `κ2`, `lowDefect`),
      `H5bWeakInputs.toInputs`, `toInputs_κ2`, `toInputs_disc`, `h5b_of_weak`. Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-11: STATUS PASS 577/577 at 43d1b00, `toInputs_κ2`,
      `toInputs_disc`, `h5b_of_weak` verified.

G14–G17 written by the formalize task on 2026-11-11 (after G13 was ticked). Each serves the F table; none
claims a row is proved for the actual operator.

- [x] G14. `SteklovAudit/H5WeakAudit.lean`: F2-style audit of `H5bWeakInputs` (G13). `weakWitness`: an explicit
      `H5bWeakInputs E Emod` for E = Emod = 0 on `Fin 1` data with a = b = 0 and J = K = 0 (reuse G11's
      `zeroData` / `lowMass_satisfiable`, G9's `invRate`, G8's `arctanProfile` or constant F = 0 with
      Λ0 = 0, lam = 0), so the structure is not vacuous; `weak_rows_not_target`: the new rows `tailRate` and
      `lowMass` are satisfiable for E = 2L, Emod = 0 while `H5bTarget` fails (G9's `not_target_double`),
      so neither replacement row is the target in disguise. Theorem names: `weakWitness`,
      `weakWitness_nonempty`, `weak_rows_not_target`.
      Written by the formalize task 2026-11-11 (uncompiled at push, commit e58b396): `weak_hs2_zero`,
      `zeroData_J`, `zeroData_K`, `zeroData_pde`, `zeroData_tail`, `zeroRate`, `weakWitness` (any `E = Emod`),
      `weakWitness_nonempty`, `weak_rows_not_target`, plus `weakOfTarget` and `weak_iff_target`
      (`Nonempty (H5bWeakInputs E Emod) ↔ H5bTarget E Emod`: as in F2, the disguise sits in the cutoff row).
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-12: STATUS PASS 586/586 at cf32b08, all nine G14 theorems verified.
- [x] G15. `SteklovAudit/H5LowCount.lean`: reduce the low-mass row (G10/G11) to a Bessel bound plus an
      L-uniform low-energy count. Low pairs satisfy `a i ≤ M` (from `¬ hiE`, as in G5's `le_of_not_hiE`), so
      `hs2 (mask (¬ hiE D M) J) ≤ ∑ i with a i ≤ M, ∑ j, J i j ^ 2`. Prove `low_mask_le_rows`, and
      `lowMass_of_bessel_lowCount`: if `∀ i, ∑ j, J i j ^ 2 ≤ 1` and
      `((Finset.univ.filter fun i => a i ≤ M).card : ℝ) ≤ c ε γ M` for every L, then `LowMass D c`.
      Replaces the row "low-energy defect bound κ" by "eigenvalues ≤ M are L-uniformly finitely many"
      (true for a discrete spectrum, not proved here) plus the same Bessel bound as G12.
      Written by the formalize task 2026-11-12 (uncompiled at push, commit 30b11d1): `not_hiE_le`,
      `mask_sq_le_row`, `low_mask_le_rows`, `rows_le_card`, `lowMass_of_bessel_lowCount`,
      `lowDefect_of_bessel_lowCount`, `idData`, `card_filter_le_two`, `lowCount_nonjunk` (identity coupling
      on `Fin 2`, total mass 2). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-12: STATUS PASS 594/594 (run on 0ddfe89), all eight G15 theorems verified.
- [x] G16. `SteklovAudit/H5PaperRows.lean`: assemble G12 + G13 + G15 + G7. `structure H5bPaperInputs` =
      `H5bWeakInputs` with `pde` replaced by `bessel`, Weyl `count` (G12) and the `defect` field of
      `PDEInputs` copied verbatim; `lowMass` replaced by the low count of G15 (same `bessel`); and the
      Lipschitz group replaced by `F ε γ L x = φ (x - L)` with `ProfileLipRows` (G7). Prove
      `H5bPaperInputs.toWeak : H5bWeakInputs E Emod` (a `def`) and `h5b_of_paper : H5bTarget E Emod` via
      `h5b_of_weak`. Records the F table rows as: cutoff, Lemma 7.1′ defect, Bessel, Weyl count, tail rate,
      low count, window profile.
      Written by the formalize task 2026-11-12 (uncompiled at push): `H5bPaperInputs` (fields `P`, `bessel`,
      `count`, `defect`, `c`, `lowCount` replace `F`, `pde`, `m`, `lowMass` and the Lipschitz group),
      `H5bPaperInputs.toWeak`, `toWeak_F`, `toWeak_m`, `toWeak_disc`, `h5b_of_paper`. Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-12: STATUS PASS 598/598 at 8eade62, `toWeak_F`, `toWeak_m`,
      `toWeak_disc`, `h5b_of_paper` verified.
- [x] G17. Same file (or `SteklovAudit/H5PaperAudit.lean`): audit of G16. `paperWitness` (non-vacuity, Fin 1
      data with J = 0, φ = arctan from G8), and `paper_rows_not_target`: every field of `H5bPaperInputs` other
      than `cutoff`/`discVanish` is satisfiable for E = 2L, Emod = 0 while `H5bTarget` fails, so all of the
      "target in disguise" content stays in the cutoff row (G2, G3). Theorem names: `paperWitness`,
      `paper_rows_not_target`.
      Written by the formalize task 2026-11-12 in `SteklovAudit/H5PaperAudit.lean` (uncompiled at push, commit
      59fd59e): `wN`, `wN_le_one`, `wData`, `wData_K`, `wData_sum`, `wData_bessel`, `wData_count`, `wData_defect`,
      `wData_tail`, `wData_lowCount`, `w_cutoff`, `paperOfCutoff` (all non-cutoff rows from one family
      independent of `E`, `Emod`), `paperWitness`, `paperWitness_nonempty`, `paperWitness_nonjunk`,
      `paper_rows_not_target` (no `disc` meets cutoff + `discVanish` for E = 2L, Emod = 0), `paper_iff_target`.
      Note: the `count` row holds for all real L, so at L = -1 it forces nA = 0; the witness uses nA = 0 for
      L < 0. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-12: STATUS PASS 611/611 at ef4e80f, all thirteen listed G17
      theorems verified (incl. `paper_rows_not_target`, `paper_iff_target`).

G18–G21 written by the formalize task on 2026-11-12 (after G17 was ticked). They split the cutoff row, the
one row that carries the "target in disguise" content (G2, G3, G14, G17), into a true-operator side and a
model side, each mentioning only one spectrum. None claims a row is proved for the actual operator.

- [x] G18. `SteklovAudit/H5CutoffSides.lean`: the reduction step. With row masses `r i = ∑ j, J i j ^ 2`
      and column masses `c j = ∑ i, J i j ^ 2`, prove `double_sum_split`:
      `∑ i, ∑ j, (f (a i) - g (b j)) * J i j ^ 2 = ∑ i, f (a i) * r i - ∑ j, g (b j) * c j`
      (Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_comm), and `cutoff_of_sides`: if
      `|E - ∑ i, φ (a i - L) * r i| ≤ d1` and `|Emod - ∑ j, φ (b j - L) * c j| ≤ d2` then the G16 cutoff
      inequality holds with `disc = d1 + d2` (abs_sub_le / abs_add). Also `discVanish_of_sides`: if d1 and d2
      are each eventually `≤ η L` for every η > 0, so is d1 + d2. Theorem names: `double_sum_split`,
      `cutoff_of_sides`, `discVanish_of_sides`.
      Written by the formalize task 2026-11-12 in `SteklovAudit/H5CutoffSides.lean` (uncompiled at push, commit
      df5c73c): `double_sum_split`, `cutoff_of_sides`, `discVanish_of_sides`, stated over arbitrary finite index
      types (so they apply verbatim to `Data (Fin nA) (Fin nB)`). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 614/614 at ea72791, all three G18 theorems verified.
- [x] G19. Same file (or `SteklovAudit/H5SideRows.lean`): `structure H5bSideInputs` = `H5bPaperInputs` with
      `disc`, `cutoff`, `discVanish` replaced by `d1`, `trueSide`, `d1Vanish` (true count vs. the
      J-row-weighted localized trace of the true eigenvalues `a`) and `d2`, `modelSide`, `d2Vanish` (model
      count vs. the column-weighted trace of the model eigenvalues `b`). Prove `H5bSideInputs.toPaper` (a
      `def`, via G18), `toPaper_disc` (`= d1 + d2`, by rfl) and `h5b_of_sides : H5bTarget E Emod` via
      `h5b_of_paper`. F table: the cutoff row becomes two rows, "true side" and "model side".
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5SideRows.lean` (uncompiled at push, commit
      ae865e1): `H5bSideInputs`, `H5bSideInputs.toPaper`, `toPaper_disc`, `toPaper_P`, `h5b_of_sides`. Next run:
      tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 617/617 at d4d55cb, `toPaper_disc`, `toPaper_P`,
      `h5b_of_sides` verified.
- [x] G20. `SteklovAudit/H5SideAudit.lean`: audit of G19. `sideWitness`: an explicit `H5bSideInputs 0 0`
      (reuse G17's `paperOfCutoff` data: J = 0 so all traces vanish, d1 = d2 = 0), `sideWitness_nonempty`;
      and `model_side_not_target`, `true_side_not_target`: each side row (with its vanishing field and all
      non-cutoff rows) is satisfiable for a pair (E, Emod) for which `H5bTarget` fails (E = 2L with only the
      model side imposed; Emod = 2L with only the true side imposed; reuse G9's `not_target_double` or prove
      the mirrored version), so neither side alone is the target in disguise.
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5SideAudit.lean` (uncompiled at push):
      `wData_rowTrace`, `wData_colTrace`, `w_trueSide`, `w_modelSide`, `sideOfBounds` (all non-side rows from
      G17's family, side rows reduce to `|E| ≤ d1`, `|Emod| ≤ d2`), `zeroDisc_vanish`, `zero_bound`,
      `sideWitness`, `sideWitness_nonempty`, `not_target_mirror`, `model_side_not_target`,
      `true_side_not_target` (each also shows no vanishing discrepancy fits the other side). Next run: tick
      if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 627/627 at d3358a5, all ten listed G20 theorems
      verified.
- [x] G21. Same file as G20: the refinement is genuine and honest about direction. `sides_imply_cutoff`
      (restating G18 at the structure level: every `H5bSideInputs` yields `H5bPaperInputs` with the same
      non-cutoff fields), and `cutoff_not_sides`: an explicit Fin 1 example (J i j = 1, a = b, E = Emod = 2L, φ = arctan from G8, so the weighted trace is bounded by π/2)
      where the G16 cutoff row holds with disc = 0 but the true-side row fails for every vanishing d1, so
      G19 is a strictly stronger, two-row form of the cutoff row, not a weaker one. Record that in the F table
      text of G19 (the side rows are what the paper's §7 localization argues, one spectrum at a time).
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5SideAudit.lean` (uncompiled at push, commit
      1e87cc2): `sides_imply_cutoff`, `arctan_abs_le_two`, `fin1_cutoff`, `fin1_rowTrace`,
      `fin1_trueSide_fails`, `cutoff_not_sides` (eigenvalues a = b = 0 rather than a = b free; the bound
      used is |arctan| ≤ 2 via `Real.pi_le_four`). F table note for G19: the two side rows are strictly
      stronger than the cutoff row (they imply it, and `cutoff_not_sides` shows the converse fails); they
      are what the paper's §7 localization argues, one spectrum at a time. Next run: tick if STATUS shows
      it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 633/633 at 1fe8bce, all six G21 theorems verified.

G22–G25 written by the formalize task on 2026-11-13 (after G21 was ticked). They reduce each side row of G19
to a one-spectrum smoothed count with no `J`, plus a completeness row on `J` that mentions neither `E` nor
`Emod`. None claims a row is proved for the actual operator.

- [x] G22. `SteklovAudit/H5Completeness.lean`: the reduction step, over an arbitrary `Fintype ι` with values
      `f : ι → ℝ` and weights `w : ι → ℝ` (so it applies to rows `w i = ∑ j, J i j ^ 2` and to columns).
      `weighted_sum_split`: `∑ i, f i * w i = ∑ i, f i - ∑ i, f i * (1 - w i)` (Finset.sum_sub_distrib, ring);
      `side_of_count_and_defect`: if `|E - ∑ i, f i| ≤ e`, `∑ i, |f i| * (1 - w i) ≤ k` and `∀ i, w i ≤ 1`,
      then `|E - ∑ i, f i * w i| ≤ e + k` (Finset.abs_sum_le_sum_abs, abs_mul); `defect_le_sup`: if
      `∀ i, |f i| ≤ Φ` and `∀ i, w i ≤ 1` then `∑ i, |f i| * (1 - w i) ≤ Φ * ∑ i, (1 - w i)`. Theorem names:
      `weighted_sum_split`, `side_of_count_and_defect`, `defect_le_sup`.
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5Completeness.lean` (uncompiled at push, commit
      799a5d8): `weighted_sum_split`, `defect_abs_le`, `side_of_count_and_defect`, `defect_le_sup`,
      `side_of_count_and_sup` (count + sup·missing-mass form), `side_of_count_and_defect_nonvacuous` (Fin 1,
      w = 1/2, bound attained). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 639/639 at 282272e, all six G22 theorems verified.
- [x] G23. `SteklovAudit/H5CountRows.lean`: `structure H5bCountInputs` = `H5bSideInputs` (G19) with
      `d1`, `trueSide`, `d1Vanish` replaced by a true count row `e1`, `trueCount`
      (`|E - ∑ i, P.φ (a i - L)| ≤ e1`, no `J`), `e1Vanish`, and a row-completeness row `k1`, `rowDefect`
      (`∑ i, |P.φ (a i - L)| * (1 - ∑ j, J i j ^ 2) ≤ k1`), `k1Vanish`; mirror for the model side (`e2`,
      `modelCount`, `e2Vanish`, `k2`, `colDefect`, `k2Vanish`) with a new column Bessel row
      `colBessel : ∀ ε γ L j, ∑ i, J i j ^ 2 ≤ 1`. Prove `H5bCountInputs.toSides : H5bSideInputs E Emod`
      (a `def`, `d1 = e1 + k1`, `d2 = e2 + k2`, via G22 and G18's `discVanish_of_sides`), `toSides_d1`,
      `toSides_d2` (rfl) and `h5b_of_counts : H5bTarget E Emod` via `h5b_of_sides`. F table: each side row
      becomes "smoothed count of one spectrum (no J)" + "completeness of J weighted by the window profile".
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5CountRows.lean` (uncompiled at push, commit
      bfde66f): `H5bCountInputs`, `H5bCountInputs.toSides`, `toSides_d1`, `toSides_d2`, `h5b_of_counts`. Next run:
      tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 642/642 at b3f2e53, `toSides_d1`, `toSides_d2`,
      `h5b_of_counts` verified.
- [x] G24. `SteklovAudit/H5CountAudit.lean`: audit of G23. `countWitness : H5bCountInputs 0 0` (data with
      `nA = nB = 0`, so every sum is empty and all `e`, `k` are 0; G8's `arctanProfile`),
      `countWitness_nonempty`; `true_count_not_target` and `model_count_not_target`: each count row (with its
      vanishing field) is satisfiable for a pair where `H5bTarget` fails (reuse G9's `not_target_double` and
      G20's `not_target_mirror`); `defect_rows_not_target`: the two completeness rows and `colBessel` are a
      `Prop` on `D`, `P`, `k1`, `k2` only (no `E`, `Emod`) and hold for the witness data while
      `H5bTarget` fails for E = 2L, Emod = 0.
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5CountAudit.lean` (uncompiled at push, commit
      1b664d0): `zData` (empty family, nA = nB = 0), `countOfBounds`, `countWitness`, `countWitness_nonempty`,
      `true_count_not_target` (E = 0, Emod = 2L, via `not_target_mirror`), `model_count_not_target`
      (E = 2L, Emod = 0), `defect_rows_not_target`, plus helper lemmas `z_*`. Next run: tick if STATUS shows
      it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 656/656 at 73469a7, all G24 theorems in
      `H5CountAudit.lean` verified.
- [x] G25. Same file as G24: the completeness row is not redundant. `trueCount_not_trueSide`: an explicit
      example with `nA L = Nat.ceil L` eigenvalues all equal to 0, `J = 0`, φ = arctan and
      `E L = Nat.ceil L * arctan (-L)`, so the true count row holds with e1 = 0 while the row-weighted trace is 0
      and the G19 true-side row fails for every vanishing `d1` (|arctan (-L)| ≥ arctan 1 = π/4 for L ≥ 1; use
      `Real.arctan_one`, `Real.arctan_strictMono` or `Real.arctan_lt_arctan`); and `rowDefect_of_sup`: with
      `∀ x, |P.φ x| ≤ Φ` (G21's `arctan_abs_le_two` for arctan) the row-completeness row follows from
      `Φ * ∑ i, (1 - ∑ j, J i j ^ 2) ≤ k1` (G22's `defect_le_sup` with G12's Bessel row), recording the crude
      form of the row: the total missing row mass below the cutoff is o(L).
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5CountAudit.lean` (uncompiled at push, commit
      30898f1): `const_sum_fin`, `ceil_trueCount`, `ceil_rowTrace`, `ceil_trueSide_fails`,
      `trueCount_not_trueSide` (eigenvalues at 0 written as a constant function; E L = ⌈L⌉₊ * arctan (0 - L);
      vanishing rate tested with η = 1/2 and π > 3), `rowDefect_of_sup` (any bounded φ, over arbitrary
      Fintypes), `rowDefect_arctan` (Φ = 2). F table: the row-completeness row is not redundant; its crude
      form is `Φ * (total missing row mass) ≤ k1`, so it needs the missing row mass below the cutoff to be
      o(L). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 663/663 at e2829a3, all seven G25 theorems verified.

G26–G29 written by the formalize task on 2026-11-13 (after G25 was ticked). They replace the two
profile-weighted completeness rows of G23 by profile-free missing-mass rows, record honestly that this is a
stronger form, and then split the row side into the existing L-uniform low count plus a high-energy
missing-mass row. None claims a row is proved for the actual operator.

- [x] G26. `SteklovAudit/H5MissingMass.lean`: `structure H5bMassInputs` = `H5bCountInputs` (G23) with
      `k1`, `rowDefect`, `k1Vanish` replaced by a profile bound `Φ : ℝ`, `hΦ : 0 ≤ Φ`,
      `profBound : ∀ x, |P.φ x| ≤ Φ` and a row missing-mass row `m1`, `rowMiss`
      (`∑ i, (1 - ∑ j, J i j ^ 2) ≤ m1`), `m1Vanish`; mirror `m2`, `colMiss`, `m2Vanish` for columns.
      Prove `vanish_const_mul` (if `m` is o(L) in the `e1Vanish` sense and `0 ≤ Φ` then so is `Φ * m`; treat
      `Φ = 0` and `0 < Φ` separately, use `η / Φ`), `H5bMassInputs.toCounts : H5bCountInputs E Emod` (a `def`,
      `k1 = Φ * m1`, `k2 = Φ * m2`, rows via G25's `rowDefect_of_sup` and its column mirror), `toCounts_k1`
      (rfl) and `h5b_of_mass : H5bTarget E Emod` via `h5b_of_counts`.
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5MissingMass.lean` (uncompiled at push, commit
      29c5da9): `vanish_const_mul`, `H5bMassInputs`, `H5bMassInputs.toCounts` (rows via G22's `defect_le_sup`
      directly, with `bessel`/`colBessel`), `toCounts_k1`, `toCounts_k2`, `h5b_of_mass`. Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 667/667 at 7246446 (build of 29c5da9 also passed;
      only its status push lost a race), all G26 theorems in `H5MissingMass.lean` verified.
- [x] G27. `SteklovAudit/H5MassAudit.lean`: audit of G26. `massWitness : H5bMassInputs 0 0` (G24's `zData`,
      `Φ = 2`, `m1 = m2 = 0`), `massWitness_nonempty`; `mass_stronger_than_defect`: a `Fin ⌈L⌉₊` example with
      all true eigenvalues at `L`, `J = 0`, φ = arctan, where the G23 row-completeness row holds with `k1 = 0`
      (`arctan 0 = 0`) while the missing row mass is `⌈L⌉₊`, so no vanishing `m1` meets `rowMiss`. F table
      text: the missing-mass row is a stronger, profile-free sufficient form of the completeness row, not a
      weaker one; it is the form the paper's Bessel/completeness argument would naturally give.
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5MassAudit.lean` (uncompiled at push, commit
      ae140c9): `z_rowMiss`, `z_colMiss`, `massWitness`, `massWitness_nonempty`, `atL_rowDefect`,
      `atL_rowMass`, `atL_rowMiss_fails`, `mass_stronger_than_defect` (eigenvalues at `L` written as a
      constant function, `J : Fin ⌈L⌉₊ → Fin 1 → ℝ` zero; vanishing tested with η = 1/2). Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-13: STATUS PASS 678/678 at af8fabd, all seven G27 theorems in
      `H5MassAudit.lean` verified.
- [x] G28. `SteklovAudit/H5MassSplit.lean`: the low/high split of the row missing mass, over a `Fintype ι`.
      `missing_nonneg` and `missing_le_one` (from `∀ i, 0 ≤ ∑ j, J i j ^ 2` via `sq_nonneg` and the Bessel row);
      `missing_split`: `∑ i, (1 - r i) ≤ (filter (a i ≤ M)).card + ∑ i ∈ filter (M < a i), (1 - r i)`
      (`Finset.sum_filter_add_sum_filter_not`, `Finset.card_eq_sum_ones`, `Finset.sum_le_sum`). Theorem names:
      `missing_nonneg`, `missing_le_one`, `missing_split`.
      Written by the formalize task 2026-11-13 together with G29 in `SteklovAudit/H5MassSplit.lean` (commit
      a6377f4); `missing_split` repaired in af8fabd (`hsplit.symm`, CI error at 72:82). Ticked by the formalize
      task 2026-11-13: STATUS PASS 678/678 at af8fabd, all three G28 theorems verified.
- [x] G29. Same file as G28: `structure H5bHighMassInputs` = `H5bMassInputs` with `m1`, `rowMiss`,
      `m1Vanish` replaced by a high-energy row `hm1 : ℝ → ℝ → ℝ → ℝ → ℝ`, `rowMissHigh`
      (`∑ i ∈ filter (M < a i), (1 - ∑ j, J i j ^ 2) ≤ hm1 ε γ M L`) and `hm1Vanish` (for every η > 0 there are
      `M`, `L₀` with `hm1 ε γ M L ≤ η * L` for `L ≥ L₀`); the existing `lowCount` row supplies the rest. Prove
      `H5bHighMassInputs.toMass` (a `def` with `m1 ε γ L := ∑ i, (1 - ∑ j, (D ε γ L).J i j ^ 2)`, so `rowMiss`
      is `le_refl`; `m1Vanish` from G28's `missing_split`, `lowCount` and `hm1Vanish`) and `h5b_of_high_mass`. F table: the row missing-mass row is reduced to its high-energy part, given the
      L-uniform low count already in the table (strictly weaker than G26's row when `lowCount` is present).
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5MassSplit.lean` (commit a6377f4, with G28):
      `H5bHighMassInputs`, `H5bHighMassInputs.toMass` (vanishing with η/2 for the high part and threshold
      `max Lhm (max 1 (2 (c + 1) / η))` for the low count), `h5b_of_high_mass`. Ticked by the formalize task
      2026-11-13: STATUS PASS 678/678 at af8fabd, `h5b_of_high_mass` verified.

G30–G33 written by the formalize task on 2026-11-13 (after G27–G29 were ticked). They audit G29, mirror the
high/low split on the model (column) side with a new named model low-count row, and reduce both L-uniform low
counts to a linear growth condition on the eigenvalues. None claims a row is proved for the actual operator.

- [x] G30. `SteklovAudit/H5HighMassAudit.lean`: audit of G29. `highMassWitness : H5bHighMassInputs 0 0`
      (G24's `zData`, `Φ = 2`, `hm1 = 0`, `m2 = 0`, `c = 0`), `highMassWitness_nonempty`; `zero_rowMissHigh_not_mass`:
      a `Fin ⌈L⌉₊` family with all true eigenvalues at 0 and `J = 0` (`Fin 1` columns) where `rowMissHigh` holds
      with `hm1 = 0` for every `M ≥ 0` (the filter `M < 0` is empty) but the full missing row mass is `⌈L⌉₊`, so no
      vanishing `m1` meets G26's `rowMiss` (vanishing tested with η = 1/2, as in G27's `atL_rowMiss_fails`), and the
      same family violates every L-uniform `lowCount`. F table text: the high-energy row alone is strictly weaker
      than the full missing-mass row; the gap is exactly the low count. Theorem names: `highMassWitness_nonempty`,
      `zero_rowMissHigh`, `zero_rowMass`, `zero_rowMissHigh_not_mass`, `zero_not_lowCount`.
      Written by the formalize task 2026-11-13 in `SteklovAudit/H5HighMassAudit.lean` (uncompiled at push, commit
      aa9f255): `z_rowMissHigh`, `highMassWitness` (low-count rate `c = 1` via G24's `z_lowCount`, not `c = 0`),
      `highMassWitness_nonempty`, `zero_rowMissHigh`, `zero_rowMass` (= G27's `atL_rowMass`, same `J`),
      `zero_not_lowCount` (M = 0, L = c 0 + 1), `zero_rowMissHigh_not_mass` (third part is G27's
      `atL_rowMiss_fails`). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 684/684 at 677d47c, all six G30 theorems in
      `H5HighMassAudit.lean` verified.
- [x] G31. `SteklovAudit/H5ColMassSplit.lean`: column mirror of G28–G29. `col_missing_split`:
      `∑ j, (1 - ∑ i, J i j ^ 2) ≤ (filter (b j ≤ M)).card + ∑ j ∈ filter (M < b j), (1 - ∑ i, J i j ^ 2)` from
      `colBessel` (apply G28's `missing_split` to the transpose `fun j i => J i j`). `structure H5bHighMass2Inputs`
      = `H5bHighMassInputs` with `m2`, `colMiss`, `m2Vanish` replaced by a high-energy column row `hm2`,
      `colMissHigh`, `hm2Vanish` (same shape as `hm1Vanish`) plus a NEW named model low-count row `cB`,
      `modelLowCount : ((filter fun j => b j ≤ M).card : ℝ) ≤ cB ε γ M` (new F table row: L-uniform model low
      count). Prove `H5bHighMass2Inputs.toHigh : H5bHighMassInputs E Emod` (a `def`, `m2 ε γ L := ∑ j, (1 - ...)`,
      `colMiss` by `le_refl`, `m2Vanish` copied from G29's `m1Vanish` proof) and `h5b_of_high_mass2`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5ColMassSplit.lean` (uncompiled at push, commit
      f3c71ac): `col_missing_split` (G28's `missing_split` on the transpose), `H5bHighMass2Inputs` (new named
      row `cB`, `modelLowCount`), `H5bHighMass2Inputs.toHigh`, `h5b_of_high_mass2`. Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 686/686 at 21989c5, `col_missing_split` and
      `h5b_of_high_mass2` in `H5ColMassSplit.lean` verified.
- [x] G32. `SteklovAudit/H5LowCountGrowth.lean`: reduce an L-uniform low count to linear eigenvalue growth,
      over `Fin n` with values `a : Fin n → ℝ`. `lowCount_of_linear_growth`: if `0 < s` and
      `∀ k : Fin n, (k : ℝ) * s ≤ a k`, then `((filter fun k => a k ≤ M).card : ℝ) ≤ M / s + 1` (map `k ↦ k.val`
      into `Finset.range (⌊M / s⌋₊ + 1)`, `Finset.card_le_card_of_injOn`, `Nat.floor_le`/`Nat.lt_floor_add_one`;
      if the step is hard, prove the weaker bound via `Finset.card_le_card` on `filter (fun k => (k : ℝ) ≤ M / s)`).
      `count_not_lowCount`: the Weyl `count` row (`card ≤ Cm (1 + L) ^ 2`, Cm = 1) holds for `Fin ⌈L⌉₊` with all
      eigenvalues 0 while no function `c M` bounds the low count for all L, so `lowCount` is a genuine row and
      not implied by `count`. Theorem names: `lowCount_of_linear_growth`, `count_not_lowCount`. F table text:
      each low-count row (true `lowCount`, model `modelLowCount`) follows from linear growth of the indexed
      eigenvalues with an L-independent slope; no growth bound is proved for the actual operator or the model.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5LowCountGrowth.lean` (uncompiled at push, commit
      030d4cc): `card_low_le_floor` (count ≤ ⌊M / s⌋₊ + 1, all M), `lowCount_of_linear_growth` (with `0 ≤ M`
      added: the stated bound M / s + 1 is false for M < -s, where the count is 0), `lowCount_of_linear_growth_abs`
      (|M| / s + 1, all M), `exists_lowCount_of_linear_growth` (lowCount row shape for a family with one slope),
      `ceil_count`, `count_not_lowCount` (second part is G30's `zero_not_lowCount`). Next run: tick if STATUS
      shows it compiled.
      Fixed in commit 2d0b136 (`ceil_count`: `le_or_lt` replaced by `by_cases`). Ticked by the formalize task
      2026-11-14: STATUS PASS 692/692 at 2d0b136.
- [x] G33. `SteklovAudit/H5HighMass2Audit.lean`: audit of G31. `highMass2Witness : H5bHighMass2Inputs 0 0`
      (G24's `zData`, `hm1 = hm2 = 0`, `c = cB = 0`), `highMass2Witness_nonempty`; `highMass2_rows_not_target`:
      the rows `rowMissHigh`, `hm1Vanish`, `colMissHigh`, `hm2Vanish`, `lowCount`, `modelLowCount` are a `Prop` on
      `D` and the rates only (no `E`, `Emod`) and hold for the witness data while `H5bTarget` fails for E = 2L,
      Emod = 0 (reuse G24's `model_count_not_target` pattern). Records that, after G31, all "target in disguise"
      content of H5b sits in the two one-spectrum count rows `trueCount` and `modelCount`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5HighMass2Audit.lean` (uncompiled at push):
      `highMass2OfBounds` (all non-count rows from G24's `zData`, `hm1 = hm2 = 0`, `c = cB = 0`),
      `highMass2Witness`, `highMass2Witness_nonempty`, `highMass2_rows_not_target`, `highMass2_count_not_target`
      (no vanishing `e1` for `E = 2L`, `Emod = 0` with the other rows from the witness). Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 699/699 at fdeaec1, all G33 theorems in
      `H5HighMass2Audit.lean` verified (`highMass2Witness_nonempty`, `highMass2_rows_not_target`,
      `highMass2_count_not_target` and the `zz_*` helpers).

G34–G37 written by the formalize task on 2026-11-14 (after G33 was ticked). G33 showed that all E-dependent
content of H5b sits in the two one-spectrum count rows `trueCount` and `modelCount`. These items replace that
pair by ONE strictly weaker row on the difference of the two smoothed counts (the chain only ever uses the
difference), audit it, and record that this row is (7.29) for the smoothed test with `J` removed. None claims
a row is proved for the actual operator.

- [x] G34. `SteklovAudit/H5DiffCount.lean`: the reduction step, over arbitrary `Fintype ι`, `Fintype κ` with
      `f : ι → ℝ`, `g : κ → ℝ`, `J : ι → κ → ℝ`. `diff_of_counts`: `|X1 - S1| ≤ e1` and `|X2 - S2| ≤ e2` give
      `|(X1 - X2) - (S1 - S2)| ≤ e1 + e2` (abs_sub_le / abs_add, or `abs_le` + linarith).
      `cutoff_of_diff_count`: if `|X - (∑ i, f i - ∑ j, g j)| ≤ e`, `∀ i, |f i| ≤ Φ`, `∀ j, |g j| ≤ Φ`, the row and
      column Bessel bounds hold, `∑ i, (1 - ∑ j, J i j ^ 2) ≤ m1`, `∑ j, (1 - ∑ i, J i j ^ 2) ≤ m2` and `0 ≤ Φ`, then
      `|X - ∑ i, ∑ j, (f i - g j) * J i j ^ 2| ≤ e + Φ * m1 + Φ * m2` (G18's `double_sum_split`, G22's
      `weighted_sum_split` and `defect_le_sup` on rows and on the transpose, then `abs_le` + linarith).
      Theorem names: `diff_of_counts`, `cutoff_of_diff_count`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5DiffCount.lean` (uncompiled at push):
      `diff_of_counts`, helper `defect_abs_le_mass`, `cutoff_of_diff_count`, `cutoff_of_diff_count_nonvacuous`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 703/703 at ffc7a73, all four G34 theorems in
      `H5DiffCount.lean` verified.
- [x] G35. Same file: `structure H5bDiffInputs` = `H5bMassInputs` (G26) with `e1`, `trueCount`, `e1Vanish`,
      `e2`, `modelCount`, `e2Vanish` replaced by one row `e12`, `diffCount`
      (`|(E ε γ L - Emod ε γ L) - (∑ i, P.φ (a i - L) - ∑ j, P.φ (b j - L))| ≤ e12 ε γ L`), `e12Vanish` (same shape
      as `e1Vanish`). Prove `H5bDiffInputs.toPaper : H5bPaperInputs E Emod` (a `def`, `disc = e12 + Φ * m1 +
      Φ * m2`, `cutoff` by G34, `discVanish` by G26's `vanish_const_mul` and G18's `discVanish_of_sides`
      twice), `h5b_of_diff : H5bTarget E Emod` via `h5b_of_paper`, and the weakening direction
      `H5bMassInputs.toDiff : H5bDiffInputs E Emod` (`e12 = e1 + e2` via `diff_of_counts`,
      `e12Vanish` via `discVanish_of_sides`). F table: the two count rows become one row, "smoothed count
      difference"; every `H5bMassInputs` gives an `H5bDiffInputs`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5DiffCount.lean` (uncompiled at push):
      `H5bDiffInputs`, `H5bDiffInputs.toPaper`, `h5b_of_diff`, `toPaper_disc`, and
      `SteklovAudit.H5MissingMass.H5bMassInputs.toDiff` (declared in the `H5MissingMass` namespace so
      `W.toDiff` works). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 705/705 at 072cda1, `h5b_of_diff` and
      `toPaper_disc` in `H5DiffCount.lean` verified (the defs `toPaper`, `toDiff` compile with them).
- [x] G36. `SteklovAudit/H5DiffAudit.lean`: audit of G35. `diffWitness : H5bDiffInputs 0 0` (G27's
      `massWitness` data: G24's `zData`, `Φ = 2`, `m1 = m2 = 0`, `e12 = 0`), `diffWitness_nonempty`; strictness:
      `diff_not_counts`: with `nA = nB = 0` (G24's `zData`) and `E L = Emod L = 2 L`, `diffCount` holds with
      `e12 = 0` while `trueCount` fails for every vanishing `e1` (vanishing tested with η = 1, at L = max L₀ 1,
      as in G9's `not_target_double`), so the single row is strictly weaker than the pair. Theorem names:
      `diffWitness_nonempty`, `double_diffCount`, `double_trueCount_fails`, `diff_not_counts`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5DiffAudit.lean` (uncompiled at push,
      commit aaa21ac): helper `z_diffCount`, `diffOfBounds` (all non-difference fields from `zData`),
      `self_diff_bound`, `diffWitness`, `diffWitness_nonempty`, `diffDouble : H5bDiffInputs (2L) (2L)`,
      `double_diffCount`, `double_trueCount_fails`, `diff_not_counts`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 711/711 at 138418a, all G36 theorems in
      `H5DiffAudit.lean` verified (`z_diffCount`, `self_diff_bound`, `diffWitness_nonempty`,
      `double_diffCount`, `double_trueCount_fails`, `diff_not_counts`).
- [x] G37. Same file as G36: the difference row is not the target in disguise and is where (7.29) now sits.
      `diff_row_not_target`: the family of G25 (`nA L = ⌈L⌉₊` true eigenvalues at 0, `nB = 0`, φ = arctan,
      `E L = ⌈L⌉₊ * arctan (0 - L)`, `Emod = 0`) satisfies `diffCount` with `e12 = 0` (reuse G25's
      `ceil_trueCount` / `const_sum_fin`) while `H5bTarget E Emod` fails (|E| ≥ (π/4) L for L ≥ 1; η = 1/2 as in
      G25's `ceil_trueSide_fails`). Also `diff_rows_E_free`: every field of `H5bDiffInputs` other than
      `diffCount` is a `Prop` on `D`, `P` and the rates only (state it as G33 did: those rows hold for the
      witness data while `H5bTarget` fails for E = 2L, Emod = 0). F table text: after G35, all E-dependent
      content of H5b is the one row `diffCount`, i.e. (7.29) for the test `φ (· - L)` with `J` removed; that row
      is open for the actual operator. Theorem names: `diff_row_not_target`, `diff_rows_E_free`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5DiffAudit.lean` (uncompiled at push):
      helpers `ceil_diffCount` (G25 family, empty model, `e12 = 0`), `ceil_not_target` (η = 1/2);
      `diff_row_not_target`; `diff_rows_E_free` (for any `E`, `Emod`, `diffOfBounds` gives a full structure
      from the difference row alone; for `E = 2L`, `Emod = 0` the target fails and no vanishing `e12` meets
      the row). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 715/715 at e878059, all G37 theorems in
      `H5DiffAudit.lean` verified (`ceil_diffCount`, `ceil_not_target`, `diff_row_not_target`, `diff_rows_E_free`).

G38–G41 written by the formalize task on 2026-11-14 (after G37 was ticked). G37 showed that all E-dependent
content of H5b is the one row `diffCount`. G38–G39 put that row together with the weakest missing-mass rows
(G29/G31 high-mass split), so the F table has one current strongest form. G40–G41 check what happens when
`E`, `Emod` are exactly the smoothed counts of the coupled spectra: `diffCount` is then free, and the content
moves to the E-free rows (missing mass, i.e. completeness of the coupling), which stay named inputs. None
claims a row is proved for the actual operator.

- [x] G38. `SteklovAudit/H5DiffHighMass.lean`: `structure H5bDiffHigh2Inputs` = `H5bDiffInputs` (G35) with
      `m1`, `rowMiss`, `m1Vanish`, `m2`, `colMiss`, `m2Vanish` replaced by the high-mass rows of
      `H5bHighMass2Inputs` (G31): `hm1`, `rowMissHigh`, `hm1Vanish`, `hm2`, `colMissHigh`, `hm2Vanish`, and add
      `cB`, `modelLowCount` (copy the field shapes from `H5ColMassSplit.lean`). Prove `H5bDiffHigh2Inputs.toDiff :
      H5bDiffInputs E Emod` (a `def`; take `m1`, `m2` to be the exact missing-mass sums with `le_refl`, and their
      vanishing as in `H5bHighMass2Inputs.toHigh` and the G29 analogue, reusing whatever lemma those use),
      `h5b_of_diffHigh2 : H5bTarget E Emod` via `h5b_of_diff`, and the weakening direction
      `H5bHighMass2Inputs.toDiffHigh2` (declare in the `H5ColMassSplit` namespace via `_root_`; `e12 = e1 + e2` by
      `diff_of_counts`, `e12Vanish` by `discVanish_of_sides`). If the file would exceed ~120 lines, put the
      weakening direction in G39 instead. Theorem names: `h5b_of_diffHigh2` (defs `toDiff`, `toDiffHigh2`).
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5DiffHighMass.lean` (uncompiled at push):
      helper `vanish_of_split` (low/high split with vanishing high part vanishes), `H5bDiffHigh2Inputs`,
      `H5bDiffHigh2Inputs.toDiff`, `h5b_of_diffHigh2`. The weakening direction `toDiffHigh2` is moved to G39
      (line budget). Ticked by the formalize task 2026-11-14: STATUS PASS 717/717 at 1319797,
      `vanish_of_split` and `h5b_of_diffHigh2` in the table.
- [x] G39. `SteklovAudit/H5DiffHighAudit.lean`: audit of G38. First (moved from G38) the weakening direction
      `H5bHighMass2Inputs.toDiffHigh2 : H5bDiffHigh2Inputs E Emod` (declare via `_root_` in the `H5ColMassSplit`
      namespace; `e12 = e1 + e2` by `diff_of_counts`, `e12Vanish` by `discVanish_of_sides`, other fields copied). `diffHigh2OfBounds E Emod e12 h v` (as G36's
      `diffOfBounds`, empty family `zData`, `hm1 = hm2 = 0`, `cB = 1`), `diffHigh2Witness_nonempty :
      Nonempty (H5bDiffHigh2Inputs 0 0)`; strictness `diffHigh2_not_highMass2`: for `E = Emod = 2L` a full
      `H5bDiffHigh2Inputs` exists with `e12 = 0`, while no `H5bHighMass2Inputs (2L) (2L)` built on the empty family
      exists (its `trueCount` fails by G36's `double_trueCount_fails`). F table text: the current strongest form
      of H5b is `H5bDiffHigh2Inputs`. Theorem names: `diffHigh2Witness_nonempty`, `diffHigh2_not_highMass2`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5DiffHighAudit.lean` (uncompiled at push):
      `toDiffHigh2`, `diffHigh2OfBounds` (with `c = cB = 0`), `diffHigh2Witness_nonempty`,
      `highMass2_double_empty_fails`, `diffHigh2_not_highMass2`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 720/720 at 1112ed5, `diffHigh2Witness_nonempty`,
      `highMass2_double_empty_fails`, `diffHigh2_not_highMass2` verified.
- [x] G40. `SteklovAudit/H5SmoothedIdent.lean`: `structure H5bSmoothedInputs` = the fields of `H5bDiffInputs`
      with `e12`, `diffCount`, `e12Vanish` removed (no `E`, `Emod` parameters). Defs `W.Esm ε γ L := ∑ i, W.P.φ
      ((W.D ε γ L).a i - L)` and `W.Emodsm` (same with `b`). Prove `smoothed_diffCount` (the difference row for
      `W.Esm`, `W.Emodsm` with `e12 = 0`: `sub_self`, `abs_zero`), `H5bSmoothedInputs.toDiff : H5bDiffInputs W.Esm
      W.Emodsm` (`e12 = 0`, vanishing by G27/G36's `zeroDisc_vanish` or `mul_nonneg` + `le_of_lt`), and
      `h5b_of_smoothed : H5bTarget W.Esm W.Emodsm`, plus `diffCount_iff_ident`: for any `E`, `Emod`, the
      difference row with rate `e` is the same statement as `|(E - W.Esm) - (Emod - W.Emodsm)| ≤ e` (`ring_nf` or
      `congr 1; ring`). Docstring: if the paper's `E`, `Emod` are the smoothed counts of the same coupled spectra,
      (7.29) needs only the E-free rows; this does not prove those rows. Theorem names: `smoothed_diffCount`,
      `h5b_of_smoothed`, `diffCount_iff_ident`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5SmoothedIdent.lean` (uncompiled at push):
      `H5bSmoothedInputs`, defs `Esm`, `Emodsm`, `toDiff` (`e12 = 0`, `L₀ = 0`), theorems `smoothed_diffCount`,
      `h5b_of_smoothed`, `diffCount_iff_ident`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 723/723 at a51bcce, `smoothed_diffCount`,
      `h5b_of_smoothed`, `diffCount_iff_ident` verified.
- [x] G41. Same file as G40 (or `SteklovAudit/H5SmoothedAudit.lean`): the E-free rows carry real content.
      `smoothed_rowMiss_forces`: for the G25 family (`nA L = ⌈L⌉₊` true eigenvalues at `0`, `nB = 0`, so every row
      mass `∑ j : Fin 0, J i j ^ 2` is `0`), any `m1` meeting `rowMiss` has `m1 ε γ L ≥ ⌈L⌉₊`, hence `m1Vanish`
      fails (η = 1/2 at `L = max L₀ 1`, `Nat.le_ceil`); `smoothed_needs_mass`: for that family the smoothed counts
      violate `H5bTarget` (G37's `ceil_not_target`) and no `H5bSmoothedInputs` with those data exists. F table text:
      on the smoothed-identification route the open content of (7.29) is the missing-mass (completeness) rows.
      Theorem names: `smoothed_rowMiss_forces`, `smoothed_needs_mass`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5SmoothedAudit.lean` (uncompiled at push):
      `smCeilD` (the G25 family as `Data (Fin ⌈L⌉₊) (Fin 0)`), `smCeil_rowMass` (missing row mass `= ⌈L⌉₊`),
      `smoothed_rowMiss_forces`, `smCeil_E`, `smCeil_Emod`, `smCeil_not_target` (via G37's `ceil_not_target`),
      `smoothed_needs_mass` (target fails, and no `H5bSmoothedInputs` has that missing row mass). Next run:
      tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 729/729 at 0c45ac5, `smCeil_rowMass`,
      `smoothed_rowMiss_forces`, `smCeil_E`, `smCeil_Emod`, `smCeil_not_target`, `smoothed_needs_mass` verified.

G42–G45 written by the formalize task on 2026-11-14 (after G41 was ticked). G40–G41 put the open content of
(7.29), on the smoothed-identification route, in the E-free rows of `H5bSmoothedInputs`, chiefly missing mass.
G42 checks that structure is non-vacuous and is implied by the G35 form; G43 replaces its missing-mass rows by
the weaker high-mass rows (G38 shape); G44 reduces the missing-mass rows to row/column normalization of `J`
(completeness in spectral coordinates); G45 shows the column row carries content of its own. None claims a row
is proved for the actual operator.

- [x] G42. `SteklovAudit/H5SmoothedWitness.lean`: `H5bDiffInputs.toSmoothed : H5bSmoothedInputs` for any `E`,
      `Emod` (a `def` declared via `_root_` in the `H5DiffCount` namespace or as a plain `def`; forget `e12`,
      `diffCount`, `e12Vanish`, copy the rest), `smoothedWitness_nonempty : Nonempty H5bSmoothedInputs` (via
      G36/G37's `diffOfBounds` or the G36 witness `diffWitness_nonempty` composed with `toSmoothed`), and
      `smoothed_witness_target : ∃ W : H5bSmoothedInputs, H5bTarget W.Esm W.Emodsm` (from `h5b_of_smoothed`).
      Check: the G40 structure is satisfiable and is no stronger than the G35 form. Theorem names:
      `smoothedWitness_nonempty`, `smoothed_witness_target` (def `toSmoothed`).
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5SmoothedWitness.lean` (uncompiled at push):
      `H5bDiffInputs.toSmoothed` (declared via `_root_` in the `H5DiffCount` namespace), `toSmoothed_Esm`,
      `toSmoothed_Emodsm`, `toSmoothed_P` (rfl), `smoothedWitness_nonempty`, `smoothed_witness_target`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 734/734 at e652886, `toSmoothed_Esm`,
      `toSmoothed_Emodsm`, `toSmoothed_P`, `smoothedWitness_nonempty`, `smoothed_witness_target` verified.
- [x] G43. `SteklovAudit/H5SmoothedHigh.lean`: `structure H5bSmoothedHigh2Inputs` = `H5bSmoothedInputs` with
      `m1`, `rowMiss`, `m1Vanish`, `m2`, `colMiss`, `m2Vanish` replaced by the high-mass rows `hm1`, `rowMissHigh`,
      `hm1Vanish`, `hm2`, `colMissHigh`, `hm2Vanish`, plus `cB`, `modelLowCount` (copy the field shapes from
      `H5bDiffHigh2Inputs` in `H5DiffHighMass.lean`, dropping `e12`, `diffCount`, `e12Vanish`). Prove
      `H5bSmoothedHigh2Inputs.toDiffHigh2 : H5bDiffHigh2Inputs W.Esm W.Emodsm` (`e12 = 0` as in G40's `toDiff`;
      `Esm`/`Emodsm` defined for this structure in the same way, or via a `toSmoothedData` projection) and
      `h5b_of_smoothedHigh2` via `h5b_of_diffHigh2`. F table text: on the smoothed route the current strongest
      form is `H5bSmoothedHigh2Inputs`. Theorem names: `h5b_of_smoothedHigh2` (def `toDiffHigh2`).
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5SmoothedHigh.lean` (uncompiled at push,
      commit ec8ddcc): `H5bSmoothedHigh2Inputs`, defs `Esm`, `Emodsm`, `toDiffHigh2` (`e12 = 0`, `L₀ = 0`),
      theorems `smoothedHigh_diffCount`, `h5b_of_smoothedHigh2`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 736/736 at f02746a, `smoothedHigh_diffCount`,
      `h5b_of_smoothedHigh2` verified.
- [x] G44. `SteklovAudit/H5Parseval.lean`: reduction of the missing-mass rows to normalization of `J`.
      `rowMiss_of_rowNorm`: if `∀ i, ∑ j, J i j ^ 2 = 1` (named hypothesis `rowNorm`, the completeness of the
      model basis for each true eigenvector) then `∑ i, (1 - ∑ j, J i j ^ 2) ≤ 0`, and the constant-zero `m1`
      meets `m1Vanish` (`mul_nonneg`); `colMiss_of_colNorm` likewise for columns; `smoothedOfNorm`: an
      `H5bSmoothedInputs` built from `rowNorm`, `colNorm` and the remaining rows (bessel/colBessel follow from
      the norms by `le_of_eq`, so drop them too). F table text: the missing-mass row may be replaced by exact
      row/column normalization of the coupling plus the other E-free rows; this is a reduction, not a proof of
      normalization. Theorem names: `rowMiss_of_rowNorm`, `colMiss_of_colNorm` (def `smoothedOfNorm`).
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5Parseval.lean` (uncompiled at push):
      `rowMiss_of_rowNorm`, `colMiss_of_colNorm`, `zero_vanish`, `card_eq_of_norms` (row + column
      normalization force `card ι = card κ`, so the reduction needs square truncations), structure
      `H5bNormInputs`, def `smoothedOfNorm`, `h5b_of_norm`, `norm_card_eq`. Next run: tick if STATUS shows
      it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 742/742 at d0b22e6, `rowMiss_of_rowNorm`,
      `colMiss_of_colNorm`, `card_eq_of_norms`, `zero_vanish`, `h5b_of_norm`, `norm_card_eq` verified.
- [x] G45. `SteklovAudit/H5SmoothedColAudit.lean`: the column row carries content of its own. `smColD L :
      Data (Fin 0) (Fin ⌈L⌉₊)` (no true eigenvalues, `⌈L⌉₊` model eigenvalues at `0`, `J = 0`): its row missing
      mass is `0` (so `rowMiss`/`m1Vanish` hold with `m1 = 0`), its column missing mass is `⌈L⌉₊`;
      `smoothed_colMiss_forces` (any `m2` meeting `colMiss` has `m2 ≥ ⌈L⌉₊`, so `m2Vanish` fails, as in G41) and
      `smCol_not_target` (the smoothed counts `0` and `⌈L⌉₊ · arctanProfile.φ (0 - L)` violate `H5bTarget`; reuse
      G41's argument with `abs_sub_comm`). Theorem names: `smCol_rowMass_zero`, `smoothed_colMiss_forces`,
      `smCol_not_target`.
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5SmoothedColAudit.lean` (uncompiled at push):
      `smColD`, `smCol_rowMass_zero`, `smCol_rowMiss_zero` (row rows hold with `m1 = 0`), `smCol_colMass`,
      `smoothed_colMiss_forces`, `smCol_E`, `smCol_Emod`, `smCol_not_target`, `smoothed_needs_colMass`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 750/750 at bfb5820 (code commit e77830e),
      `smCol_rowMass_zero`, `smCol_rowMiss_zero`, `smCol_colMass`, `smoothed_colMiss_forces`, `smCol_E`,
      `smCol_Emod`, `smCol_not_target`, `smoothed_needs_colMass` verified.

G46–G49 written by the formalize task on 2026-11-14 (after G45 was ticked). G44 replaced both missing-mass rows
by exact row and column normalization, but `card_eq_of_norms` shows that forces square truncations
(`nA = nB`), which the actual coupling need not have. G46–G49 keep normalization on one side only and show the
other missing-mass row is then exactly a truncation-size gap row; G47 checks it is no stronger than G44 and
matches the G45 family; G48 checks the new structures are satisfiable, including a non-square case. None claims
a row (normalization, gap, count, defect, tail, low count) is proved for the actual operator.

- [x] G46. `SteklovAudit/H5ColCount.lean` (imports `SteklovAudit.H5Parseval`): one-sided normalization.
      `colMass_eq_of_rowNorm`: for `D : Data ι κ` with `rowNorm : ∀ i, ∑ j, D.J i j ^ 2 = 1`,
      `∑ j, (1 - ∑ i, D.J i j ^ 2) = (Fintype.card κ : ℝ) - Fintype.card ι` (`Finset.sum_sub_distrib`,
      `Finset.sum_comm`, then the `card_eq_of_norms` argument); `rowMass_eq_of_colNorm` symmetric.
      `structure H5bRowNormInputs` = `H5bNormInputs` with `colNorm` replaced by `colBessel`, `m2`,
      `cardGap : ∀ ε γ L, (nB ε γ L : ℝ) - nA ε γ L ≤ m2 ε γ L` and `m2Vanish` (shape of G40's). Def
      `smoothedOfRowNorm : H5bSmoothedInputs` (`m1 = 0` via `rowMiss_of_rowNorm`/`zero_vanish`; `colMiss`
      from `colMass_eq_of_rowNorm` + `cardGap`) and `h5b_of_rowNorm` via `h5b_of_smoothed`. Docstring: the
      gap row is a statement about truncation sizes only; it is not proved. Theorem names:
      `colMass_eq_of_rowNorm`, `rowMass_eq_of_colNorm`, `h5b_of_rowNorm` (def `smoothedOfRowNorm`).
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5ColCount.lean` (uncompiled at push):
      `colMass_eq_of_rowNorm`, `rowMass_eq_of_colNorm`, structure `H5bRowNormInputs`, `rowNorm_colMiss`,
      def `smoothedOfRowNorm`, `h5b_of_rowNorm`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-14: STATUS PASS 754/754 at ca072a7, `colMass_eq_of_rowNorm`,
      `rowMass_eq_of_colNorm`, `rowNorm_colMiss`, `h5b_of_rowNorm` verified.
- [x] G47. `SteklovAudit/H5ColCountAudit.lean`: the gap row is the column row, no more and no less.
      `colMiss_iff_cardGap`: under `rowNorm`, for every `m`, column missing mass `≤ m` iff
      `card κ - card ι ≤ m` (rewrite by `colMass_eq_of_rowNorm`). `smCol_cardGap`: the G45 family `smColD L`
      satisfies `rowNorm` (vacuously, `Fin 0`) and has gap `⌈L⌉₊`, matching `smCol_colMass`. Def
      `rowNormOfNorm : H5bNormInputs → H5bRowNormInputs` (`m2 = 0`, gap `≤ 0` from `norm_card_eq`,
      `colBessel` from `colNorm`), so G46 is no stronger than G44. Theorem names: `colMiss_iff_cardGap`,
      `smCol_cardGap` (def `rowNormOfNorm`).
      Written by the formalize task 2026-11-14 in `SteklovAudit/H5ColCountAudit.lean` (uncompiled at push):
      `colMiss_iff_cardGap`, `smCol_cardGap`, def `rowNormOfNorm`, `rowNormOfNorm_m2`, `rowNormOfNorm_target`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 758/758 at 8d152cb, `colMiss_iff_cardGap`,
      `smCol_cardGap`, `rowNormOfNorm_m2`, `rowNormOfNorm_target` verified.
- [x] G48. `SteklovAudit/H5RowNormWitness.lean`: non-vacuity. `normWitness_nonempty : Nonempty H5bNormInputs`
      and `rowNormWitness_nonsquare : ∃ W : H5bRowNormInputs, ∀ ε γ L, W.nA ε γ L < W.nB ε γ L`. Reuse the
      profile witness used in G45 (`arctanProfile` or the G36/G37 witness). Prefer `nA = 1`, `nB = 2`,
      `J 0 0 = 1`, other entries `0`, all eigenvalues `0`, if `Data`'s remaining fields allow it; otherwise
      `nA = 0`, `nB = 1` (and say in the docstring that `rowNorm` is then vacuous). Gap rate `m2 = 1`,
      `m2Vanish` with `L₀ = 1 / η`. Theorem names: `normWitness_nonempty`, `rowNormWitness_nonsquare`.
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5RowNormWitness.lean` (uncompiled at push,
      commit 4df671a): defs `normWitness` (G24's `zData`), `gapD`, `rowNormWitness` (`nA = 0`, `nB = 1`,
      `m2 = 1`, so `rowNorm` is vacuous); theorems `normWitness_nonempty`, `rowNormWitness_nonsquare`,
      `rowNormWitness_target`, and `rowNorm_count_neg_one` (the count row at `L = -1` forces `nA = 0`, which
      is why the preferred `nA = 1`, `nB = 2` witness is impossible). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 768/768 at deea382, `normWitness_nonempty`,
      `rowNormWitness_nonsquare`, `rowNormWitness_target`, `rowNorm_count_neg_one` verified.
- [x] G49. `SteklovAudit/H5ColNorm.lean`: the mirror of G46. `structure H5bColNormInputs` = `H5bNormInputs`
      with `rowNorm` replaced by `bessel`, `m1`, `rowGap : ∀ ε γ L, (nA ε γ L : ℝ) - nB ε γ L ≤ m1 ε γ L`
      and `m1Vanish`; def `smoothedOfColNorm` (`rowMiss` from `rowMass_eq_of_colNorm`) and
      `h5b_of_colNorm`. F table text: on the smoothed route, with completeness on one side, the other
      missing-mass row may be replaced by an o(L) gap between truncation sizes. Theorem names:
      `h5b_of_colNorm` (def `smoothedOfColNorm`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5ColNorm.lean` (uncompiled at push,
      commit e316e35): structure `H5bColNormInputs`, `colNorm_rowMiss`, def `smoothedOfColNorm`,
      `h5b_of_colNorm`, `smoothedOfColNorm_m2`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 771/771 at 469be46 (code commit e316e35),
      `colNorm_rowMiss`, `h5b_of_colNorm`, `smoothedOfColNorm_m2` verified.

G50–G53 written by the formalize task on 2026-11-15 (after G49 was ticked). Definition check on every
`H5b…Inputs` form: the E-free rows (count, defect, tail, low count, missing mass, Bessel) are quantified
over all real `L`, but `H5bTarget` only concerns large `L`. G48's `rowNorm_count_neg_one` shows the count row
at `L = -1` forces an empty true truncation there, a constraint with no paper content. G50–G53 replace
`H5bSmoothedInputs` by a strictly weaker form whose E-free rows are required only for `1 ≤ L` (the paper's
range), prove it still gives (7.29) for the smoothed counts, and prove it is strictly weaker. None claims a
row is proved for the actual operator.

- [x] G50. `SteklovAudit/H5Reindex.lean` (reduction step G51 needs): `def Data.reindex (D : Data ι κ)
      (e : ι ≃ ι') (f : κ ≃ κ') : Data ι' κ'` (`a := D.a ∘ e.symm`, `b := D.b ∘ f.symm`,
      `J i j := D.J (e.symm i) (f.symm j)`) and invariance under it, each by `Equiv.sum_comp` (and
      `Finset.card_equiv` / `Finset.card_bij` or `Finset.card_map` for the filter): `reindex_rowSq`
      (`∑ j, J' i j ^ 2 = ∑ j, D.J (e.symm i) j ^ 2`), `reindex_colSq`, `reindex_rowMass`
      (`∑ i, (1 - ∑ j, J'^2)` unchanged), `reindex_colMass`, `reindex_hs2K` (`hs2 D'.K = hs2 D.K`),
      `reindex_tail` (`hs2 (mask (hiE D' M) D'.K) = hs2 (mask (hiE D M) D.K)`), `reindex_lowCount`
      (card of `{i | a' i ≤ M}` unchanged), `reindex_smoothed` (`∑ i, φ (a' i - L) = ∑ i, φ (D.a i - L)`,
      same for `b`). Docstring: bookkeeping for G51 only; moves no row by itself.
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5Reindex.lean` (uncompiled at push,
      commit fa52170): def `Data.reindex` (in namespace `SteklovAudit.AbstractTransfer`); theorems
      `reindex_a`, `reindex_b`, `reindex_J`, `reindex_K`, `sum_sum_reindex`, `hs2_reindex`, `reindex_rowSq`,
      `reindex_colSq`, `reindex_rowMass`, `reindex_colMass`, `reindex_hs2K`, `reindex_tail`,
      `reindex_lowCount`, `reindex_smoothedA`, `reindex_smoothedB`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 786/786 at 7f3dfed (code commit fa52170), all 15
      `H5Reindex` theorems verified.
- [x] G51. `SteklovAudit/H5EventualRows.lean` (imports `SteklovAudit.H5Reindex`): `structure
      H5bSmoothedEvInputs` = `H5bSmoothedInputs` (G40) with `rowMiss`, `colMiss`, `bessel`, `colBessel`,
      `count`, `defect`, `tail`, `ha`, `hb`, `lowCount` each guarded by `1 ≤ L →` (rates `m1`, `m2`, `τ`, `c`,
      `Cm`, `Ck`, `tailRate`, `m1Vanish`, `m2Vanish` unchanged). Glued data: `evN W ε γ L := if 1 ≤ L then
      W.nA ε γ L else 0` (same for `nB`) and `evD` by `dite`: for `h : 1 ≤ L`, `(W.D ε γ L).reindex
      (finCongr (if_pos h).symm) (finCongr (if_pos h).symm)`, otherwise G24's `zData` reindexed along
      `finCongr (if_neg h).symm`. Prove `evD_pos` (the `dif_pos` unfolding), and the empty-side facts used
      in G52: `tau_nonneg` (`0 ≤ τ ε γ M`, from `tail` at `L = 1` and `hs2 ≥ 0`), `c_nonneg` (from
      `lowCount` at `L = 1`). Theorem names: `evD_pos`, `tau_nonneg`, `c_nonneg` (defs `evN`, `evNB`, `evD`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5EventualRows.lean` (uncompiled at push):
      structure `H5bSmoothedEvInputs`, def `ofSmoothed` (old form ⇒ new), defs `evN`, `evNB`, `evD`;
      theorems `evN_pos`, `evNB_pos`, `evN_neg`, `evNB_neg`, `evD_pos`, `tau_nonneg`, `c_nonneg`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 793/793 at dd7ba3a (code commit 53eba9c),
      `evN_pos`, `evNB_pos`, `evN_neg`, `evNB_neg`, `evD_pos`, `tau_nonneg`, `c_nonneg` verified.
- [x] G52. Same file as G51 (or `SteklovAudit/H5EventualTarget.lean`): `def H5bSmoothedEvInputs.toSmoothed
      : H5bSmoothedInputs` on the glued family (`m1' L := if 1 ≤ L then m1 L else 0`, same for `m2`; for
      `L < 1` every row holds for the empty data, using `hCm`, `tau_nonneg`, `c_nonneg`, `positivity`; for
      `1 ≤ L` transport by the G50 lemmas); `ev_Esm_eq` / `ev_Emodsm_eq`: for `1 ≤ L` the glued smoothed
      counts equal `∑ i, W.P.φ ((W.D ε γ L).a i - L)` and the model analogue; `h5b_of_smoothedEv`:
      `H5bTarget` for those original smoothed counts (from `h5b_of_smoothed`, taking `L₀ := max L₀ 1`).
      F table text: on the smoothed route the E-free rows need only hold for `L ≥ 1`. Theorem names:
      `ev_Esm_eq`, `ev_Emodsm_eq`, `h5b_of_smoothedEv` (def `toSmoothed`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5EventualTarget.lean` (uncompiled at push,
      commit 379ab84): defs `evM1`, `evM2`, `toSmoothed`; theorems `evM1_pos`, `evM1_neg`, `evM2_pos`,
      `evM2_neg`, `evD_neg`, `hs2_fin0`, `card_filter_zData`, `ev_Esm_eq`, `ev_Emodsm_eq`,
      `h5b_of_smoothedEv`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 803/803 at 82a4e4f (code commit 379ab84), all 10
      `H5EventualTarget` theorems verified.
- [x] G53. `SteklovAudit/H5EventualAudit.lean`: the new form is strictly weaker and non-vacuous.
      `smoothed_count_neg_one : ∀ W : H5bSmoothedInputs, ∀ ε γ, W.nA ε γ (-1) = 0` (as G48's
      `rowNorm_count_neg_one`); `evWitness : H5bSmoothedEvInputs` with `nA = nB = 1`, `a = b = 0`, `J = 1`,
      `P = arctanProfile`, `Φ = 2`, `m1 = m2 = 0` (`zero_vanish`), `Cm = 1`, `Ck = 0`, `τ = 0`, `c = 1`;
      `evWitness_not_smoothed : ¬ ∃ V : H5bSmoothedInputs, V.nA = evWitness.nA` (G53 strictness: the
      true truncation is nonempty at `L = -1`); `evWitness_target` (from `h5b_of_smoothedEv`). Theorem
      names: `smoothed_count_neg_one`, `evWitness_not_smoothed`, `evWitness_target` (def `evWitness`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5EventualAudit.lean` (uncompiled at push,
      commit ed7ac50): def `evOneD` (1×1, `a = b = 0`, `J = 1`), def `evWitness`; theorems
      `smoothed_count_neg_one`, `evOneD_rowSq`, `evOneD_colSq`, `evOneD_K`, `evOneD_hs2K`, `evOneD_count`,
      `evOneD_defect`, `evOneD_tail`, `evOneD_lowCount`, `evWitness_nonempty`, `evWitness_not_smoothed`,
      `evWitness_target`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 815/815 at 452bcb9 (code commit ed7ac50), all 12
      `H5EventualAudit` theorems verified.

G54–G57 written by the formalize task on 2026-11-15 (after G53 was ticked). G50–G53 guarded the E-free rows of
`H5bSmoothedInputs` by `1 ≤ L`. The one-sided normalization forms `H5bRowNormInputs` (G46) and
`H5bColNormInputs` (G49) still quantify `rowNorm`/`colNorm`, the gap row and the other rows over all real `L`;
G48's `rowNorm_count_neg_one` is why their witness had to make `rowNorm` vacuous (`nA = 0`). G54–G57 guard
those rows too, reduce to `H5bSmoothedEvInputs` (G51), and check the new forms are strictly weaker with a
witness where normalization is not vacuous. None claims a row is proved for the actual operator.

- [x] G54. `SteklovAudit/H5RowNormEv.lean` (imports `SteklovAudit.H5EventualTarget`, `SteklovAudit.H5ColCount`):
      `structure H5bRowNormEvInputs` = `H5bRowNormInputs` (G46) with every row (`rowNorm`, `colBessel`,
      `cardGap`, `count`, `defect`, `tail`, `ha`, `hb`, `lowCount`) guarded by `1 ≤ L →` (rates and their
      vanishing unchanged; copy field names from `H5ColCount.lean`). Def `toSmoothedEv : H5bSmoothedEvInputs`
      (`m1 = 0` with `rowMiss` from `rowMiss_of_rowNorm` and `m1Vanish` from `zero_vanish`; `bessel` by
      `le_of_eq` from `rowNorm`; `colMiss` from `colMass_eq_of_rowNorm` + `cardGap`, using
      `Fintype.card_fin`), def `ofRowNorm : H5bRowNormInputs → H5bRowNormEvInputs` (forget the guards), and
      `h5b_of_rowNormEv`: `H5bTarget` for the original smoothed counts `∑ i, W.P.φ ((W.D ε γ L).a i - L)` and
      the model analogue, via `h5b_of_smoothedEv` (state it in exactly the form `h5b_of_smoothedEv` uses for
      `toSmoothedEv`). Docstring: row normalization and the gap row are not proved. Theorem names:
      `toSmoothedEv_nA` (rfl), `h5b_of_rowNormEv` (defs `toSmoothedEv`, `ofRowNorm`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5RowNormEv.lean` (uncompiled at push,
      commit 8db8d3f): structure `H5bRowNormEvInputs`, defs `ofRowNorm`, `toSmoothedEv`; theorems
      `rowNormEv_colMiss`, `toSmoothedEv_nA`, `h5b_of_rowNormEv`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 818/818 at d4527a8 (code commit 8db8d3f),
      `rowNormEv_colMiss`, `toSmoothedEv_nA`, `h5b_of_rowNormEv` verified.
- [x] G55. `SteklovAudit/H5RowNormEvAudit.lean`: non-vacuity and strictness of G54. `rnD`: `Data (Fin 1) (Fin 2)`
      with `a = b = 0`, `J 0 0 = 1`, `J 0 1 = 0` (`rnD_rowNorm : ∀ i, ∑ j, rnD.J i j ^ 2 = 1`, by
      `Fin.sum_univ_two`; `rnD_colMass` = 1 by `colMass_eq_of_rowNorm` or direct `Fin.sum_univ_two`).
      `rowNormEvWitness : H5bRowNormEvInputs` with `nA = 1`, `nB = 2`, `D = rnD`, `P = arctanProfile`,
      `Φ = 2`, `m2 = 1` (vanishing with `L₀ = 1 / η` as in G48), `Cm = 1`, `Ck` with `hs2 rnD.K ≤ Ck^2`
      (compute `rnD.K` as G53's `evOneD_K` did, or take `Ck` large and bound), `τ = 0` if the tail of `rnD.K`
      vanishes else a constant, `c = 1`. Theorems `rowNormEvWitness_genuine` (`rowNorm` holds with `nA = 1 > 0`,
      so it is not vacuous), `rowNormEv_not_rowNorm : ¬ ∃ V : H5bRowNormInputs, V.nA = rowNormEvWitness.nA`
      (via G48's `rowNorm_count_neg_one`), `rowNormEvWitness_target` (from `h5b_of_rowNormEv`). If the file
      would exceed ~120 lines, move `rowNormEvWitness_target` to G57. Theorem names as above (def `rnD`,
      `rowNormEvWitness`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5RowNormEvAudit.lean` (uncompiled at push,
      commit e2fcabe): defs `rnD` (`J 0 j = if j.val = 0 then 1 else 0`), `rowNormEvWitness` (`Ck = 0`,
      `τ = 0` since `K = 0`); theorems `rnD_rowNorm`, `rnD_colBessel`, `rnD_K`, `rnD_hs2K`, `rnD_defect`,
      `rnD_tail`, `rnD_lowCount`, `rowNormEvWitness_genuine`, `rowNormEv_not_rowNorm`,
      `rowNormEvWitness_target`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 828/828 at 6d3d18b (code commit e2fcabe), all 10
      `H5RowNormEvAudit` theorems verified.
- [x] G56. `SteklovAudit/H5ColNormEv.lean` (mirror of G54 for G49): `structure H5bColNormEvInputs` =
      `H5bColNormInputs` with every row guarded by `1 ≤ L →`; def `toSmoothedEv` (`m2 = 0` via
      `colMiss_of_colNorm`/`zero_vanish`, `colBessel` from `colNorm`, `rowMiss` from `rowMass_eq_of_colNorm`
      + `rowGap`), def `ofColNorm`, and `h5b_of_colNormEv` via `h5b_of_smoothedEv`. F table text: on the
      smoothed route with one-sided completeness, normalization and the gap row need only hold for `L ≥ 1`.
      Theorem names: `toSmoothedEv_nB` (rfl), `h5b_of_colNormEv` (defs `toSmoothedEv`, `ofColNorm`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5ColNormEv.lean` (uncompiled at push,
      commit eaa10f9): structure `H5bColNormEvInputs`, defs `ofColNorm`, `toSmoothedEv`; theorems
      `colNormEv_rowMiss`, `toSmoothedEv_nB`, `h5b_of_colNormEv`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 846/846 at 4e531be (code commit eaa10f9),
      `colNormEv_rowMiss`, `toSmoothedEv_nB`, `h5b_of_colNormEv` verified.
- [x] G57. `SteklovAudit/H5ColNormEvAudit.lean`: witness for G56 with `nA = 2`, `nB = 1`, `cnD : Data (Fin 2)
      (Fin 1)`, `a = b = 0`, `J 0 0 = 1`, `J 1 0 = 0` (`cnD_colNorm`), `m1 = 1`, other rates as in G55;
      `colNormEvWitness_genuine` (`colNorm` holds with `nB = 1 > 0` and the row gap is `1`, non-square),
      `colNormEv_not_colNorm : ¬ ∃ V : H5bColNormInputs, V.nA = colNormEvWitness.nA` (the count row of
      `H5bColNormInputs` at `L = -1` forces `nA = 0`, as `rowNorm_count_neg_one`), and
      `colNormEvWitness_target`. Theorem names as above (defs `cnD`, `colNormEvWitness`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5ColNormEvAudit.lean` (uncompiled at push,
      commit 59126e2): defs `cnD` (`J i 0 = if i.val = 0 then 1 else 0`), `colNormEvWitness` (`Ck = 0`,
      `τ = 0` since `K = 0`, `c = 2`); theorems `cnD_colNorm`, `cnD_bessel`, `cnD_K`, `cnD_hs2K`,
      `cnD_defect`, `cnD_tail`, `cnD_count`, `cnD_lowCount`, `colNormEvWitness_genuine`,
      `colNorm_count_neg_one`, `colNormEv_not_colNorm`, `colNormEvWitness_target`. Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 858/858 at e24821f (code commit 59126e2), all 12
      `H5ColNormEvAudit` theorems verified.

G58–G61 written by the formalize task on 2026-11-15 (after G57 was ticked). G51–G57 guarded every E-free row of the
smoothed route by `1 ≤ L`. The `count` and `defect` rows are still stated with `(1 + L) ^ 2`, while the paper
(Weyl count, Lemma 7.1′) states them as `C · L²`; and every witness so far has fixed truncation sizes, so the
count row has only been exercised on bounded data. G58–G61 restate those two rows in the paper's form, record
that the restatement is equivalent (not a weakening), exercise the rows on unbounded truncations, and check that
`lowCount` is an independent input. None claims a row is proved for the actual operator.

- [x] G58. `SteklovAudit/H5EvPaperScale.lean` (imports `SteklovAudit.H5EventualTarget`): `structure
      H5bPaperScaleInputs` = `H5bSmoothedEvInputs` (G51, copy field names from `H5EventualRows.lean`) with
      `count : ∀ ε γ L, 1 ≤ L → (Fintype.card (Fin (nA ε γ L)) : ℝ) ≤ Cm ε γ * L ^ 2` and
      `defect : ∀ ε γ L, 1 ≤ L → hs2 (D ε γ L).K ≤ Ck ε γ ^ 2 * L ^ 2` (the paper's `C L²` form). Lemma
      `sq_le_one_add_sq (h : 1 ≤ L) : L ^ 2 ≤ (1 + L) ^ 2` (nlinarith); `paperScale_count`, `paperScale_defect`:
      the G51 rows (`mul_le_mul_of_nonneg_left` with `hCm` / `sq_nonneg`); def `toSmoothedEv`;
      `h5b_of_paperScale`: `H5bTarget` for `∑ i, W.P.φ ((W.D ε γ L).a i - L)` and the model analogue, via
      `h5b_of_smoothedEv`. Docstring: neither row is proved. Theorem names: `sq_le_one_add_sq`,
      `paperScale_count`, `paperScale_defect`, `toSmoothedEv_nA` (rfl), `h5b_of_paperScale`.
      Ticked by the formalize task 2026-11-15: STATUS PASS 863/863 at 96b118a (code commit 96b118a),
      `H5EvPaperScale` compiled.
- [x] G59. `SteklovAudit/H5EvPaperScaleAudit.lean`: the converse, so the F table can say the paper form is an
      exact restatement up to constants. `one_add_sq_le_four_sq (h : 1 ≤ L) : (1 + L) ^ 2 ≤ 4 * L ^ 2`
      (nlinarith); def `ofSmoothedEv : H5bSmoothedEvInputs → H5bPaperScaleInputs` with `Cm' = 4 * Cm` (nonneg
      by `positivity`/`mul_nonneg`) and `Ck' = 2 * Ck` (`(2 * Ck) ^ 2 * L ^ 2 = Ck ^ 2 * (4 * L ^ 2)` by `ring`);
      `ofSmoothedEv_nA` (rfl). F table text: the count and defect rows of the smoothed route may be stated
      in the paper's `C L²` form for `L ≥ 1`; the two forms are equivalent (constants change by 4 and 2).
      Theorem names: `one_add_sq_le_four_sq`, `ofSmoothedEv_nA` (def `ofSmoothedEv`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5EvPaperScaleAudit.lean` (uncompiled at
      push, commit b750b5c): def `ofSmoothedEv`; theorems `one_add_sq_le_four_sq`, `smoothedEv_count_paper`,
      `smoothedEv_defect_paper`, `ofSmoothedEv_nA`, `ofSmoothedEv_Cm`, `ofSmoothedEv_Ck`,
      `ofSmoothedEv_target`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-15: STATUS PASS 870/870 at 54169c0 (code commit b750b5c), all 7
      `H5EvPaperScaleAudit` theorems verified.
- [x] G60. `SteklovAudit/H5EvGrowWitness.lean`: the count row exercised on unbounded truncations.
      `growD (n : ℕ) : Data (Fin n) (Fin n)` with `a i = b i = (i : ℝ)`, `J i j = if i = j then 1 else 0`;
      `growD_rowNorm`, `growD_colNorm` (`Finset.sum_ite_eq` / `Finset.sum_ite_eq'`), `growD_K : (growD n).K i j = 0`
      (unfold `Data.K` as `rnD_K` did; diagonal `J` and `a = b`). `growWitness : H5bPaperScaleInputs` with
      `nA = nB = ⌊L⌋₊`, `m1 = m2 = 0` (`zero_vanish`), `Cm = 1` (`Nat.floor_le`, then `L ≤ L ^ 2` for `1 ≤ L`),
      `Ck = 0`, `τ = 0`, `Cτ = 0` (`zeroRate`), `P = arctanProfile`, `Φ = 2`, `c M = |M| + 1` (the filter
      `{i | (i : ℝ) ≤ M}` injects into `Finset.range (⌊|M|⌋₊ + 1)`; if this pushes the file past ~120 lines,
      move `lowCount` and the witness to G61 and keep only the `growD` lemmas here). Theorems
      `growWitness_unbounded : ∀ N : ℕ, ∃ L, 1 ≤ L ∧ N ≤ growWitness.nA 0 0 L` and `growWitness_target`
      (from `h5b_of_paperScale`). Theorem names as above (defs `growD`, `growWitness`).
      Written by the formalize task 2026-11-15 in `SteklovAudit/H5EvGrowWitness.lean` (uncompiled at push,
      commit 8bc8e58), full item (witness kept here, not moved to G61): defs `growD` (`a i = b i = i.val`,
      identity `J`), `growWitness` (`Cm = 1`, `Ck = 0`, `τ = 0`, `m1 = m2 = 0`, `c M = |M| + 1`); theorems
      `growD_rowNorm`, `growD_colNorm`, `growD_K`, `growD_hs2K`, `growD_rowMiss`, `growD_colMiss`,
      `growD_count`, `growD_lowCount`, `growWitness_unbounded`, `growWitness_target`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 880/880 at 2ddc845 (fix commit 407140a), all 10
      `H5EvGrowWitness` theorems verified.
- [x] G61. `SteklovAudit/H5EvLowCountIndep.lean`: `lowCount` is not implied by the other rows. `flatD (n : ℕ) :
      Data (Fin n) (Fin n)` with `a = b = 0` and `J` diagonal (as `growD`); with `n = ⌊L⌋₊` it satisfies
      normalization, the paper-scale `count` (`Cm = 1`), `defect` (`Ck = 0`), `tail` (`τ = 0`), `ha`, `hb`
      (state these as `flatD_rowNorm`, `flatD_colNorm`, `flatD_count`, `flatD_K`), but
      `flatD_not_lowCount : ¬ ∃ c : ℝ, ∀ L : ℝ, 1 ≤ L →
        ((Finset.univ.filter fun i => (flatD ⌊L⌋₊).a i ≤ 0).card : ℝ) ≤ c` (the filter is all of `Fin ⌊L⌋₊`;
      take `L = ⌈c⌉₊ + 2` and use `Nat.floor_natCast` / `Nat.le_ceil`). F table text: the low-energy count row
      is an independent input, not a consequence of the Weyl-type count row. Theorem names as above.
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5EvLowCountIndep.lean` (uncompiled at push,
      commit 5184686): def `flatD`; theorems `flatD_rowNorm`, `flatD_colNorm`, `flatD_K`, `flatD_hs2K`,
      `flatD_count`, `flatD_ha`, `flatD_hb`, `flatD_filter_univ`, `flatD_not_lowCount`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 889/889 at 63510e6 (code commit 5184686), all 9
      `H5EvLowCountIndep` theorems verified.

G62–G65 written by the formalize task on 2026-11-16 (after G61 was ticked). Target row: "Low-energy defect bound
κ". In `h5b_of_inputs` the low part of `cumulative_transfer_bound` is `lam · √(κ2 · mLo)` with `κ2` L-uniform and
`mLo = Cm (1 + L)²`, which is why every route so far needs an L-uniform `lowCount`. If the low-energy mass is kept
as its own bound `mLo`, then `lam → 0` already makes the low term `o(L)` when `κ2` and `mLo` grow linearly in `L`.
G62–G65 replace the L-uniform low row by a strictly weaker L-dependent one, reduce it to a low-energy count
`≤ c(M) · (1 + |L|)`, and check strictness with G61's `flatD`. None claims a row is proved for the actual operator.

- [x] G62. `SteklovAudit/H5LowLinear.lean` (imports `SteklovAudit.H5Compare`): `structure H5bLowLInputs (E Emod :
      ℝ → ℝ → ℝ → ℝ)` = the fields of `H5bInputs` (copy names and types from `H5Compare.lean`: `nA` … `tailVanish`,
      `Λ0`, `hΛ0`, `lam`, `hlam`, `lipHi`, `lipLo`) with `κ2`, `lowDefect`, `lamVanish` replaced by
      `κ2 : ℝ → ℝ → ℝ → ℝ → ℝ`, `lowDefect : ∀ ε γ M L, hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).K)
      ≤ κ2 ε γ M L`, `mLo : ℝ → ℝ → ℝ → ℝ → ℝ`, `lowMass : ∀ ε γ M L, hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j)
      (D ε γ L).J) ≤ mLo ε γ M L`, and `lowVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L,
      L₀ ≤ L → lam ε γ M L * Real.sqrt (κ2 ε γ M L * mLo ε γ M L) ≤ η * L`. `h5b_of_lowLInputs : H5bTarget E Emod`:
      copy the proof of `h5b_of_inputs`, passing `κ2 ε γ M L` and `mLo ε γ M L` (with `lowMass`) as the low
      arguments of `cumulative_transfer_bound` (drop `e2`); the `hlow` step uses `lowVanish` at `η / 2` and
      `discVanish` at `η / 2`. Docstring: no row is proved. Theorem names: `h5b_of_lowLInputs`.
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5LowLinear.lean` (uncompiled at push,
      commit 6881d86): structure `H5bLowLInputs`; theorem `h5b_of_lowLInputs`. Next run: tick if STATUS shows
      it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 890/890 at 196b1f3 (code commit 6881d86),
      `H5LowLinear.h5b_of_lowLInputs` verified.
- [x] G63. `SteklovAudit/H5LowLinearAudit.lean`: G62 is no stronger than F1. `low_term_le (hlam : 0 ≤ lam)
      (hs : 0 ≤ s) (hL : 1 ≤ L) (h : lam * (4 * (s + 1)) ≤ η) : lam * (s * (1 + L)) ≤ η * L` (the `k2`–`k4`
      steps of `h5b_of_inputs`); def `ofInputs : H5bInputs E Emod → H5bLowLInputs E Emod` with `κ2 _ _ M _ :=
      H.κ2 ε γ M`, `mLo _ _ _ L := H.Cm ε γ * (1 + L) ^ 2` (`lowMass` from `hs2_mask_le` and `(H.pde ε γ L).mass`),
      `lowVanish` from `lamVanish` at `η / (4 * (s + 1))` with `s = √(κ2 · Cm)` and the identity
      `√(κ2 · (Cm (1 + L)²)) = √(κ2 · Cm) · (1 + L)` (the `e2` step of `h5b_of_inputs`), threshold `max L₁ 1`.
      Theorem names: `low_term_le`, `ofInputs_nA` (rfl), `ofInputs_target` (`h5b_of_lowLInputs (ofInputs H)`).
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5LowLinearAudit.lean` (uncompiled at push,
      commit aa511bc): def `ofInputs`; theorems `low_term_le`, `ofInputs_nA`, `ofInputs_κ2`, `ofInputs_mLo`,
      `ofInputs_target`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 895/895 at 4100856 (code commit aa511bc), all 5
      `H5LowLinearAudit` theorems verified.
- [x] G64. `SteklovAudit/H5LowLinearRows.lean` (imports `SteklovAudit.H5LowLinear`, `SteklovAudit.H5LowCount`,
      `SteklovAudit.H5LowMass`): the G62 low rows from a linearly growing low count. For `D : Data ι κ` with
      Bessel rows, `0 ≤ a`, `0 ≤ b`, and `card (filter (a i ≤ M)) ≤ c`: `lowMass_le_count` (`low_mask_le_rows`
      then `rows_le_card`) and `lowDefect_le_count : hs2 (mask low K) ≤ M ^ 2 * c` (`lowDefect_of_lowMass`).
      Scalar step `lowVanish_of_linear (hc : 0 ≤ C) (hlam : ∀ L, 0 ≤ lam L) (hv : ∀ η > 0, ∃ L₀, ∀ L ≥ L₀,
      lam L ≤ η) : ∀ η > 0, ∃ L₀, ∀ L ≥ L₀, lam L * Real.sqrt ((M ^ 2 * (C * (1 + |L|))) * (C * (1 + |L|))) ≤ η * L`
      (the root is `|M| * C * (1 + |L|)` by `Real.sqrt_mul_self`/`Real.sqrt_sq` after `ring_nf`; for `L ≥ 1`,
      `1 + |L| ≤ 2 L`; use `hv` at `η / (2 * (|M| * C + 1))`). Theorem names: `lowMass_le_count`,
      `lowDefect_le_count`, `lowVanish_of_linear`. F table text: the low-energy row needs only a low count
      `≤ c(M) · (1 + |L|)` together with `lam → 0`, not an L-uniform count.
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5LowLinearRows.lean` (uncompiled at push,
      commit ad580cf): theorems `lowMass_le_count`, `lowDefect_le_count`, `lowRows_of_linearCount`,
      `sqrt_linear_rows`, `lowVanish_of_linear`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 900/900 at d4c2258 (code commit ad580cf), all 5
      `H5LowLinearRows` theorems verified.
- [x] G65. `SteklovAudit/H5LowLinearStrict.lean` (imports `SteklovAudit.H5EvLowCountIndep`): the linear low
      count is strictly weaker than the L-uniform `lowCount`. `flatD_linearCount : ∀ M L : ℝ, ((Finset.univ.filter
      fun i => (flatD ⌊L⌋₊).a i ≤ M).card : ℝ) ≤ 1 * (1 + |L|)` (card of a filter ≤ `Fintype.card (Fin ⌊L⌋₊) =
      ⌊L⌋₊`; `Nat.floor_le` for `0 ≤ L`, `Nat.floor_eq_zero`/`Nat.floor_of_nonpos` for `L < 0`; `le_abs_self`),
      and `linearCount_strictly_weaker`: the conjunction of `flatD_linearCount` with G61's `flatD_not_lowCount`.
      F table text: on `flatD` the G64 low row holds with `c = 1` while no L-uniform `c` exists. Theorem
      names: `flatD_linearCount`, `linearCount_strictly_weaker`.
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5LowLinearStrict.lean` (uncompiled at push,
      commit 1cee561): theorems `floor_le_one_add_abs`, `flatD_filter_card_le`, `flatD_linearCount`,
      `flatD_linearCount_exists`, `linearCount_strictly_weaker`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 905/905 checked at e815998 (status commit
      544bb40; e815998 fixed 1cee561), all 5 `H5LowLinearStrict` theorems verified.

G66–G70 written by the formalize task on 2026-11-16 (after G65 was ticked). Target row: "High-energy defect tail
τ(M), σ(M) → 0". In `H5bLowLInputs` (G62) the tail bound `tail : hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M`
must hold for every `L` (including `L < 1` and every bounded range of `L`), and the high term of
`cumulative_transfer_bound` is `Λ0 · √(τ · mHi)` with `mHi = Cm (1 + L)²` fixed by `pde.mass`. Only large `L`
matters for (7.29). G66–G70 let the tail depend on `L` with eventual vanishing, check that this is no stronger and
strictly weaker, then keep the high-energy mass as its own bound (the mirror of G62). None claims a row is proved for
the actual operator.

- [x] G66. `SteklovAudit/H5TailEv.lean` (imports `SteklovAudit.H5LowLinear`): `structure H5bTailEvInputs (E Emod :
      ℝ → ℝ → ℝ → ℝ)` = the fields of `H5bLowLInputs` (copy names and types from `H5LowLinear.lean`) with `τ`,
      `tail`, `tailVanish` replaced by `τ : ℝ → ℝ → ℝ → ℝ → ℝ`, `tail : ∀ ε γ M L, 1 ≤ L → hs2 (mask (hiE (D ε γ L)
      M) (D ε γ L).K) ≤ τ ε γ M L`, and `tailVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ → ∃ M L₀ : ℝ, ∀ L,
      L₀ ≤ L → τ ε γ M L ≤ δ`. `h5b_of_tailEv : H5bTarget E Emod`, proved directly (not via
      `little_o_of_vanishing_tail`, whose tail is L-free): `key` as in `h5b_of_lowLInputs` with `H.τ ε γ M L`
      (for `1 ≤ L`); given `η`, set `C := H.Λ0 ε γ * √(H.Cm ε γ)` and `δ := η / (4 * (C + 1))`; take `M, L₁` from
      `tailVanish` at `δ ^ 2` (then `√τ ≤ δ` by `Real.sqrt_le_sqrt` + `Real.sqrt_sq`), `L₂` from `lowVanish` at `M`,
      `η / 4`, `L₃` from `discVanish` at `η / 4`, threshold `max (max 1 L₁) (max L₂ L₃)`; finish with
      `1 + L ≤ 2 * L`, `C * δ ≤ η / 4` (`div_le_iff₀`/`le_div_iff₀` or `field_simp`, then `nlinarith`) and
      `linarith`. Docstring: no row is proved. Theorem names: `h5b_of_tailEv`.
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5TailEv.lean` (uncompiled at push,
      commit 6e7681f): structure `H5bTailEvInputs`; theorem `h5b_of_tailEv`. Next run: tick if STATUS shows
      it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 906/906 at abf03c8, `H5TailEv.h5b_of_tailEv`
      verified.
- [x] G67. `SteklovAudit/H5TailEvAudit.lean`: G66 is no stronger than G62. def `ofLowL : H5bLowLInputs E Emod →
      H5bTailEvInputs E Emod` with `τ ε γ M _ := H.τ ε γ M`, `tail ε γ M L _ := H.tail ε γ M L`, `tailVanish` from
      `H.tailVanish` with `L₀ = 0` (any `L₀`), all other fields copied. Theorem names: `ofLowL_nA` (rfl),
      `ofLowL_τ` (rfl), `ofLowL_target` (`h5b_of_tailEv (ofLowL H)`).
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5TailEvAudit.lean` (uncompiled at push,
      commit 25f01d2): def `ofLowL`; theorems `ofLowL_nA`, `ofLowL_τ`, `ofLowL_target`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 909/909 at f9028e7, all 3 `H5TailEvAudit`
      theorems verified.
- [x] G68. `SteklovAudit/H5TailEvStrict.lean`: the eventual tail row is strictly weaker than the L-uniform one, as
      a statement about the row's shape (a function `t M L` standing for `hs2 (mask (hiE _ M) K)` at scale `L`).
      `bumpTail (M L : ℝ) : ℝ := if 1 ≤ L ∧ L < 2 ∧ M < 1 / (2 - L) then 1 else 0` (unit defect mass at energy
      `1 / (2 - L)` for `L ∈ [1, 2)`, none for `L ≥ 2`). `bumpTail_eventual : ∀ δ > 0, ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L →
      bumpTail M L ≤ δ` (`M = 0`, `L₀ = 2`, `if_neg`); `bumpTail_not_uniform : ¬ ∃ τ : ℝ → ℝ, (∀ M L, 1 ≤ L →
      bumpTail M L ≤ τ M) ∧ ∀ δ > 0, ∃ M, τ M ≤ δ` (at `δ = 1/2` with its `M`, take `L = 2 - 1 / (|M| + 1)`, so
      `1 ≤ L < 2` and `1 / (2 - L) = |M| + 1 > M`; `bumpTail M L = 1 ≤ τ M ≤ 1/2`, contradiction). Theorem names:
      `bumpTail_eventual`, `bumpTail_not_uniform`, `tailEv_strictly_weaker` (the conjunction). F table text: the
      tail row needs only `τ(M, L) → 0` along `L → ∞` for some `M`, not a bound uniform in `L ≥ 1`.
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5TailEvStrict.lean` (uncompiled at push,
      commit b45cc57): def `bumpTail`; theorems `bumpTail_eventual`, `bumpTail_not_uniform`,
      `tailEv_strictly_weaker`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 912/912 at 4583e19, all 3 `H5TailEvStrict`
      theorems verified.
- [x] G69. `SteklovAudit/H5HiLinear.lean` (imports `SteklovAudit.H5TailEv`): mirror of G62 for the high part.
      `structure H5bHiLInputs` = `H5bTailEvInputs` with `tailVanish` replaced by `mHi : ℝ → ℝ → ℝ → ℝ → ℝ`,
      `hiMass : ∀ ε γ M L, hs2 (mask (hiE (D ε γ L) M) (D ε γ L).J) ≤ mHi ε γ M L` and `hiVanish : ∀ ε γ : ℝ,
      0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ → ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → Λ0 ε γ * Real.sqrt (τ ε γ M L * mHi ε γ M L) ≤
      δ * L` (`lowVanish` stays, for every `M`). `h5b_of_hiLInputs : H5bTarget E Emod`: pass `mHi ε γ M L` with `hiMass` as the high mass argument
      of `cumulative_transfer_bound` (drop `e1`, `e3`), then pick `M, L₁` from `hiVanish` at `η / 3`, `L₂` from `lowVanish` at that `M`
      and `η / 3`, `L₃` from `discVanish` at `η / 3`, threshold `max (max 1 L₁) (max L₂ L₃)`. Docstring: no row is proved. Theorem names: `h5b_of_hiLInputs`.
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5HiLinear.lean` (uncompiled at push,
      commit 2b9645a): structure `H5bHiLInputs`; theorem `h5b_of_hiLInputs`. Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-16: STATUS PASS 913/913 at da786df,
      `H5HiLinear.h5b_of_hiLInputs` verified.
- [x] G70. `SteklovAudit/H5HiLinearAudit.lean`: G69 is no stronger than G66. def `ofTailEv : H5bTailEvInputs E Emod
      → H5bHiLInputs E Emod` with `mHi _ _ _ L := H.Cm ε γ * (1 + L) ^ 2` (`hiMass` from `hs2_mask_le` and
      `(H.pde ε γ L).mass`), `hiVanish` from `tailVanish` at `(δ / (4 * (C + 1))) ^ 2` with
      `C = Λ0 · √Cm` and `√(τ · (Cm (1 + L)²)) = √τ · √Cm · (1 + L)` (the `e1` step), threshold `max L₀ 1`.
      Theorem names: `ofTailEv_nA` (rfl), `ofTailEv_mHi` (rfl), `ofTailEv_target`. F table text: the high-energy
      row may be stated as one product bound `Λ0 · √(τ · mHi) = o(L)` at a single `M`.
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5HiLinearAudit.lean` (uncompiled at push,
      commit 5e6e0de): def `ofTailEv`; theorems `hi_term_le`, `ofTailEv_nA`, `ofTailEv_mHi`,
      `ofTailEv_target`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-17: STATUS PASS 917/917 at 7df4c11, all 4 `H5HiLinearAudit`
      theorems verified.

G71–G74 written by the formalize task on 2026-11-17 (after G70 was ticked). G71 shows the G69 high row is strictly
weaker than G66's tail row; G72–G74 merge `hiVanish` and `lowVanish` into one joint row that needs the low-energy
term to vanish only at the split energy `M` actually chosen, not at every `M`, and check that this is no stronger
and strictly weaker. None claims a row is proved for the actual operator.

- [x] G71. `SteklovAudit/H5HiLinearStrict.lean`: the G69 high row is strictly weaker than the G66 tail row, as a
      statement about row shapes (`t M L` for the tail bound τ, `m M L` for the high mass mHi). Take
      `constTail (M L : ℝ) : ℝ := 1` (a defect tail that never decays) and `unitMass (M L : ℝ) : ℝ := 1` (high-energy
      mass `O(1)`, not `O(L²)`). `constTail_hiVanish : ∀ Λ : ℝ, 0 ≤ Λ → ∀ δ : ℝ, 0 < δ → ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L →
      Λ * Real.sqrt (constTail M L * unitMass M L) ≤ δ * L` (`M = 0`, `L₀ = Λ / δ`; `Real.sqrt_one` via `simp`, then
      `div_le_iff₀` / `le_div_iff₀` and `nlinarith`); `constTail_not_tailEv : ¬ ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → constTail M L
      ≤ 1 / 2` (apply at `L = L₀`, `norm_num`). Theorem names: `constTail_hiVanish`, `constTail_not_tailEv`,
      `hiL_strictly_weaker` (the conjunction at `Λ = 1`). F table text: the high-energy row can hold with no tail decay
      at all if the high-energy mass is `o(L²)`.
      Written by the formalize task 2026-11-17 in `SteklovAudit/H5HiLinearStrict.lean` (uncompiled at push,
      commit e8f9d1c): defs `constTail`, `unitMass`; theorems `constTail_hiVanish`, `constTail_not_tailEv`,
      `hiL_strictly_weaker`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-17: STATUS PASS 920/920 at be92558, all 3 `H5HiLinearStrict`
      theorems verified.
- [x] G72. `SteklovAudit/H5Joint.lean` (imports `SteklovAudit.H5HiLinear`): `structure H5bJointInputs (E Emod : ℝ →
      ℝ → ℝ → ℝ)` = the fields of `H5bHiLInputs` (copy names and types from `H5HiLinear.lean`) with `hiVanish` and
      `lowVanish` replaced by one field `jointVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ M L₀ : ℝ, ∀ L,
      L₀ ≤ L → Λ0 ε γ * Real.sqrt (τ ε γ M L * mHi ε γ M L) + lam ε γ M L * Real.sqrt (κ2 ε γ M L * mLo ε γ M L) ≤
      η * L`. `h5b_of_jointInputs : H5bTarget E Emod`: `key` exactly as in `h5b_of_hiLInputs`; take `M, L₁` from
      `jointVanish` at `η / 2`, `L₂` from `discVanish` at `η / 2`, threshold `max (max 1 L₁) L₂`, finish with
      `linarith`. Docstring: no row is proved; `disc` stays its own row. Theorem names: `h5b_of_jointInputs`.
      Written by the formalize task 2026-11-17 in `SteklovAudit/H5Joint.lean` (uncompiled at push,
      commit f4ad4df): structure `H5bJointInputs`; theorem `h5b_of_jointInputs`. Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-17: STATUS PASS 921/921 at c474cd4,
      `H5Joint.h5b_of_jointInputs` verified.
- [x] G73. `SteklovAudit/H5JointAudit.lean` (imports `SteklovAudit.H5Joint`): G72 is no stronger than G69. def
      `ofHiL : H5bHiLInputs E Emod → H5bJointInputs E Emod`, all fields copied, `jointVanish` from `H.hiVanish` at
      `η / 2` (giving `M, L₁`), then `H.lowVanish` at that `M` and `η / 2` (giving `L₂`), threshold `max L₁ L₂`,
      `linarith` with `η / 2 * L + η / 2 * L = η * L` (`ring`). Theorem names: `ofHiL_nA` (rfl), `ofHiL_τ` (rfl),
      `ofHiL_target` (`h5b_of_jointInputs (ofHiL H)`).
      Written by the formalize task 2026-11-17 in `SteklovAudit/H5JointAudit.lean` (uncompiled at push,
      commit 37418b3): def `ofHiL`; theorems `ofHiL_nA`, `ofHiL_τ`, `ofHiL_target`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-17: STATUS PASS 927/927 at 08e5bc2, all 3 `H5JointAudit`
      theorems verified.
- [x] G74. `SteklovAudit/H5JointStrict.lean`: the joint row is strictly weaker than "high row at some `M` and low
      row at every `M`", as a statement about row shapes. `hiZero (M L : ℝ) : ℝ := 0` and `loBad (M L : ℝ) : ℝ :=
      if 0 < M then L else 0` (the low-energy term is `o(L)` only for the split energy `M ≤ 0`). `joint_holds : ∀ η :
      ℝ, 0 < η → ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → hiZero M L + loBad M L ≤ η * L` (`M = 0`, `L₀ = 0`, `simp`, `positivity` or
      `nlinarith`); `lowEvery_fails : ¬ ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → loBad M L ≤ η * L` (at `M = 1`,
      `η = 1 / 2`, take `L = max L₀ 1`, `if_pos`, `linarith`). Theorem names: `joint_holds`, `lowEvery_fails`,
      `joint_strictly_weaker` (the conjunction). F table text: the low-energy row is needed only at the split
      energy used for the high row.
      Written by the formalize task 2026-11-17 in `SteklovAudit/H5JointStrict.lean` (commit acfd0b3): theorems
      `joint_holds`, `lowEvery_fails`, `joint_strictly_weaker`.
      Ticked by the formalize task 2026-11-17: STATUS PASS 927/927 at 08e5bc2, all 3 `H5JointStrict`
      theorems verified.

G75–G78 written by the formalize task on 2026-11-17 (after G73 and G74 were ticked). G75 checks whether the joint form
inherits the F2 caveat (`cutoff`/`discVanish` alone can carry the target when `D` is unconstrained); G76 shows the rows
other than `cutoff`/`disc` carry no information about `E − Emod`; G77–G78 weaken the joint row by letting the split
energy depend on `L`, and check that this is no stronger and strictly weaker. None claims a row is proved for the actual
operator.

- [x] G75. `SteklovAudit/H5JointIff.lean` (imports `SteklovAudit.H5Joint`): the F2 audit for the joint form.
      `noncomputable def jointOfTarget (h : H5bTarget E Emod) : H5bJointInputs E Emod` with `nA = nB = 0`,
      `D := fun _ _ _ => emptyData` (`H5Compare.emptyData`), `disc ε γ L := |E ε γ L - Emod ε γ L|` (`cutoff` by
      `simp`), every other function `0`, `pde` copied from how `H5Compare.inputsOfTarget` builds it; `discVanish` is
      `h` itself (unfold `H5bTarget`), `jointVanish` with `M = 0`, `L₀ = 0` (`simp`, then `positivity`/`nlinarith`
      using `0 ≤ L`). Theorem names: `jointOfTarget` (def), `jointInputs_iff_target : Nonempty (H5bJointInputs E Emod)
      ↔ H5bTarget E Emod` (← by `⟨jointOfTarget h⟩`, → by `h5b_of_jointInputs`). F table text: with `D` unconstrained the
      joint form, like F1, is equivalent to the target; the caveat sits in the `cutoff`/`disc` row.
      Ticked by the formalize task 2026-11-17: STATUS PASS 929/929 at 6149898, `H5JointIff.jointInputs_iff_target`
      and `H5JointIff.jointInputs_nonempty` verified.
- [x] G76. `SteklovAudit/H5JointCutoffNeeded.lean`: the `cutoff` row is the only link to `E`. `sq_target_fails : ¬
      H5bTarget (fun _ _ L => L ^ 2) (fun _ _ _ => 0)` (unfold `H5bTarget`; apply at `ε = γ = η = 1`, take
      `L = max L₀ 2`, then `L ^ 2 ≤ L` contradicts `2 ≤ L` via `nlinarith`; `abs_of_nonneg` / `sq_nonneg` for the
      absolute value); `zero_rows_hold : ∀ η : ℝ, 0 < η → ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → (0 : ℝ) * Real.sqrt (0 * 0) + 0 *
      Real.sqrt (0 * 0) ≤ η * L` (`M = 0`, `L₀ = 0`, `simp`, `positivity`). Theorem names: `sq_target_fails`,
      `zero_rows_hold`, `cutoff_row_needed` (the conjunction). F table text: all rows except `cutoff`/`disc` can hold
      with zero functions while `E − Emod` grows like `L²`, so they constrain `E` only through `cutoff`.
      Written by the formalize task 2026-11-17 in `SteklovAudit/H5JointCutoffNeeded.lean` (uncompiled at push,
      commit 49e8cb1): theorems `sq_target_fails`, `zero_rows_hold`, `cutoff_row_needed`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 932/932 at ffda128, all 3 `H5JointCutoffNeeded`
      theorems verified.
- [x] G77. `SteklovAudit/H5JointSel.lean` (imports `SteklovAudit.H5Joint`): the split energy may depend on `L`.
      `structure H5bJointSelInputs (E Emod)` = the fields of `H5bJointInputs` (copy names and types from
      `H5Joint.lean`) with `jointVanish` replaced by `selVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ (Msel
      : ℝ → ℝ) (L₀ : ℝ), ∀ L, L₀ ≤ L → Λ0 ε γ * Real.sqrt (τ ε γ (Msel L) L * mHi ε γ (Msel L) L) + lam ε γ (Msel L)
      L * Real.sqrt (κ2 ε γ (Msel L) L * mLo ε γ (Msel L) L) ≤ η * L`. `h5b_of_jointSelInputs : H5bTarget E Emod`:
      `key` exactly as in `h5b_of_jointInputs` (it holds for every `M` and `L`), applied at `M = Msel L`; thresholds
      as in G72. Docstring: no row is proved. Theorem names: `h5b_of_jointSelInputs`.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5JointSel.lean` (uncompiled at push,
      commit 5af98ca): structure `H5bJointSelInputs`; theorem `h5b_of_jointSelInputs`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 933/933 at 9693187,
      `H5JointSel.h5b_of_jointSelInputs` verified.
- [x] G78. `SteklovAudit/H5JointSelAudit.lean` (imports `SteklovAudit.H5JointSel`): G77 is no stronger than G72 and
      strictly weaker as row shapes. def `ofJoint : H5bJointInputs E Emod → H5bJointSelInputs E Emod` (all fields
      copied, `Msel := fun _ => M`); theorems `ofJoint_τ` (rfl), `ofJoint_target`. Row shapes: `late (M L : ℝ) : ℝ :=
      if L ≤ M then 0 else L`; `sel_holds : ∀ η : ℝ, 0 < η → ∃ (Msel : ℝ → ℝ) (L₀ : ℝ), ∀ L, L₀ ≤ L → late (Msel L) L
      ≤ η * L` (`Msel = id`, `L₀ = 0`, `if_pos le_rfl`, `positivity`); `const_fails : ¬ ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → late M
      L ≤ 1 / 2 * L` (take `L = max L₀ (M + 1) ` and also `L ≥ 1`: use `max (max L₀ (M + 1)) 1`, `if_neg`, `linarith`).
      Theorem names: `ofJoint_τ`, `ofJoint_target`, `sel_holds`, `const_fails`, `sel_strictly_weaker`. F table text:
      the split energy in (7.29) may be chosen as a function of `L`.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5JointSelAudit.lean` (uncompiled at push,
      commit 0f789c1): defs `ofJoint`, `late`; theorems `ofJoint_τ`, `ofJoint_target`, `sel_holds`,
      `const_fails`, `sel_strictly_weaker`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 938/938 at dd66421, all 5 `H5JointSelAudit`
      theorems verified.

G79–G82 written by the formalize task on 2026-11-18 (after G78 was ticked). G79 runs the F2 audit on the selector form
(G77); G80 states the selector row directly on the masked defect and mass `hs2` quantities at the chosen split energy,
so the four rows `tail`, `hiMass`, `lowDefect`, `lowMass` (and their bounding functions τ, mHi, κ2, mLo) are no longer
separate inputs; G81–G82 check that G80 is no stronger than G77 and inherits the F2 caveat. None claims a row is proved
for the actual operator.

- [x] G79. `SteklovAudit/H5JointSelIff.lean` (imports `SteklovAudit.H5JointSelAudit` and `SteklovAudit.H5JointIff`):
      the F2 audit for the selector form. `selInputs_iff_target : Nonempty (H5bJointSelInputs E Emod) ↔ H5bTarget E
      Emod` (← by `⟨H5JointSelAudit.ofJoint (H5JointIff.jointOfTarget h)⟩`, → by `fun ⟨H⟩ => h5b_of_jointSelInputs
      H`); `selInputs_nonempty_zero : Nonempty (H5bJointSelInputs (fun _ _ _ => 0) (fun _ _ _ => 0))` (target holds
      for `E = Emod`: unfold `H5bTarget`, `simp`, `⟨0, fun L hL => by positivity⟩` or `mul_nonneg`). Docstring: with
      `D` unconstrained the selector form is equivalent to the target; the caveat sits in the `cutoff`/`disc` row.
      Theorem names: `selInputs_iff_target`, `selInputs_nonempty_zero`.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5JointSelIff.lean` (uncompiled at push):
      theorems `selInputs_iff_target`, `selInputs_nonempty_zero`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 940/940 at 6e2a9f5, both `H5JointSelIff` theorems
      verified.
- [x] G80. `SteklovAudit/H5SelDirect.lean` (imports `SteklovAudit.H5JointSel`): `structure H5bSelDirectInputs (E
      Emod)` = the fields of `H5bJointSelInputs` without `τ`, `tail`, `mHi`, `hiMass`, `κ2`, `lowDefect`, `mLo`,
      `lowMass`, and with `selVanish` replaced by `directVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ (Msel :
      ℝ → ℝ) (L₀ : ℝ), ∀ L, L₀ ≤ L → Λ0 ε γ * Real.sqrt (hs2 (mask (hiE (D ε γ L) (Msel L)) (D ε γ L).K) * hs2 (mask
      (hiE (D ε γ L) (Msel L)) (D ε γ L).J)) + lam ε γ (Msel L) L * Real.sqrt (hs2 (mask (fun i j => ¬ hiE (D ε γ L)
      (Msel L) i j) (D ε γ L).K) * hs2 (mask (fun i j => ¬ hiE (D ε γ L) (Msel L) i j) (D ε γ L).J)) ≤ η * L`.
      `h5b_of_selDirectInputs : H5bTarget E Emod`: as `h5b_of_jointSelInputs`, with `key` from
      `cumulative_transfer_bound` taking τ, mHi, κ2, mLo to be the four `hs2` values and all four bounds `le_rfl`
      (no `1 ≤ L` needed; keep the `max 1 _` threshold anyway). Docstring: no row is proved; `directVanish` bounds
      the defect matrix `K` and the overlap `J`, not `E − Emod`. Theorem names: `h5b_of_selDirectInputs`.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5SelDirect.lean` (uncompiled at push,
      commit 4cb2d7a): structure `H5bSelDirectInputs`; theorem `h5b_of_selDirectInputs`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 941/941 at 3243b9e,
      `H5SelDirect.h5b_of_selDirectInputs` verified.
- [x] G81. `SteklovAudit/H5SelDirectAudit.lean` (imports `SteklovAudit.H5SelDirect`): G80 is no stronger than G77.
      `noncomputable def ofSel : H5bJointSelInputs E Emod → H5bSelDirectInputs E Emod` (shared fields copied);
      `directVanish` from `selVanish` at the same `η` with the same `Msel` and threshold `max 1 L₀` (the `tail`
      field needs `1 ≤ L`): bound each `hs2` product by the `τ·mHi` / `κ2·mLo` product with `Real.sqrt_le_sqrt
      (mul_le_mul _ _ (hs2_nonneg _) (le_trans (hs2_nonneg _) _))`, then `mul_le_mul_of_nonneg_left` with `hΛ0` /
      `hlam`, then `linarith`. Theorem names: `ofSel` (def), `ofSel_Λ0` (rfl), `ofSel_target` (`h5b_of_selDirectInputs
      (ofSel H)`). F table text: the four bounding functions τ, mHi, κ2, mLo are needed only along the chosen split.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5SelDirectAudit.lean` (uncompiled at push,
      commit cce374e): def `ofSel`; theorems `ofSel_Λ0`, `ofSel_target`. Next run: tick if STATUS shows it
      compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 943/943 at f81bae4, both `H5SelDirectAudit`
      theorems verified.
- [x] G82. `SteklovAudit/H5SelDirectIff.lean` (imports `SteklovAudit.H5SelDirectAudit` and
      `SteklovAudit.H5JointSelIff`): the F2 audit for G80. `selDirect_iff_target : Nonempty (H5bSelDirectInputs E Emod)
      ↔ H5bTarget E Emod` (← via `ofSel` applied to the G79 witness, → by `h5b_of_selDirectInputs`). Theorem names:
      `selDirect_iff_target`. F table text: as with F1, G72 and G77, the content of the direct form sits in the
      `cutoff`/`disc` row once `D` is constrained by the operator.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5SelDirectIff.lean` (uncompiled at push,
      commit 38cad5b): theorems `selDirect_iff_target`, `selDirect_nonempty_zero` (satisfiability for
      `E = Emod = 0`). Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 945/945 at 7a28d02, both `H5SelDirectIff`
      theorems verified.

Items G83–G86 written by the formalize task on 2026-11-18 (no unchecked item was left in A–G).

- [x] G83. `SteklovAudit/H5SelMin.lean` (imports `SteklovAudit.H5SelDirect`): the PDE rows are not used by the
      direct form. `structure H5bSelMinInputs (E Emod)` = the fields of `H5bSelDirectInputs` (copy names and types
      from `H5SelDirect.lean`) without `Cm`, `Ck`, `hCm`, `pde`. `h5b_of_selMinInputs : H5bTarget E Emod` (the proof
      of `h5b_of_selDirectInputs` verbatim; it never uses those fields). `noncomputable def forgetPde :
      H5bSelDirectInputs E Emod → H5bSelMinInputs E Emod` (fields copied) and `forgetPde_target`. Theorem names:
      `h5b_of_selMinInputs`, `forgetPde_target`. F table text: in the direct form the rows (2.2) and Lemma 7.1′
      (`PDEInputs.mass`, `.defect`) are not separate inputs; they matter only as a means of proving `directVanish`.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5SelMin.lean` (uncompiled at push,
      commit 2e8988f): structure `H5bSelMinInputs`; def `forgetPde`; theorems `h5b_of_selMinInputs`,
      `forgetPde_Λ0`, `forgetPde_target`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 948/948 at c3b2271, all three `H5SelMin`
      theorems verified.
- [x] G84. `SteklovAudit/H5SelMinStrict.lean` (imports `SteklovAudit.H5SelMin`): G83 is strictly weaker than G80 on
      the data level. `bigD (L : ℝ) : Data (Fin 1) (Fin 1)` with `a = b = 0`, `J _ _ = (1 + |L|) ^ 2` (so `K = 0`).
      `bigD_selMin : H5bSelMinInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0)` with `nA = nB = 1`, `D _ _ L := bigD L`,
      `F = 0`, `disc = 0`, `Λ0 = lam = 0`, `Msel = fun _ => 0`, `L₀ = 0` (`directVanish`: `K = 0`, so every `hs2` of a
      masked `K` is 0; `simp [hs2, mask, Data.K]`). `bigD_not_pde : ∀ Cm Ck : ℝ, ¬ PDEInputs (bigD |Cm|) |Cm| Cm Ck`
      (`hs2 J = (1 + |Cm|) ^ 4 > Cm * (1 + |Cm|) ^ 2`; `nlinarith [abs_nonneg Cm, le_abs_self Cm]`). Theorem names:
      `bigD_selMin`, `bigD_not_pde`. F table text: an instance of the G83 rows whose overlap mass violates (2.2) at
      every constant.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5SelMinStrict.lean` (uncompiled at push,
      commit 529d782): defs `bigD`, `bigD_selMin`; theorems `bigD_K`, `bigD_selMin_target`, `hs2_bigD_J`,
      `bigD_not_pde`, `selMin_without_pde`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: run #371 at 529d782 verified 953/953 theorems (PASS; the run
      was marked failed only at the status-push step).
- [x] G85. `SteklovAudit/H5MaskSplit.lean` (imports `SteklovAudit.H5Compare`): two inequalities that merging the
      high and low parts needs. `hs2_mask_add_compl (p) [∀ i j, Decidable (p i j)] (M : ι → κ → ℝ) : hs2 (mask p M) +
      hs2 (mask (fun i j => ¬ p i j) M) = hs2 M` (unfold `hs2`, `mask`; `← Finset.sum_add_distrib`, `split_ifs <;>
      simp`); `sqrt_mul_add_sqrt_mul_le (0 ≤ a₁ a₂ b₁ b₂) : √(a₁ * b₁) + √(a₂ * b₂) ≤ √((a₁ + a₂) * (b₁ + b₂))` (`Real.le_sqrt`,
      `Real.sq_sqrt`, `Real.sqrt_mul_self`; the cross term by `nlinarith [sq_nonneg (√(a₁ * b₂) - √(a₂ * b₁))]`);
      `split_le_unsplit (p) (K J) : √(hs2 (mask p K) * hs2 (mask p J)) + √(hs2 (mask (¬p) K) * hs2 (mask (¬p) J)) ≤
      √(hs2 K * hs2 J)`. Theorem names: `hs2_mask_add_compl`, `sqrt_mul_add_sqrt_mul_le`, `split_le_unsplit`.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5MaskSplit.lean` (uncompiled at push,
      commit e305cf1): theorems `hs2_mask_add_compl`, `sqrt_mul_add_sqrt_mul_le` (implicit `a₁ a₂ b₁ b₂`),
      `split_le_unsplit`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 956/956 at 587302d, all three `H5MaskSplit`
      theorems verified.
- [x] G86. `SteklovAudit/H5GlobalLip.lean` (imports `SteklovAudit.H5SelMin`, `SteklovAudit.H5MaskSplit`): the
      uniform-Lipschitz case of the row "Lipschitz-type bounds Λ, λ". `structure H5bGlobalLipInputs (E Emod)` = `nA`,
      `nB`, `D`, `F`, `disc`, `cutoff`, `discVanish` (as in G83), `Λ : ℝ → ℝ → ℝ`, `hΛ : ∀ ε γ, 0 ≤ Λ ε γ`, `lip : ∀ ε γ L
      x y, |F ε γ L x - F ε γ L y| ≤ Λ ε γ * |x - y|`, `globalVanish : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀, ∀ L, L₀ ≤ L
      → Λ ε γ * √(hs2 (D ε γ L).K * hs2 (D ε γ L).J) ≤ η * L`. `noncomputable def toSelMin` (`Λ0 := Λ`, `lam _ _ _ _ :=
      Λ`, `lipHi`/`lipLo` from `lip`, `directVanish` with `Msel := fun _ => 0` and the same `L₀`, by `split_le_unsplit`,
      `mul_add`, `mul_le_mul_of_nonneg_left`); `h5b_of_globalLipInputs`. Docstring: the split energy is not needed when
      `F ε γ L` is Lipschitz uniformly in `L`; whether the smoothed counting function is, is the open row (Josiah to
      say); nothing is proved for the operator. Theorem names: `toSelMin_Λ0` (rfl), `h5b_of_globalLipInputs`.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5GlobalLip.lean` (uncompiled at push,
      commit e91c7dc): structure `H5bGlobalLipInputs`; def `toSelMin`; theorems `toSelMin_Λ0`,
      `h5b_of_globalLipInputs`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 958/958 at 33f1b69, both `H5GlobalLip`
      theorems verified.

Items G87–G90 written by the formalize task on 2026-11-18 (no unchecked item was left in A–G).

- [x] G87. `SteklovAudit/H5GlobalLipAudit.lean` (imports `SteklovAudit.H5GlobalLip`): the F2 audit for G86.
      `globalLip_nonempty_zero : Nonempty (H5bGlobalLipInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0))` (`nA = nB = 0`,
      `D` with `a = b = 0`, `J = 0`, `F = 0`, `disc = 0`, `Λ = 0`; every field by `simp`, `L₀ := 0`).
      `noncomputable def ofTarget (h : H5bTarget E Emod) : H5bGlobalLipInputs E Emod` (`nA = nB = 0`, `F = 0`,
      `disc ε γ L := |E ε γ L - Emod ε γ L|`, `discVanish := h` after `unfold H5bTarget at h`, `Λ = 0`, `globalVanish`
      with `L₀ := 0`: `0 * _ ≤ η * L` by `simp` then `positivity`/`nlinarith`). `globalLip_iff_target : Nonempty
      (H5bGlobalLipInputs E Emod) ↔ H5bTarget E Emod`. Theorem names: `globalLip_nonempty_zero`,
      `globalLip_iff_target`. F table text: as with F2, G72, G77 and G82, with `D` unconstrained the content of the
      global-Lipschitz form sits in the `cutoff`/`disc` row; `lip` and `globalVanish` carry content only once `D` is
      the operator's cutoff data.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5GlobalLipAudit.lean` (uncompiled at push,
      commit 893e025): def `ofTarget`; theorems `ofTarget_Λ`, `globalLip_iff_target`, `globalLip_nonempty_zero`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-18: STATUS PASS 961/961 at 1daa17c, all three
      `H5GlobalLipAudit` theorems verified.
- [x] G88. `SteklovAudit/H5GlobalLipStrict.lean` (imports `SteklovAudit.H5GlobalLip`): G86 is a special case of
      G83, not a replacement. `steepF : ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ L x => L * x`. `def steep_selMin : H5bSelMinInputs
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0)` with `nA = nB = 0` (all sums over `Fin 0` are empty; `lipHi`/`lipLo` by
      `fun _ _ _ _ i => i.elim0`), `F := steepF`, `disc = 0`, `Λ0 = lam = 0`, `Msel := fun _ => 0`, `L₀ := 0`.
      `steepF_not_lip : ∀ ε γ Λ : ℝ, ¬ ∀ L x y : ℝ, |steepF ε γ L x - steepF ε γ L y| ≤ Λ * |x - y|` (take
      `L = |Λ| + 1`, `x = 1`, `y = 0`; `simp [steepF]` then `nlinarith [abs_nonneg Λ, le_abs_self Λ]` after rewriting
      `|(|Λ| + 1)| = |Λ| + 1` by `abs_of_pos`). Theorem names: `steep_selMin_F` (rfl), `steepF_not_lip`. F table
      text: the G83 rows admit a test `F` that is not Lipschitz uniformly in `L`; G86 needs the extra input `lip`.
      Written by the formalize task 2026-11-18 in `SteklovAudit/H5GlobalLipStrict.lean` (uncompiled at push):
      def `steepF`, `steep_selMin`; theorems `steep_selMin_F`, `steepF_not_lip`, `steep_selMin_not_lip`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the interactive session 2026-11-21: STATUS PASS 974/974 at 41473f6, all three
      `H5GlobalLipStrict` theorems verified.
- [x] G89. `SteklovAudit/H5GlobalVanishNeeded.lean` (imports `SteklovAudit.H5GlobalLip`): the rows (2.2) and
      Lemma 7.1′ do not give `globalVanish`. `pdeD (L : ℝ) : Data (Fin 1) (Fin 1)` with `a = 1`, `b = 0`,
      `J _ _ = 1 + L` (so `K _ _ = 1 + L`). `pdeD_pde : ∀ L, PDEInputs (pdeD L) L 1 1` (both fields: `simp [hs2, pdeD,
      Data.K]`). `pdeD_prod : Real.sqrt (hs2 (pdeD L).K * hs2 (pdeD L).J) = (1 + L) ^ 2` (`Real.sqrt_eq_iff_mul_self_eq`
      or rewrite the product as `((1 + L) ^ 2) ^ 2` and use `Real.sqrt_sq (sq_nonneg _)`). `pdeD_not_vanish : ¬ ∃ L₀ : ℝ,
      ∀ L, L₀ ≤ L → 1 * Real.sqrt (hs2 (pdeD L).K * hs2 (pdeD L).J) ≤ 1 * L` (at `L = max L₀ 0`: `(1 + L) ^ 2 > L`,
      `nlinarith`). Theorem names: `pdeD_pde`, `pdeD_prod`, `pdeD_not_vanish`. F table text: with `Cm = Ck = 1` in
      `PDEInputs` the unsplit product can be `(1 + L)²`; `globalVanish` is a separate input, as the docstring of
      `trace_transfer_naive` says of the O(L²) bound.
      Written by the interactive session 2026-11-21 in `SteklovAudit/H5GlobalVanishNeeded.lean` (uncompiled at
      push, commit 41473f6): def `pdeD`; theorems `pdeD_pde`, `pdeD_prod`, `pdeD_not_vanish`. It also imports
      `SteklovAudit.H5TailAudit`, for `hs2_fin_one`.
      Ticked by the interactive session 2026-11-21: STATUS PASS 974/974 at 41473f6, all three
      `H5GlobalVanishNeeded` theorems verified.
- [x] G90. `SteklovAudit/H5GlobalLipRows.lean` (imports `SteklovAudit.H5GlobalLip`): `globalVanish` replaced by
      two rows at the linear scale. `structure H5bGlobalLipRows (E Emod)` = the fields of `H5bGlobalLipInputs` without
      `globalVanish`, plus `m : ℝ → ℝ → ℝ`, `hm : ∀ ε γ, 0 ≤ m ε γ`, `massLin : ∀ ε γ L, 1 ≤ L → hs2 (D ε γ L).J ≤ m ε γ *
      L`, `δ : ℝ → ℝ → ℝ → ℝ`, `defectLin : ∀ ε γ L, 1 ≤ L → hs2 (D ε γ L).K ≤ δ ε γ L * L`, `δVanish : ∀ ε γ, 0 < ε →
      0 < γ → ∀ η, 0 < η → ∃ L₀, ∀ L, L₀ ≤ L → δ ε γ L ≤ η`. Lemma `sqrt_lin_prod (hL : 0 ≤ L) (hk : k ≤ d * L) (hj : j ≤
      m * L) (hk0 : 0 ≤ k) (hj0 : 0 ≤ j) (hd : d ≤ t ^ 2) (ht : 0 ≤ t) (hm : 0 ≤ m) : Λ * √(k * j) ≤ Λ * (t * √m * L)` for
      `0 ≤ Λ` (`Real.sqrt_le_sqrt` to `√((t * √m * L) ^ 2)`, `Real.sqrt_sq`, `Real.sq_sqrt hm`, `nlinarith`).
      `noncomputable def toGlobalLip` (for `η`: apply `δVanish` with `(η / ((Λ ε γ + 1) * (√(m ε γ) + 1))) ^ 2`, take
      `max 1 L₀`); `h5b_of_globalLipRows`. Docstring: `massLin` is (2.2) at the scale `L` rather than `(1 + L)²` and
      `defectLin` is an `o(L)` Hilbert–Schmidt defect; whether the paper supplies either at this scale is open (Josiah
      to say); both are named hypotheses, proved for no operator. Theorem names: `sqrt_lin_prod`,
      `h5b_of_globalLipRows`.
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5GlobalLipRows.lean` (uncompiled at push,
      commit 696755b): structure `H5bGlobalLipRows`; defs `toGlobalLip`; theorems `sqrt_lin_prod`, `scale_le`,
      `toGlobalLip_Λ`, `h5b_of_globalLipRows`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 978/978 at 0901598, all four
      `H5GlobalLipRows` theorems verified.

Items G91–G94 written by the formalize task on 2026-11-21 (no unchecked item was left in A–G).

- [x] G91. `SteklovAudit/H5GlobalLipRowsAudit.lean` (imports `SteklovAudit.H5GlobalLipRows`): the F2 audit for G90.
      `globalLipRows_nonempty_zero : Nonempty (H5bGlobalLipRows (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0))` (`nA = nB = 0`,
      `D` with `a = b = 0`, `J = 0`, `F = 0`, `disc = 0`, `Λ = m = 0`, `δ = 0`; the sums over `Fin 0` vanish by
      `simp [hs2]`; vanishing rows with `L₀ := 0`). `noncomputable def ofTarget (h : H5bTarget E Emod) :
      H5bGlobalLipRows E Emod` (`nA = nB = 0`, `F = 0`, `disc ε γ L := |E ε γ L - Emod ε γ L|`, `discVanish := h` after
      `unfold H5bTarget at h`, `Λ = m = δ = 0`; `massLin`/`defectLin` by `simp [hs2]`, `δVanish` with `L₀ := 0` and
      `hη.le`). `globalLipRows_iff_target : Nonempty (H5bGlobalLipRows E Emod) ↔ H5bTarget E Emod` (forward by
      `h5b_of_globalLipRows`). Theorem names: `globalLipRows_nonempty_zero`, `ofTarget_m` (rfl),
      `globalLipRows_iff_target`. F table text: as with F2 and G87, with `D` unconstrained the content sits in the
      `cutoff`/`disc` row; `massLin`, `defectLin`, `δVanish` carry content only once `D` is the operator's cutoff data.
      Written by the formalize task 2026-11-21 (commit cc56216). Ticked by the formalize task 2026-11-21: STATUS PASS
      982/982 at cc56216, all four `H5GlobalLipRowsAudit` theorems verified.
- [x] G92. `SteklovAudit/H5GlobalLipRowsStrict.lean` (imports `SteklovAudit.H5GlobalLipRows`,
      `SteklovAudit.H5GlobalVanishNeeded`, `SteklovAudit.H5TailAudit`): the G90 rows are sufficient, not necessary, for
      the G86 inputs. `pdeD_hs2J : hs2 (pdeD L).J = (1 + L) ^ 2` (`rw [H5TailAudit.hs2_fin_one]`; `rfl`/`ring`).
      `pdeD_not_massLin : ¬ ∃ m : ℝ, ∀ L : ℝ, 1 ≤ L → hs2 (pdeD L).J ≤ m * L` (at `L = max 1 (|m| + 1)`: `(1 + L) ^ 2 >
      L * L ≥ m * L`; `nlinarith [le_abs_self m, abs_nonneg m, le_max_left 1 (|m| + 1), le_max_right 1 (|m| + 1)]`).
      `noncomputable def pdeGlobalLip : H5bGlobalLipInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0)` with `nA = nB = 1`,
      `D := fun _ _ L => pdeD L`, `F = 0`, `disc = 0`, `Λ = 0`, `lip` by `simp`, `globalVanish` with `L₀ := 0`
      (`0 * _ ≤ η * L` by `simp` and `positivity`/`nlinarith`). Theorem names: `pdeD_hs2J`, `pdeD_not_massLin`,
      `pdeGlobalLip_D` (rfl). F table text: G86 inputs exist (with `Λ = 0`) whose cutoff data violate `massLin`, so
      `massLin` is an extra input of G90, not a consequence of the G86 row.
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5GlobalLipRowsStrict.lean` (uncompiled at push,
      commit f83bbb3): def `pdeGlobalLip`; theorems `pdeD_hs2J`, `pdeD_not_massLin`, `pdeGlobalLip_Λ`,
      `pdeGlobalLip_D`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 986/986 at 9559e55, all four
      `H5GlobalLipRowsStrict` theorems verified.
- [x] G93. `SteklovAudit/H5DeltaVanishNeeded.lean` (imports `SteklovAudit.H5GlobalLipRows`, `SteklovAudit.H5TailAudit`):
      `δVanish` is the row that carries the `o(L)`. `linD (L : ℝ) : Data (Fin 1) (Fin 1)` with `a = 1`, `b = 0`,
      `J _ _ = Real.sqrt L` (so `K _ _ = Real.sqrt L`). `linD_massLin : ∀ L, 1 ≤ L → hs2 (linD L).J ≤ 1 * L` and
      `linD_defectLin : ∀ L, 1 ≤ L → hs2 (linD L).K ≤ 1 * L` (`hs2_fin_one`, `Real.sq_sqrt` with `0 ≤ L`).
      `linD_prod : ∀ L, 0 ≤ L → Real.sqrt (hs2 (linD L).K * hs2 (linD L).J) = L` (product is `L ^ 2`; `Real.sqrt_sq`).
      `linD_not_vanish : ¬ ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → 1 * Real.sqrt (hs2 (linD L).K * hs2 (linD L).J) ≤ (1 / 2) * L` (at
      `L = max L₀ 1`: `L ≤ L / 2` with `L ≥ 1`, `linarith`). Theorem names: `linD_massLin`, `linD_defectLin`,
      `linD_prod`, `linD_not_vanish`. F table text: `massLin` and `defectLin` with a constant `δ = 1` give only `O(L)`;
      without `δVanish` the row `globalVanish` fails.
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5DeltaVanishNeeded.lean` (uncompiled at push,
      commit 9035e4a): def `linD`; theorems `linD_hs2J`, `linD_hs2K`, `linD_massLin`, `linD_defectLin`,
      `linD_prod`, `linD_not_vanish`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 992/992 at d0b3753, all six
      `H5DeltaVanishNeeded` theorems verified.
- [x] G94. `SteklovAudit/H5GlobalLipRowsEv.lean` (imports `SteklovAudit.H5GlobalLipRows`): a strictly weaker form of the
      G90 rows. `structure H5bGlobalLipRowsEv (E Emod)` = the fields of `H5bGlobalLipRows` without `massLin`, `δ`,
      `defectLin`, `δVanish`, plus `massEv : ∀ ε γ, ∃ L₁ : ℝ, ∀ L, L₁ ≤ L → hs2 (D ε γ L).J ≤ m ε γ * L` (mass row only
      eventually) and `defectSmall : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → hs2 (D ε γ L).K ≤
      η * L` (no auxiliary `δ`). `def ofRows (H : H5bGlobalLipRows E Emod) : H5bGlobalLipRowsEv E Emod` (`massEv` with
      `L₁ := 1`; `defectSmall` at `max 1 L₀` from `defectLin`, `δVanish` and `mul_le_mul_of_nonneg_right`).
      `noncomputable def toGlobalLipEv : H5bGlobalLipInputs E Emod` (as `toGlobalLip`, with `t` as there, `defectSmall` at
      `t ^ 2`, `L ≥ max 1 (max L₀ L₁)`, then `sqrt_lin_prod` with `d := t ^ 2` and `scale_le`). Theorem names:
      `ofRows_m` (rfl), `h5b_of_globalLipRowsEv`. F table text: the row can be stated as eventual `O(L)` mass plus
      `o(L)` defect, with no rate function `δ`; both remain named hypotheses, proved for no operator.
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5GlobalLipRowsEv.lean` (uncompiled at push,
      commit 4faaef4): structure `H5bGlobalLipRowsEv`; defs `ofRows`, `toGlobalLipEv`; theorems `ofRows_m`,
      `toGlobalLipEv_Λ`, `h5b_of_globalLipRowsEv`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 995/995 at 6a2263f, all three
      `H5GlobalLipRowsEv` theorems verified.

Items G95–G97 written by the formalize task on 2026-11-21 (no unchecked A–G item was left after G94). They audit the
G94 rows (`H5bGlobalLipRowsEv`): strictness against G90, the F2 audit, and necessity of `massEv`. None proves a row
for the Steklov operator.

- [x] G95. `SteklovAudit/H5GlobalLipRowsEvStrict.lean` (imports `SteklovAudit.H5GlobalLipRowsEv`): the G94 mass row is
      strictly weaker than the G90 row `massLin` for every constant `m`. `noncomputable def evD (L : ℝ) : Data (Fin 1) (Fin 1)`
      with `a = 0`, `b = 0`, `J _ _ = if L < 2 then Real.sqrt (1 / (L - 1)) else 0`. `evD_hs2K : ∀ L, hs2 (evD L).K = 0`
      (`Data.K`, `sub_self`); `evD_massEv : ∀ L, 2 ≤ L → hs2 (evD L).J ≤ 0 * L` (`if_neg`, `hs2` over `Fin 1`);
      `evD_no_massLin : ¬ ∃ m : ℝ, ∀ L, 1 ≤ L → hs2 (evD L).J ≤ m * L` (at `L = 1 + s`, `s = 1 / (2 * (|m| + 1))`, so
      `0 < s ≤ 1/2`, `hs2 J = 1 / s = 2 * (|m| + 1)` via `Real.sq_sqrt`, and `m * (1 + s) ≤ |m| * (3/2) < 2 * (|m| + 1)`;
      `le_abs_self`, `nlinarith`). Theorem names: `evD_hs2K`, `evD_massEv`, `evD_no_massLin`. F table text: the
      eventual mass row of G94 admits cutoff data that no G90 `massLin` row (any `m`) admits; the defect rows hold
      trivially there (`K = 0`).
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5GlobalLipRowsEvStrict.lean` (uncompiled at push,
      commit 6197075): def `evD`; theorems `evD_hs2K`, `evD_massEv`, `evD_J_sq`, `evD_no_massLin`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 999/999 at c142355, all four
      `H5GlobalLipRowsEvStrict` theorems verified.
- [x] G96. `SteklovAudit/H5GlobalLipRowsEvAudit.lean` (imports `SteklovAudit.H5GlobalLipRowsEv`,
      `SteklovAudit.H5GlobalLipRowsAudit`): the F2 audit for G94. `globalLipRowsEv_iff_target (E Emod) :
      Nonempty (H5bGlobalLipRowsEv E Emod) ↔ H5bTarget E Emod` (`h5b_of_globalLipRowsEv`; converse
      `ofRows (H5GlobalLipRowsAudit.ofTarget h)`), `globalLipRowsEv_nonempty_zero` (witness `E = Emod = 0`, as in
      `globalLipRows_nonempty_zero`), and `ofTarget_ev_m : (ofRows (H5GlobalLipRowsAudit.ofTarget h)).m = fun _ _ => 0`
      (rfl). Theorem names: `globalLipRowsEv_iff_target`, `globalLipRowsEv_nonempty_zero`, `ofTarget_ev_m`. F table text:
      the G94 rows are satisfiable, and (like G90) they are equivalent to the target only through the unconstrained
      `cutoff` row with empty data; the F2 caveat stands.
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5GlobalLipRowsEvAudit.lean` (uncompiled at push,
      commit 615e263): theorems `globalLipRowsEv_iff_target`, `ofTarget_ev_m`, `globalLipRowsEv_nonempty_zero`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 1002/1002 at 55fd293, all three
      `H5GlobalLipRowsEvAudit` theorems verified.
- [x] G97. `SteklovAudit/H5MassEvNeeded.lean` (imports `SteklovAudit.H5GlobalLipRows`): `massEv` cannot be dropped from
      G94. `noncomputable def bigD (L : ℝ) : Data (Fin 1) (Fin 1)` with `a = 1 / L`, `b = 0`, `J _ _ = L`, so
      `hs2 J = L ^ 2` and `hs2 K = 1` for `L ≠ 0` (`field_simp`). `bigD_hs2J : ∀ L, hs2 (bigD L).J = L ^ 2`;
      `bigD_hs2K : ∀ L, L ≠ 0 → hs2 (bigD L).K = 1`; `bigD_defectSmall : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      hs2 (bigD L).K ≤ η * L` (`L₀ = 1 / η + 1`); `bigD_not_massEv : ¬ ∃ m L₁ : ℝ, ∀ L, L₁ ≤ L → hs2 (bigD L).J ≤ m * L`
      (at `L = max L₁ (|m| + 1)`, `L ^ 2 > m * L`); `bigD_not_vanish : ¬ ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      1 * Real.sqrt (hs2 (bigD L).K * hs2 (bigD L).J) ≤ (1 / 2) * L` (product `L ^ 2`, `Real.sqrt_sq`, at `L = max L₀ 1`).
      Theorem names: `bigD_hs2J`, `bigD_hs2K`, `bigD_defectSmall`, `bigD_not_massEv`, `bigD_not_vanish`. F table text:
      an `o(L)` defect alone does not give `globalVanish` (with `Λ = 1`); the mass row is a necessary separate input.
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5MassEvNeeded.lean` (uncompiled at push,
      commit 097862e): def `bigD`; theorems `bigD_hs2J`, `bigD_hs2K`, `bigD_defectSmall`, `bigD_not_massEv`,
      `bigD_prod`, `bigD_not_vanish`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 1008/1008 at 533996a, all six
      `H5MassEvNeeded` theorems verified.

Items G98–G100 written by the formalize task on 2026-11-21 (no unchecked A–G item was left after G97). They replace
the G94 mass/defect pair by a strictly weaker trade-off pair (mass `O(L^p)`, defect `o(L^(2-p))`), check strictness,
and run the F2 audit. None proves a row for the Steklov operator.

- [x] G98. `SteklovAudit/H5GlobalLipRowsPow.lean` (imports `SteklovAudit.H5GlobalLipRowsEv`): a trade-off form of the
      G94 rows. `structure H5bGlobalLipRowsPow (E Emod)` = the fields of `H5bGlobalLipRowsEv` with `massEv`,
      `defectSmall` replaced by `p : ℝ → ℝ → ℝ`, `hp : ∀ ε γ, 0 ≤ p ε γ ∧ p ε γ ≤ 2`, `massPow : ∀ ε γ, ∃ L₁ : ℝ,
      ∀ L, L₁ ≤ L → hs2 (D ε γ L).J ≤ m ε γ * L ^ (p ε γ)` (`Real.rpow`) and `defectPow : ∀ ε γ : ℝ, 0 < ε → 0 < γ →
      ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → hs2 (D ε γ L).K ≤ η * L ^ (2 - p ε γ)`. Helper
      `rpow_split : 0 < L → L ^ p * L ^ (2 - p) = L * L` (`← Real.rpow_add`, `Real.rpow_two` or
      `Real.rpow_natCast`, `sq`). `def ofEv (H : H5bGlobalLipRowsEv E Emod)` with `p := fun _ _ => 1`
      (`Real.rpow_one`; `2 - 1 = 1` by `norm_num`). `noncomputable def toGlobalLipPow : H5bGlobalLipInputs E Emod`
      (as `toGlobalLipEv`: `t` as there, `defectPow` at `t ^ 2`, `L ≥ max 1 (max L₀ L₁)`; then
      `hs2 K * hs2 J ≤ (t ^ 2 * m) * (L * L)` by `mul_le_mul` and `rpow_split`, and feed `sqrt_lin_prod` with
      `k := hs2 K * hs2 J / L`, or prove the `Real.sqrt` bound directly via `Real.sqrt_le_sqrt`,
      `Real.sqrt_mul_self`, `Real.sqrt_mul`). Theorem names: `rpow_split`, `ofEv_p` (rfl), `toGlobalLipPow_Λ` (rfl),
      `h5b_of_globalLipRowsPow`. F table text: the mass and defect rows may trade powers of `L` (`O(L^p)` mass with
      `o(L^(2-p))` defect, `0 ≤ p ≤ 2`); `p = 1` is G94. Both remain named hypotheses, proved for no operator.
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5GlobalLipRowsPow.lean` (uncompiled at push,
      commit 806f9b9): structure `H5bGlobalLipRowsPow`; defs `ofEv`, `toGlobalLipPow`; theorems `rpow_split`,
      `sqrt_pow_prod`, `ofEv_p`, `toGlobalLipPow_Λ`, `h5b_of_globalLipRowsPow`. Next run: tick if STATUS shows it
      compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 1013/1013 at 5fb76b2, all five
      `H5GlobalLipRowsPow` theorems verified.
- [x] G99. `SteklovAudit/H5GlobalLipRowsPowStrict.lean` (imports `SteklovAudit.H5GlobalLipRowsPow`,
      `SteklovAudit.H5TailAudit`): G98 is strictly weaker than G94 on cutoff data. `noncomputable def powD (L : ℝ) :
      Data (Fin 1) (Fin 1)` with `a = 1 / L ^ 2`, `b = 0`, `J _ _ = L`, so `hs2 J = L ^ 2` and `hs2 K = 1 / L ^ 2` for
      `L ≠ 0`. `powD_massPow : ∀ L, 1 ≤ L → hs2 (powD L).J ≤ 1 * L ^ (2 : ℝ)` (`Real.rpow_two`/`Real.rpow_natCast`);
      `powD_defectPow : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → hs2 (powD L).K ≤ η * L ^ ((2 : ℝ) - 2)` (`sub_self`,
      `Real.rpow_zero`; `1 / L ^ 2 ≤ 1 / L ≤ η` for `L ≥ max 1 (1 / η)`, `div_le_div_of_nonneg_left`, `nlinarith`);
      `powD_not_massEv : ¬ ∃ m L₁ : ℝ, ∀ L, L₁ ≤ L → hs2 (powD L).J ≤ m * L` (as `bigD_not_massEv`). Theorem names:
      `powD_hs2J`, `powD_hs2K`, `powD_massPow`, `powD_defectPow`, `powD_not_massEv`. F table text: the G98 rows (with
      `p = 2`) admit cutoff data that no G94 row admits.
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5GlobalLipRowsPowStrict.lean` (uncompiled at push):
      def `powD`; theorems `powD_hs2J`, `powD_hs2K`, `powD_massPow`, `powD_defectPow`, `powD_not_massEv`. Next run:
      tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 1018/1018 at 1b8fa7e, all five
      `H5GlobalLipRowsPowStrict` theorems verified.
- [x] G100. `SteklovAudit/H5GlobalLipRowsPowAudit.lean` (imports `SteklovAudit.H5GlobalLipRowsPow`,
      `SteklovAudit.H5GlobalLipRowsEvAudit`): the F2 audit for G98. `globalLipRowsPow_iff_target (E Emod) :
      Nonempty (H5bGlobalLipRowsPow E Emod) ↔ H5bTarget E Emod` (`h5b_of_globalLipRowsPow`; converse
      `ofEv (ofRows (H5GlobalLipRowsAudit.ofTarget h))`), `globalLipRowsPow_nonempty_zero` (witness `E = Emod = 0`, as
      in `globalLipRowsEv_nonempty_zero`), `ofTarget_pow_p : (ofEv (ofRows (H5GlobalLipRowsAudit.ofTarget h))).p =
      fun _ _ => 1` (rfl). Theorem names: `globalLipRowsPow_iff_target`, `globalLipRowsPow_nonempty_zero`,
      `ofTarget_pow_p`. F table text: the G98 rows are satisfiable and, like G90/G94, equivalent to the target only
      through the unconstrained `cutoff` row; the F2 caveat stands.
      Written by the formalize task 2026-11-21 in `SteklovAudit/H5GlobalLipRowsPowAudit.lean` (uncompiled at push):
      theorems `globalLipRowsPow_iff_target`, `ofTarget_pow_p`, `globalLipRowsPow_nonempty_zero`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-21: STATUS PASS 1021/1021 at f2c3c1b, all three
      `H5GlobalLipRowsPowAudit` theorems verified.

Items G101–G104 written by the formalize task on 2026-11-21 (no unchecked A–G item was left after G100). They attack
the F2 caveat itself: every form since F2 is equivalent to the target only because the cutoff data `D` (and `F`) are
fields that `ofTarget` may choose empty. G101 makes `nA nB D F` parameters ("pinned" to the operator's cutoff data);
G102–G104 check that the caveat is exactly the empty choice, that pinned nonempty data makes the rows strictly
stronger than the target (so the `cutoff` row is no longer the target in disguise), and that pinned rows are
non-vacuous on nonempty data. None proves a row for the Steklov operator; the operator's cutoff data is not defined.

- [x] G101. `SteklovAudit/H5PinnedRows.lean` (imports `SteklovAudit.H5GlobalLipRows`): `structure H5bPinnedRows
      (E Emod : ℝ → ℝ → ℝ → ℝ) (nA nB : ℝ → ℝ → ℝ → ℕ) (D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
      (F₀ : ℝ → ℝ → ℝ → ℝ → ℝ)` = the fields of `H5bGlobalLipRows` except `nA`, `nB`, `D`, `F`, with every occurrence
      of `D`/`F` replaced by the parameters `D₀`/`F₀` (fields `disc`, `cutoff`, `discVanish`, `Λ`, `hΛ`, `lip`, `m`,
      `hm`, `massLin`, `δ`, `defectLin`, `δVanish`). `def toRows (H : H5bPinnedRows E Emod nA nB D₀ F₀) :
      H5bGlobalLipRows E Emod` (field-by-field copy, `D := D₀`, `F := F₀`). Theorem names: `toRows_D`
      (`(toRows H).D = D₀`, rfl), `toRows_F` (rfl), `h5b_of_pinnedRows` (`h5b_of_globalLipRows (toRows H)`). F table
      text: the G90 rows stated for given cutoff data; the data is a parameter, not something the rows may choose.
      Written by the formalize task 2026-11-22 in `SteklovAudit/H5PinnedRows.lean` (uncompiled at push): structure
      `H5bPinnedRows`; def `toRows`; theorems `toRows_D`, `toRows_F`, `h5b_of_pinnedRows`. Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-22: STATUS PASS 1024/1024 at 8bb191a, all three `H5PinnedRows` theorems
      verified.
- [x] G102. `SteklovAudit/H5PinnedZeroAudit.lean` (imports `SteklovAudit.H5PinnedRows`,
      `SteklovAudit.H5GlobalLipRowsAudit`): the caveat is exactly the empty choice. With `zA := fun _ _ _ => 0`,
      `zD : ∀ ε γ L, Data (Fin 0) (Fin 0) := fun _ _ _ => ⟨fun _ => 0, fun _ => 0, fun _ _ => 0⟩`, `zF := fun _ _ _ _
      => 0`: `pinnedZero_iff_target (E Emod) : Nonempty (H5bPinnedRows E Emod zA zA zD zF) ↔ H5bTarget E Emod`
      (forward `h5b_of_pinnedRows`; converse copies `H5GlobalLipRowsAudit.ofTarget`: `disc := |E - Emod|`, `cutoff`
      by `simp`, `Λ = m = δ = 0`, `hs2` of zero arrays by `rowsAudit_hs2_zero` or `simp [hs2, Data.K]`). Theorem
      names: `pinnedZero_iff_target`, `pinnedZero_disc` (the converse's `disc` is `|E - Emod|`, rfl). F table text:
      pinned to empty data the rows are the target; all content of G90–G100 depends on which data is pinned.
      Written by the formalize task 2026-11-22 in `SteklovAudit/H5PinnedZeroAudit.lean` (uncompiled at push): defs
      `zA`, `zD`, `zF`, `ofTargetZero`; theorems `pinnedZero_disc`, `pinnedZero_iff_target`. Next run: tick if
      STATUS shows it compiled.
      Ticked by the formalize task 2026-11-22: STATUS PASS 1026/1026 at 4b2d560, both `H5PinnedZeroAudit`
      theorems verified.
- [x] G103. `SteklovAudit/H5PinnedNotTarget.lean` (imports `SteklovAudit.H5PinnedRows`): pinned nonempty data makes the
      rows strictly stronger than the target. `oA := fun _ _ _ => 1`; `noncomputable def bumpD : ∀ ε γ L : ℝ, Data
      (Fin 1) (Fin 1) := fun _ _ L => ⟨fun _ => 1, fun _ => 0, fun _ _ => L⟩`; `idF := fun _ _ _ x => x`.
      `bump_sum : ∀ ε γ L, ∑ i, ∑ j, (idF ε γ L ((bumpD ε γ L).a i) - idF ε γ L ((bumpD ε γ L).b j)) *
      (bumpD ε γ L).J i j ^ 2 = L ^ 2` (`simp [Fin.sum_univ_one]`, `ring`); `target_zero : H5bTarget (fun _ _ _ => 0)
      (fun _ _ _ => 0)` (as in `globalLipRows_nonempty_zero`); `not_pinned_bump : ¬ Nonempty (H5bPinnedRows
      (fun _ _ _ => 0) (fun _ _ _ => 0) oA oA bumpD idF)` (from `cutoff`, `L ^ 2 ≤ disc 1 1 L` via `abs` of `0 - L ^ 2`;
      `discVanish 1 1` at `η = 1` gives `disc ≤ L` for `L ≥ L₀`; take `L = max L₀ 2`, `nlinarith`). Theorem names:
      `bump_sum`, `target_zero`, `not_pinned_bump`, `pinned_strictly_stronger` (conjunction of the last two). F table
      text: once `D` is pinned, the target does not imply the rows; the `cutoff` row is no longer the target in disguise.
      Written by the formalize task 2026-11-22 in `SteklovAudit/H5PinnedNotTarget.lean` (uncompiled at push): defs
      `oA` (abbrev), `bumpD`, `idF`; theorems `bump_sum`, `target_zero`, `not_pinned_bump`,
      `pinned_strictly_stronger`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-22: STATUS PASS 1030/1030 at 0a50819, all four `H5PinnedNotTarget`
      theorems verified.
- [x] G104. `SteklovAudit/H5PinnedNonvacuous.lean` (imports `SteklovAudit.H5PinnedRows`): pinned rows hold on nonempty
      data with a nonzero defect. `oA := fun _ _ _ => 1`; `noncomputable def decayD : ∀ ε γ L : ℝ, Data (Fin 1) (Fin 1)
      := fun _ _ L => ⟨fun _ => 1 / L, fun _ => 0, fun _ _ => 1⟩` (so `K = 1 / L`, `hs2 K = 1 / L ^ 2`, `hs2 J = 1`),
      `idF := fun _ _ _ x => x`, `E := fun _ _ L => 1 / L`, `Emod := 0`. `noncomputable def decayRows :
      H5bPinnedRows E (fun _ _ _ => 0) oA oA decayD idF` with `disc = 0` (`cutoff`: the sum is `1 / L`, `simp`),
      `Λ = 1`, `m = 1` (`massLin`: `1 ≤ 1 * L`), `δ := fun _ _ L => 1 / L ^ 3` (`defectLin`: `1 / L ^ 2 = 1 / L ^ 3 * L`
      for `L ≥ 1` by `field_simp`; `δVanish`: `1 / L ^ 3 ≤ 1 / L ≤ η` for `L ≥ max 1 (1 / η)`). Theorem names:
      `decayD_hs2K` (`= 1 / L ^ 2` for `L ≠ 0`), `decayRows_m` (rfl), `pinned_nonempty_decay`. F table text: the pinned
      form is satisfiable on nonempty data with nonzero defect; not vacuous.
      Written by the formalize task 2026-11-22 in `SteklovAudit/H5PinnedNonvacuous.lean` (uncompiled at push): defs
      `oA` (abbrev), `decayD`, `idF`, `eD`, `decayRows`; theorems `decay_sum`, `decayD_hs2J`, `decayD_hs2K`,
      `decay_defect_pos`, `decayRows_m`, `pinned_nonempty_decay`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-22: STATUS PASS 1036/1036 at b94e672, all six
      `H5PinnedNonvacuous` theorems verified.

Items G105–G108 written by the formalize task on 2026-11-22 (no unchecked A–G item was left after G104). They carry
the pinned form (G101) further: the G98 trade-off rows for pinned data and their strictness, the `disc` field shown to
carry no content once data is pinned, and a data-only consequence of the pinned rows. None proves a row for the
Steklov operator; the operator's cutoff data is not defined.

- [x] G105. `SteklovAudit/H5PinnedRowsPow.lean` (imports `SteklovAudit.H5PinnedRows`, `SteklovAudit.H5GlobalLipRowsPow`):
      the G98 trade-off rows for pinned data. `structure H5bPinnedRowsPow (E Emod) (nA nB) (D₀) (F₀)` = the fields of
      `H5bGlobalLipRowsPow` except `nA`, `nB`, `D`, `F`, with `D`/`F` replaced by the parameters `D₀`/`F₀` (fields
      `disc`, `cutoff`, `discVanish`, `Λ`, `hΛ`, `lip`, `m`, `hm`, `p`, `hp`, `massPow`, `defectPow`). `def toRowsPow
      (H) : H5bGlobalLipRowsPow E Emod` (field copy, `D := D₀`, `F := F₀`). `def ofPinned (H : H5bPinnedRows E Emod nA
      nB D₀ F₀) : H5bPinnedRowsPow E Emod nA nB D₀ F₀` with `p := fun _ _ => 1` (`hp` by `norm_num`; `massPow` at
      `L₁ = 1` from `massLin`, `Real.rpow_one`; `defectPow` from `defectLin` and `δVanish ... η` at `L ≥ max 1 L₀`,
      `2 - 1 = 1` by `norm_num`, `Real.rpow_one`, `mul_le_mul_of_nonneg_right`). Theorem names: `toRowsPow_D` (rfl),
      `ofPinned_p` (rfl), `h5b_of_pinnedRowsPow` (`h5b_of_globalLipRowsPow (toRowsPow H)`). F table text: for pinned
      data the mass and defect rows may trade powers of `L`; `p = 1` is G101.
      Written by the formalize task 2026-11-22 in `SteklovAudit/H5PinnedRowsPow.lean` (uncompiled at push): structure
      `H5bPinnedRowsPow`, defs `toRowsPow`, `ofPinned`; theorems `toRowsPow_D`, `ofPinned_p`, `h5b_of_pinnedRowsPow`.
      Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-22: STATUS PASS 1039/1039 at 9062471, all three `H5PinnedRowsPow`
      theorems verified.
- [x] G106. `SteklovAudit/H5PinnedRowsPowStrict.lean` (imports `SteklovAudit.H5PinnedRowsPow`): G105 is strictly weaker
      than G101 on the same pinned data. `oA := fun _ _ _ => 1`; `noncomputable def qD : ∀ ε γ L : ℝ, Data (Fin 1)
      (Fin 1) := fun _ _ L => ⟨fun _ => 1 / L ^ 2, fun _ => 0, fun _ _ => L⟩` (so `hs2 J = L ^ 2`, `K = 1 / L`,
      `hs2 K = 1 / L ^ 2` for `L ≠ 0`); `idF := fun _ _ _ x => x`; `eQ := fun _ _ L => 1 / L ^ 2 * L ^ 2` (the sum
      exactly, so `disc = 0` and `cutoff` by `simp [Fin.sum_univ_one]`). `qD_hs2J : hs2 (qD ε γ L).J = L ^ 2`;
      `qD_hs2K : L ≠ 0 → hs2 (qD ε γ L).K = 1 / L ^ 2`; `pinnedPow_nonempty_q : Nonempty (H5bPinnedRowsPow eQ (fun _ _
      _ => 0) oA oA qD idF)` (`Λ = 1`, `m = 1`, `p = 2`; `massPow` via `Real.rpow_two`/`Real.rpow_natCast`; `defectPow`
      with `2 - 2 = 0`, `Real.rpow_zero`, `1 / L ^ 2 ≤ η` for `L ≥ max 1 (1 / η)`); `not_pinnedRows_q : ¬ Nonempty
      (H5bPinnedRows eQ (fun _ _ _ => 0) oA oA qD idF)` (`massLin` at `L = |m| + 2` gives `L ^ 2 ≤ m * L`, `nlinarith`).
      Theorem names: `qD_hs2J`, `qD_hs2K`, `pinnedPow_nonempty_q`, `not_pinnedRows_q`, `pinnedPow_strictly_weaker`
      (conjunction). F table text: with the data pinned, the trade-off rows admit data the linear rows reject.
      Written by the formalize task 2026-11-22 in `SteklovAudit/H5PinnedRowsPowStrict.lean` (uncompiled at push):
      defs `oA` (abbrev), `qD`, `idF`, `eQ`, `qRowsPow`; theorems `q_sum`, `qD_hs2J`, `qD_hs2K`,
      `pinnedPow_nonempty_q`, `not_pinnedRows_q`, `pinnedPow_strictly_weaker`. Next run: tick if STATUS shows it
      compiled.
      Ticked by the formalize task 2026-11-22: STATUS PASS 1045/1045 at e601e9c, all six
      `H5PinnedRowsPowStrict` theorems verified.
- [x] G107. `SteklovAudit/H5PinnedCutoffVanish.lean` (imports `SteklovAudit.H5PinnedRows`): the `disc` field carries no
      content once the data is pinned. `structure H5bPinnedCore (E Emod nA nB D₀ F₀)` = `H5bPinnedRows` with `disc`,
      `cutoff`, `discVanish` replaced by one row `cutoffVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ,
      ∀ L, L₀ ≤ L → |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j, (F₀ ε γ L ((D₀ ε γ L).a i) - F₀ ε γ L ((D₀ ε γ L).b j)) *
      (D₀ ε γ L).J i j ^ 2| ≤ η * L`. `def ofCore (H) : H5bPinnedRows ...` with `disc` := that absolute value
      (`cutoff` by `le_refl`, `discVanish := H.cutoffVanish`); `def toCore (H : H5bPinnedRows ...)` (`cutoffVanish`
      from `le_trans (H.cutoff ..) (hL ..)`). Theorem names: `ofCore_disc` (rfl), `pinned_iff_core` (`Nonempty
      (H5bPinnedRows ..) ↔ Nonempty (H5bPinnedCore ..)`), `h5b_of_pinnedCore`. F table text: for pinned data the
      `cutoff` row is one `o(L)` statement comparing `E − Emod` with the explicit spectral sum of `D₀`.
      Written by the formalize task 2026-11-22 in `SteklovAudit/H5PinnedCutoffVanish.lean` (uncompiled at push): def
      `coreDisc` (the absolute value, used in `cutoffVanish`), structure `H5bPinnedCore`, defs `ofCore`, `toCore`;
      theorems `ofCore_disc`, `pinned_iff_core`, `h5b_of_pinnedCore`. Next run: tick if STATUS shows it compiled.
      Ticked by the formalize task 2026-11-22: STATUS PASS 1048/1048 at 1fb21d8, all three
      `H5PinnedCutoffVanish` theorems verified.
- [x] G108. `SteklovAudit/H5PinnedSumSmall.lean` (imports `SteklovAudit.H5PinnedRows`): the pinned rows constrain the
      data independently of `E`. `def pinnedSum (D₀ F₀) (ε γ L : ℝ) : ℝ := ∑ i, ∑ j, (F₀ ε γ L ((D₀ ε γ L).a i) -
      F₀ ε γ L ((D₀ ε γ L).b j)) * (D₀ ε γ L).J i j ^ 2`. `pinned_sum_littleO (H : H5bPinnedRows E Emod nA nB D₀ F₀) :
      ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |pinnedSum D₀ F₀ ε γ L| ≤ η * L` (from
      `h5b_of_pinnedRows H` and `H.cutoff`, `H.discVanish` at `η / 2`; `|s| ≤ |x| + |x - s|` by `abs_sub_abs_le_abs_sub`
      or `abs_sub_comm` + `abs_add`, `L ≥ max L₀ L₁`, `linarith`); `not_pinned_of_sum_large`: if `¬` that `o(L)`
      property holds for `D₀ F₀` at some `ε γ > 0`, then `∀ E Emod, ¬ Nonempty (H5bPinnedRows E Emod nA nB D₀ F₀)`.
      Theorem names: `pinned_sum_littleO`, `pinned_target_and_sum` (conjunction with `h5b_of_pinnedRows`),
      `not_pinned_of_sum_large`. F table text: pinned rows require the data's own spectral sum to be `o(L)`; data
      failing this (e.g. G103's `bumpD`) admits no rows for any `E`.
      Written by the formalize task 2026-11-22 in `SteklovAudit/H5PinnedSumSmall.lean` (uncompiled at push): defs
      `pinnedSum`, `SumLittleO` (the `o(L)` property, stated for all `ε γ > 0`); theorems `pinned_sum_littleO`,
      `pinned_target_and_sum`, `not_pinned_of_sum_large` (hypothesis `¬ SumLittleO D₀ F₀`). Next run: tick if STATUS
      shows it compiled.
      Ticked by the formalize task 2026-11-22: STATUS PASS 1051/1051 at c2bea0f, all three `H5PinnedSumSmall`
      theorems verified.

Status 2026-11-22: G109–G112 verified (CI at db578cf: PASS 1209/1209; all 12 declarations of `H5PinnedDataRows`,
`H5PinnedCutoffIsTarget`, `H5PinnedPtsLip`, `H5PinnedPtsLipStrict` with standard axioms only).

Items G109–G112 written by the formalize task on 2026-11-22 (no unchecked A–G item was left after G108). They split
the pinned rows (G101) into data-only rows and one row involving `E`, show that relative to the data rows the
`cutoff` row is exactly the target, and weaken the Lipschitz row to the pinned spectral points. None proves a row
for the Steklov operator; the operator's cutoff data is not defined.

- [x] G109. `SteklovAudit/H5PinnedDataRows.lean` (imports `SteklovAudit.H5PinnedCutoffVanish`,
      `SteklovAudit.H5PinnedSumSmall`): the rows that mention only the data. `structure H5bPinnedDataRows (nA nB) (D₀)
      (F₀)` = the fields `Λ`, `hΛ`, `lip`, `m`, `hm`, `massLin`, `δ`, `defectLin`, `δVanish` of `H5bPinnedRows` (no
      `E`, `Emod`, `disc`). `def dataOf (H : H5bPinnedRows E Emod nA nB D₀ F₀) : H5bPinnedDataRows nA nB D₀ F₀` (field
      copy). `sumLittleO_of_dataRows (R) : SumLittleO D₀ F₀` (G108's property, now without `E`): `trace_transfer` with
      `f := F₀ ε γ L`, then `∑ |K| |J| ≤ √(hs2 K · hs2 J)` (the Cauchy–Schwarz step already used in the G86/G83 chain,
      or `Finset.sum_mul_sq_le_sq_mul_sq` + `Real.le_sqrt`), then `sqrt_lin_prod` and `scale_le` exactly as in
      `H5GlobalLipRows.toGlobalLip`. `pinned_iff_dataRows_core : Nonempty (H5bPinnedRows E Emod nA nB D₀ F₀) ↔
      Nonempty (H5bPinnedDataRows nA nB D₀ F₀) ∧ ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀, ∀ L, L₀ ≤ L → coreDisc ..
      ≤ η * L` (use `pinned_iff_core` from G107; the core's `cutoffVanish` is the second conjunct). Theorem names:
      `dataOf_Λ` (rfl), `sumLittleO_of_dataRows`, `pinned_iff_dataRows_core`. F table text: the pinned rows are data
      rows (mass, defect, Lipschitz) plus one `o(L)` row comparing `E − Emod` with the data's spectral sum.
      Written by Josiah's interactive session 2026-11-22 in `SteklovAudit/H5PinnedDataRows.lean` (uncompiled at push):
      structure `H5bPinnedDataRows`; `dataOf`, `dataOf_Λ`; `withSum` (data rows + trivial cutoff row for `E := pinnedSum`,
      `Emod := 0`, `disc := 0`), so `sumLittleO_of_dataRows` reuses `h5b_of_pinnedRows` instead of redoing Cauchy–Schwarz;
      `coreOf`, `pinned_iff_dataRows_core`. Next run: tick if STATUS shows it compiled; if it failed, fix it first.
- [x] G110. `SteklovAudit/H5PinnedCutoffIsTarget.lean` (imports `SteklovAudit.H5PinnedDataRows`): relative to the data
      rows, the `cutoff` row is the target. `pinned_iff_target_of_dataRows (R : H5bPinnedDataRows nA nB D₀ F₀) (E
      Emod) : Nonempty (H5bPinnedRows E Emod nA nB D₀ F₀) ↔ H5bTarget E Emod` (forward `h5b_of_pinnedRows`; converse:
      `sumLittleO_of_dataRows R` and the target at `η / 2` give `cutoffVanish` by the triangle inequality as in
      `pinned_sum_littleO` (`abs_le`, `linarith`), then `pinned_iff_dataRows_core`). Theorem names:
      `cutoffVanish_of_target`, `pinned_iff_target_of_dataRows`. F table text: once the data rows hold, the remaining
      row carries exactly the content of (7.29); all non-trivial content of the pinned form is in the data rows and
      in the choice of `D₀` (the paper's cutoff data, which is open).
- [x] G111. `SteklovAudit/H5PinnedPtsLip.lean` (imports `SteklovAudit.H5PinnedDataRows`): the Lipschitz row weakened to
      the pinned spectral points. `structure H5bPinnedPtsRows (nA nB D₀ F₀)` = `H5bPinnedDataRows` with `lip`
      replaced by `lipPts : ∀ ε γ L : ℝ, 1 ≤ L → ∀ i j, |F₀ ε γ L ((D₀ ε γ L).a i) - F₀ ε γ L ((D₀ ε γ L).b j)| ≤
      Λ ε γ * |(D₀ ε γ L).a i - (D₀ ε γ L).b j|`. `trace_transfer_pts`: the `trace_transfer` bound under `lipPts` at
      one `L` (`Finset.abs_sum_le_sum_abs` twice, per-entry `abs_mul`, `Data.K`, `mul_le_mul_of_nonneg_right`,
      `Finset.mul_sum`). `def ofDataRows (R : H5bPinnedDataRows ..) : H5bPinnedPtsRows ..` (`lipPts` from `lip`).
      `sumLittleO_of_ptsRows (R) : SumLittleO D₀ F₀` (as G109, with `L ≥ max 1 L₀`). `h5b_of_ptsRows (R) (hc :
      cutoffVanish row for E Emod) : H5bTarget E Emod` (triangle inequality as in G110). Theorem names:
      `trace_transfer_pts`, `ofDataRows_Λ` (rfl), `sumLittleO_of_ptsRows`, `h5b_of_ptsRows`. F table text: the row
      "Lipschitz-type bounds Λ" is needed only on the pinned spectral points, for `L ≥ 1`.
- [x] G112. `SteklovAudit/H5PinnedPtsLipStrict.lean` (imports `SteklovAudit.H5PinnedPtsLip`): G111 is strictly weaker
      than G109 on the same data. `oA := fun _ _ _ => 1`; `noncomputable def flatD : ∀ ε γ L : ℝ, Data (Fin 1) (Fin 1)
      := fun _ _ _ => ⟨fun _ => 0, fun _ => 0, fun _ _ => 1⟩` (so `K = 0`, `hs2 J = 1`); `sqF := fun _ _ _ x => x ^ 2`.
      `ptsRows_flat : Nonempty (H5bPinnedPtsRows oA oA flatD sqF)` (`Λ = 0`, `m = 1`, `δ = 0`; `lipPts` by `simp`,
      both points are `0`; `massLin` by `simp [hs2, Fin.sum_univ_one]` and `1 ≤ 1 * L`; `defectLin` with `hs2 K = 0`).
      `not_dataRows_flat : ¬ Nonempty (H5bPinnedDataRows oA oA flatD sqF)` (`lip` at `x = Λ + 1`, `y = 0`: `(Λ + 1) ^ 2
      ≤ Λ * (Λ + 1)` contradicts `hΛ`, `nlinarith`). Theorem names: `ptsRows_flat`, `not_dataRows_flat`,
      `ptsLip_strictly_weaker` (conjunction). F table text: the pointwise Lipschitz row admits data and `F₀` that the
      global row rejects.

Status 2026-11-22 (interactive session): G113–G120 are written and verified. CI run 45052545358 at bbcf097 reports
PASS, 1121 of 1121 theorems with standard axioms only, including every declaration of `CountableCutoffTail`,
`AffineCutoffTail`, `H5CutoffInterface`, `H5CutoffAffineInstance`, `TetraAffineFlux` and `CumulativeBudget`, and the four
Foundations declarations named in G118. G119 landed with different theorem names than specified (`boundary_mass`,
`green_pair`, `residual_orthogonal`, `residual_energy`, `cutoff_tail_moment`, scaled by 12); same identities. Module
layout differs from the spec where noted in each file (G113/G114 bundle the certificates in `Cert`). Open: estimates
(i) and (ii) of G116, Parseval for the probes, and gaps (7.2), (7.29), (7.38)/(7.45), (9.1).

Items G113–G117 added by Josiah's interactive session on 2026-11-22. They take the
finite-sum certificate of `docs/affine-dtn-cutoff.md` §3 (the centered cutoff estimate) to a countable eigenbasis, then
state what a growing edge family must supply for H5. Indices are arbitrary types (`ι` = eigenbasis index, `κ` = probe
index; neither has to be finite). Summability is over `ι × κ`. Weights `w i j` stand for `|J i j|²`. Nothing here
defines the Steklov operator or its eigenbasis: Parseval and the operator-domain identities stay as named hypotheses.
Note: the doc cites `SteklovAudit/TetraAffineFlux.lean`, but that file is not in the repository. G115 must not import
it. G119 (below) creates that file. G118 (first) fixes the audit so that subdirectory modules are checked.

Ticked by the formalize task 2026-11-22: G113–G117, G119 and G120 were implemented by the interactive session and all
their theorems are `verified (standard axioms only)` in CI run #475 (commit bbcf097, 1121/1121): CountableCutoffTail
(`summable_mass` … `summable_centered`, `S_sub_Sle`, `tail_term_le`, `cutoff_tail_le`), AffineCutoffTail
(`affine_two_over_t_sq`, `affine_mu_eq`, `affine_residual_sum`, `residual_pairing_phi`, `affine_cutoff_tail`),
H5CutoffInterface (`cutoff_error_le`, `full_trace_matches`), H5CutoffAffineInstance (`affine_ratioLittleO`,
`affine_ratio_O_inv`), CumulativeBudget (`tail_littleO_of_cutoff_bound`, `tail_eta_form`, `order_of_limits_matters`),
TetraAffineFlux (`face_midpoint_moments`, `boundary_mass`, `green_pair`, `residual_orthogonal`, `residual_energy`,
`cutoff_tail_moment`; names differ from the G119 text, and the doc's "Verification and provenance" paragraph names no
theorems, so the doc needs no edit). Next unchecked A–G item: G109.

- [x] G113. `SteklovAudit/CountableCutoffTail.lean` (imports Mathlib only): from finite certificates to absolute
      summability. Data: `lam : ι → ℝ`, `mu : κ → ℝ`, `w : ι → κ → ℝ`, `hw : ∀ i j, 0 ≤ w i j`. Finite-certificate
      hypotheses: `hM : ∀ s : Finset (ι × κ), ∑ p ∈ s, w p.1 p.2 ≤ M` and
      `hE : ∀ s : Finset (ι × κ), ∑ p ∈ s, (lam p.1 - mu p.2) ^ 2 * w p.1 p.2 ≤ E`.
      Theorems:
      `summable_mass`: `Summable (fun p : ι × κ => w p.1 p.2)` and `tsum_mass_le : ∑' p, w p.1 p.2 ≤ M`, via
      `summable_of_sum_le` and `tsum_le_of_sum_le'` (`0 ≤ M` follows from `hM ∅`).
      `summable_moment`, `tsum_moment_le`: the same for `(lam - mu)² w`, with bound `E`.
      `abs_le_half_one_add_sq (d : ℝ) : |d| ≤ (1 + d ^ 2) / 2` (from `sq_nonneg (|d| - 1)` and `sq_abs`).
      `summable_centered (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf) (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|)`:
      `Summable (fun p => (F (lam p.1) - F (mu p.2)) * w p.1 p.2)`. Use `Summable.of_norm_bounded` with the bound
      `Lf * (w + (lam - mu)² w) / 2`: the termwise bound is `|F λ − F μ| w ≤ Lf |d| w`, then the previous lemma.
      Define `S F := ∑' p, (F (lam p.1) - F (mu p.2)) * w p.1 p.2` and
      `Sle F L := ∑' p, if lam p.1 ≤ L then (F (lam p.1) - F (mu p.2)) * w p.1 p.2 else 0`.
      F table text: a finite-sum certificate (uniform over finite subsets) gives absolute convergence of the centered
      Lipschitz series on a countable eigenbasis.
      Not proved: anything about the DtN operator or its spectrum.
- [x] G114. `SteklovAudit/CountableCutoffTail.lean`, appended (no new file). Cutoff tail bound
      `Lip(F)·E/(L − μ*)`. Hypotheses as in G113, plus `muStar : ℝ`, `hmu : ∀ j, mu j ≤ muStar`, `hL : muStar < L`.
      Theorems:
      `S_sub_Sle`: `S F - Sle F L = ∑' p, if L < lam p.1 then (F (lam p.1) - F (mu p.2)) * w p.1 p.2 else 0`. Summability
      of both indicator series comes from `summable_centered` (the `ite` term is bounded by `‖term‖`). Then use
      `Summable.tsum_sub` and a pointwise `split_ifs` / `not_le`.
      `tail_term_le`: if `L < lam i`, then `|(F (lam i) - F (mu j)) * w i j| ≤ Lf * ((lam i - mu j) ^ 2 * w i j) / (L - muStar)`.
      Proof: `d := lam i - mu j ≥ lam i - muStar > L - muStar > 0`, so `|d| = d ≤ d ^ 2 / (L - muStar)`
      (`le_div_iff₀`, `nlinarith`). Then `hF`, `abs_mul`, `mul_le_mul_of_nonneg_right`.
      `cutoff_tail_le : |S F - Sle F L| ≤ Lf * E / (L - muStar)`. Proof: `norm_tsum_le_tsum_norm`, then
      `Summable.tsum_le_tsum` against `Lf / (L - muStar) * ((lam − mu)² w)` (zero off the tail, because the moment
      summand is nonnegative), then `tsum_mul_left` and `tsum_moment_le`.
      F table text: for `L > max μ`, the part of the centered Lipschitz trace above `L` is at most `Lip(F)·E/(L − μ*)`.
      This is the countable version of the doc's §3 estimate.
- [x] G115. `SteklovAudit/AffineCutoffTail.lean` (imports `SteklovAudit.CountableCutoffTail`): the affine
      specialization `E = 16/a²`.
      Arithmetic, all for `a > 0`: `t := a / (2 * √2)`, `μaff := 1 / (√3 * t)`. Then
      `affine_two_over_t_sq : 2 / t ^ 2 = 16 / a ^ 2`; `affine_mu_eq : μaff = 2 * √6 / (3 * a)`;
      `affine_residual_sum : 0 + 3 * (2 / (3 * t ^ 2)) = 16 / a ^ 2`. The last one is the four probe residuals: `Rφ₀ = 0`,
      and `‖Rφⱼ‖² = 2·3/(9t²)` from the doc's pairing `⟨Ru,Rw⟩ = 2(b·e)/(9t²)` with `b = √3 eⱼ`. Also prove that pairing
      value as `residual_pairing_phi (j) : 2 * (√3) ^ 2 / (9 * t ^ 2) = 2 / (3 * t ^ 2)`.
      `structure AffineProbeParseval (lam : ι → ℝ) (J : ι → Fin 4 → ℝ) (a : ℝ) : Prop`. Named hypotheses (Parseval for
      the four probes, not proved): `mass : HasSum (fun p : ι × Fin 4 => J p.1 p.2 ^ 2) 4` and
      `defect : HasSum (fun p => (lam p.1 - ![0, μaff, μaff, μaff] p.2) ^ 2 * J p.1 p.2 ^ 2) (16 / a ^ 2)`.
      `affine_cutoff_tail (P : AffineProbeParseval lam J a) (hF : Lipschitz with Lf ≥ 0) (hL : μaff < L)`:
      `|S − Sle| ≤ 16 * Lf / (a ^ 2 * (L − μaff))`. Get `hM` and `hE` from `HasSum` with `sum_le_hasSum` (nonnegative
      terms), `muStar := μaff` (`Fin.forall_fin_succ` / `decide` on the four entries, using `0 ≤ μaff`), then G114.
      F table text: on the four affine probes the cutoff discrepancy is `O(Lip(F)/L)`, given Parseval as a hypothesis.
      Not proved: Parseval, the residual identities as operator statements, and the Steklov eigenbasis itself.
- [x] G116. `SteklovAudit/H5CutoffInterface.lean` (imports `SteklovAudit.CountableCutoffTail`): what a growing edge
      family must supply. `structure H5EdgeFamilyCutoff (ι κ : Type*)`:
      - fixed `lam : ι → ℝ`;
      - per cutoff `L : ℝ`: `mu L : κ → ℝ`, `w L : ι → κ → ℝ` (nonnegative), `F L : ℝ → ℝ`, `Lip L ≥ 0`
        (Lipschitz constant of `F L`), `muStar L`, `M L`, `E L`, and a threshold `Lgap : ℝ`;
      - fields `hmu : ∀ L j, mu L j ≤ muStar L`, `hgap : ∀ L, Lgap ≤ L → muStar L < L`, the finite certificates `hM L`,
        `hE L` as in G113, and `hF L`.
      Theorems:
      `cutoff_error_le (X) (L) (hL : X.Lgap ≤ L)`: `|S_L − Sle_L L| ≤ Lip L * E L / (L − muStar L)`, by G114 at each `L`.
      `def RatioLittleO X : Prop := ∀ η > 0, ∃ L₀, ∀ L ≥ L₀, Lip L * E L / (L − muStar L) ≤ η * L`.
      `def TraceMatches X (D : ℝ → ℝ) : Prop := ∀ η > 0, ∃ L₀, ∀ L ≥ L₀, |Sle_L L − D L| ≤ η * L`. Here `D L` stands
      for the paper's localized `E − E_mod` at cutoff `L`. This is a named hypothesis only.
      `full_trace_matches (X) (D) (h1 : RatioLittleO X) (h2 : TraceMatches X D)`: `∀ η > 0, ∃ L₀, ∀ L ≥ L₀,
      |S_L − D L| ≤ η * L` (split `η/2 + η/2`, triangle inequality, `max L₀ X.Lgap`).
      F table text: H5 through this route needs exactly two estimates, both open:
      (i) `Lip(F_L)·E_L/(L − μ*(L)) = o(L)`, where `E_L` is the summed squared defect of the edge family;
      (ii) the remaining geometric question: how closely the truncated probe trace `Sle_L L` approximates the
      localized tetrahedron–wedge discrepancy `E − E_mod` (needed: to `o(L)`).
      Docstring must say that this proves neither, and does not close (7.29) or H5.
- [x] G117. `SteklovAudit/H5CutoffAffineInstance.lean` (imports `SteklovAudit.AffineCutoffTail`,
      `SteklovAudit.H5CutoffInterface`): the affine calculation as an exact test case of estimate (i). For a constant
      family (`mu`, `w`, `F` independent of `L`, `E L = 16/a²`, `muStar L = μaff`, `Lip L = Lf`), take the Parseval
      fields of G115 as hypotheses. Prove `affine_ratioLittleO : RatioLittleO X`: the ratio is
      `16 Lf / (a² (L − μaff))`, which is `≤ η L` for large `L`. Also prove `affine_ratio_O_inv`:
      `L ≥ 2 μaff + 1 → ratio ≤ 32 Lf / (a² L)`. Take `Lgap := μaff + 1`, and `L₀ := max 1 (2 * μaff + 1)`.
      Theorem names: `affineFamily` (the structure instance; hypothesis-parametrized),
      `affine_ratioLittleO`, `affine_ratio_O_inv`.
      F table text: the fixed four-probe family satisfies (i) with rate `O(1/L)`. It says nothing about (ii) or the
      edge family.
- [x] G118. Audit fix, done before G113. `axiom_audit.py` collects modules with
      `(ROOT / "SteklovAudit").glob("*.lean")`, which is not recursive. Subdirectory modules are therefore never scanned
      for escape hatches and never get `#print axioms`. This covers `SteklovAudit/Foundations/Trace1D.lean`: its
      theorems are missing from STATUS.json even though `lakefile.toml` (`globs = ["SteklovAudit", "SteklovAudit.+"]`)
      builds it.
      Fix: replace every `glob("*.lean")` on `ROOT / "SteklovAudit"` with `rglob("*.lean")`. Where the probe import is
      built from `p.stem`, use the dotted path instead:
      `"SteklovAudit." + ".".join(p.relative_to(ROOT / "SteklovAudit").with_suffix("").parts)`.
      Use the same relative path (e.g. `Foundations/Trace1D.lean`) for the `file` field in results. Check
      `tools/build_map.py` for the same non-recursive glob.
      Acceptance: a green total is not enough. STATUS.json `results` must list each of these four declarations by name,
      each with status `verified (standard axioms only)`:
      `SteklovAudit.Foundations.Trace1D.pointwise_bound`, `SteklovAudit.Foundations.Trace1D.trace_1d`,
      `SteklovAudit.Foundations.TraceHalfLine.cross_abs_le` and `SteklovAudit.Foundations.TraceHalfLine.trace_halfLine`.
      `theorems` must rise by exactly the number of new declarations found (at least 4).
      Also add a `modules_audited` list to STATUS.json (one entry per `.lean` file, with its count of audited
      declarations). Report as a problem any file whose source declares a `theorem`/`lemma` but which has 0 audited
      entries, so a module the audit skips can no longer pass silently.
      Before writing the commit, run `python3 axiom_audit.py`, or check the CI STATUS after the push, and quote the four
      result lines in the ROADMAP note.
      F1.1 (ticked at e2b3d1d) and F1.2 were judged from the build log alone. If any of the four is missing or
      non-standard here, untick the matching F item and say why.
      Written by the formalize task 2026-11-22 (uncompiled at push): `axiom_audit.py` now uses `rglob("*.lean")` in all
      four places (new helpers `lean_files`, `rel_name`, `module_name`); probe imports use the dotted module path; the
      `file` field and hatch/tautology messages use the path under `SteklovAudit/`; STATUS.json gains `modules_audited`
      (`file`, `declared`, `audited`) and `modules_skipped`; a file declaring theorems with 0 audited entries is a
      problem and fails the audit. `tools/build_map.py`: `rglob`, module ids are dotted paths (`modname`), source links
      map dots to `/`. The audit was not run locally (no Lean here). Next run: from CI STATUS.json quote the four
      Foundations result lines here, tick if all four are verified, else untick the matching F item.
      Ticked by the formalize task 2026-11-22: CI run #475 (commit bbcf097) PASS, 1121 of 1121 theorems; "Modules
      audited: 184 files; files declaring theorems but with 0 audited declarations: none". The four result lines:
      `Foundations/Trace1D.lean  SteklovAudit.Foundations.Trace1D.pointwise_bound  verified (standard axioms only)`,
      `Foundations/Trace1D.lean  SteklovAudit.Foundations.Trace1D.trace_1d  verified (standard axioms only)`,
      `Foundations/TraceHalfLine.lean  SteklovAudit.Foundations.TraceHalfLine.cross_abs_le  verified (standard axioms only)`,
      `Foundations/TraceHalfLine.lean  SteklovAudit.Foundations.TraceHalfLine.trace_halfLine  verified (standard axioms only)`.
      All four verified, so F1.1/F1.2 need no untick. (STATUS.md on main was not refreshed by run #475: its "Commit
      status if changed" step lost a push race; the PASS figures are from that run's summary page.)
- [x] G119. `SteklovAudit/TetraAffineFlux.lean` (imports Mathlib only). This is the companion module that
      `docs/affine-dtn-cutoff.md` already cites but that does not exist. All statements are dimensionless finite
      arithmetic in `ℝ³ = Fin 3 → ℝ`.
      Vertices `V = {(1,1,1), (1,−1,−1), (−1,1,−1), (−1,−1,1)}` (as `Fin 4 → Fin 3 → ℝ`). The face opposite `v` has
      midpoint nodes at the three edge midpoints of the other vertices. Define
      `bdry (g) := (1/4) Σ_v (1/3) Σ_{midpoints m of face v} g v m`.
      For `u = c + b·x` and `w = d + e·x`, prove:
      `mass_pairing`: `bdry (u·w) = c d + (b·e)/3`;
      `flux_pairing`: `bdry ((−b·v) · w) = (b·e)/3`;
      `residual_pairing`: with `r_b(v, x) = −(b·v + b·x)`, `bdry (r_b · r_e) = 2 (b·e)/3`;
      `residual_orth`: `bdry (r_b · 1) = 0` and `bdry (r_b · xₖ) = 0` for `k = 0, 1, 2`.
      All four formulas were checked symbolically (sympy) on 2026-11-22. In Lean: unfold over `Fin 4` / `Fin 3` with
      `Fin.sum_univ_four`, `Fin.sum_univ_three`, `Matrix.cons_val_*`, then `ring`.
      Also prove the scaled forms, for `t > 0`: `(b·e)/3 · 1/(√3 t)` is `⟨Au, w⟩`, and `2 (b·e)/3 · 1/(3 t²) =
      2 (b·e)/(9 t²)` is `⟨Ru, Rw⟩`. Finally, `finite_tail` is the finite-`ι` case of G114 (or a direct
      `Finset` proof if G114 is not done yet).
      Docstring: the midpoint rule is exact for quadratics on a triangle, and the weak Green identity identifies these
      sums with boundary integrals. Both are paper arguments, not proved here. The DtN operator is not defined.
      After this compiles, check that the doc's "Verification and provenance" paragraph matches the theorem names; edit
      the doc only if it names theorems the file lacks.
- [x] G120. Strengthen `SteklovAudit/CumulativeBudget.lean` before anything cites it for (7.29); do this right after G118.
      The current `tail_over_M_is_o` proves only `(C / L) * L → C`, which is not an `o(L)` statement. Add, in the same
      file:
      `tail_littleO_of_cutoff_bound (r : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
        (h : ∀ M : ℝ, 0 < M → ∀ᶠ L in Filter.atTop, |r L| ≤ C * L / M) : r =o[Filter.atTop] id`.
      This is the required order of limits: `M` is fixed first, `L → ∞`, and `C` does not depend on `M`. Proof: use
      `Asymptotics.IsLittleO.of_bound`. Given `η > 0`, take `M := (C + 1) / η > 0`. Then eventually (also `0 ≤ L`)
      `C * L / M = C / (C + 1) * η * L ≤ η * L`, using `div_le_one` and `mul_le_mul_of_nonneg_right`, and `‖id L‖ = L`.
      `tail_eta_form`: the same hypothesis gives `∀ η > 0, ∀ᶠ L in atTop, |r L| ≤ η * L` (a direct corollary).
      `order_of_limits_matters`: with `r := id` and a constant that may depend on `M` (`C_M := M`),
      `∀ M > 0, ∀ᶠ L in atTop, |r L| ≤ M * L / M` holds, but `¬ (id =o[atTop] (id : ℝ → ℝ))`. Use
      `Asymptotics.isLittleO_iff` at `c := 1/2` with `L = max L₀ 1`. This shows the `M`-uniform constant is essential.
      Make the docstrings literal: `tail_over_M_is_o` states what it proves and points to `tail_littleO_of_cutoff_bound`.
      `uniform_defect_is_O` is an associativity identity and `time_factor_preserves_o` is `|S ε| ≤ S |ε|`; neither
      docstring may claim more than that. Keep all three old names, since other files may import them.
      Theorem names: `tail_littleO_of_cutoff_bound`, `tail_eta_form`, `order_of_limits_matters`.
      F table text: an error bounded by `C·L/M` for every fixed `M`, with `C` uniform in `M`, is `o(L)`. This is the
      abstract step from the fixed-`M` (7.29) bound. The operator estimate giving `|r L| ≤ C L / M` remains open.

Items G122–G127 added on 2026-11-22 from Josiah's review package `SteklovNextProofs` (interactive session). The review's point: G109–G112 tidy the pinned-row interfaces but would not establish any DtN data,
while these items replace assumed spectral sums by derivations and expose a missing condition in the H5 cutoff route.
Already landed from the package: `ReviewCandidates.lean` (7 lemmas; projection proof fixed with `abel` in 61c90d7),
`ReviewExtensions.lean` (6 lemmas: `spectral_sums_of_operator`, `summable_energy_tail`, `square_sum_strong_tail`,
`hs_right_tail_of_adjoint_strong`, `centered_second_order_bound`, `countable_centered_remainder_bound`), and
`AbstractHSDefectClosed.lean` (5280adb: `ProjFrobeniusContraction` discharged from symmetry and idempotence). Do not
re-add these under another namespace; import them. None of this constructs the DtN operator or proves any of H1–H6.

- [x] G122. `SteklovAudit/H5CutoffTerminal.lean` (imports `SteklovAudit.H5CutoffInterface`): the terminal condition the
      cutoff route is missing. `full_trace_matches` gives `S_L − D L = o(L)`; to get `D L = o(L)` one also needs
      `S_L = o(L)`. Define `FullTraceSmall Y : Prop := ∀ η > 0, ∃ L₀, ∀ L ≥ L₀, |(Y.X L).S (Y.F L)| ≤ η * L` and prove
      `h5_of_cutoff_route (Y) (D) (h1 : Y.RatioLittleO) (h2 : Y.TraceMatches D) (h3 : FullTraceSmall Y) :
      ∀ η > 0, ∃ L₀, ∀ L ≥ L₀, |D L| ≤ η * L` (`full_trace_matches` at `η/2`, `h3` at `η/2`, `abs_sub_abs_le_abs_sub`,
      `max`). Also correct the `H5CutoffInterface` module docstring: replace "exactly two estimates" by three, the third
      being `S_L = o(L)` (docstring-only edit; no statement changes). Theorem names: `h5_of_cutoff_route`.
      F table text: the cutoff route needs (i) ratio `o(L)`, (ii) truncated-trace matching, and (iii) full-trace
      smallness `S_L = o(L)`; (iii) is open and cannot be dropped (G123).
      Written by the formalize task 2026-11-22 in `SteklovAudit/H5CutoffTerminal.lean` (uncompiled at push, commit
      7388fef): def `FullTraceSmall`; theorem `h5_of_cutoff_route`; `H5CutoffInterface` docstring now lists three
      estimates (no statement changes). Next run: tick if STATUS shows it compiled.
      Ticked 2026-11-22: STATUS PASS 1209/1209 at db578cf, `h5_of_cutoff_route` verified.
- [x] G123. `SteklovAudit/H5CutoffObstruction.lean` (imports Mathlib only): the block example showing (iii) cannot be
      dropped. Probe `j` sits on the 2-dimensional block with eigenvalues `2j, 2j+2`, weights `1/2, 1/2`, and
      `μ_j = 2j + 1`; `F x = cos (π x)`. Prove, for each `j : ℕ`: mass `1/2 + 1/2 = 1`; squared defect
      `(−1)²/2 + 1²/2 = 1`; first moment `(−1)/2 + 1/2 = 0`; centered value
      `(cos (π·2j) − cos (π(2j+1)))/2 + (cos (π(2j+2)) − cos (π(2j+1)))/2 = 2` (use `Real.cos_nat_mul_pi` or
      `Real.cos_add_pi`, `Real.cos_nat_mul_two_pi`). Summing `n` probes: `S = 2n`, `E = n`, and with `L = 4n`,
      `μ* = 2n − 1`, the ratio `π · n / (4n − (2n − 1)) = π n / (2n + 1) ≤ π / 2`, so `ratio ≤ η L` eventually. With
      `D(4n) := 2n` truncated matching is exact (all eigenvalues `≤ 2n < 4n`), yet `D(4n) / (4n) = 1/2`.
      Theorem names: `block_mass`, `block_defect`, `block_first_moment`, `block_centered`, `obstruction_sum`
      (`∑ j < n` of the centered values is `2n`), `obstruction_ratio_le`. Docstring: an obstruction to the abstract
      implication, not a counterexample to the tetrahedral theorem.
- [x] G124. `SteklovAudit/AffineWitnessFromOperator.lean` (imports `SteklovAudit.AffineEigenbasisWitness`,
      `SteklovAudit.ReviewExtensions`): derive the witness fields instead of assuming them. Hypotheses (named): a real
      inner-product space `H`, domain `D : Submodule ℝ H`, symmetric `A : D →ₗ[ℝ] H`, Hilbert basis `b` of
      eigenvectors in `D` with eigenvalues `lam`, four probes `u : Fin 4 → D` with `∑ ‖u j‖² = 4` and
      `∑ ‖A (u j) − muVec a j • u j‖² = 16 / a²`. Define `witnessOfOperator : AffineEigenbasisWitness ι a` with
      `J i j := ⟪b i, u j⟫`, fields from `spectral_sums_of_operator`. Theorems: `witnessOfOperator_lam` (rfl),
      `cutoff_of_operator` (G115 bound from the operator data via `cutoff_of_witness`). F table text: the two Parseval
      fields of the affine witness follow from symmetry, an eigenbasis in the domain, and two geometric norm
      identities; the operator, eigenbasis and norm identities stay hypotheses.
- [x] G125. `SteklovAudit/TaylorRemainder.lean` (imports Mathlib only): the calculus bridge the centered bound needs.
      `taylor_remainder_of_lipschitz_deriv (F F' : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hd : ∀ x, HasDerivAt F (F' x) x)
      (hL : ∀ x y, |F' x − F' y| ≤ B * |x − y|) (x y : ℝ) : |F x − F y − F' y * (x − y)| ≤ B / 2 * (x − y) ^ 2`.
      Proof route: `g t := F t − F y − F' y * (t − y) − B/2 * (t − y)²` and its mirror, monotonicity from the
      derivative sign (`monotoneOn_of_deriv_nonneg` / `image_le_of_deriv_right_le_deriv_boundary`), or integrate
      `F' t − F' y` with `intervalIntegral.integral_eq_sub_of_hasDerivAt`. Keep it under 120 lines; split `x ≥ y` /
      `x ≤ y` if needed. F table text: `C¹,¹` regularity with constant `B` gives the second-order remainder `B/2`.
- [x] G126. `SteklovAudit/AffineFullTrace.lean` (imports `SteklovAudit.AffineWitnessFromOperator`,
      `SteklovAudit.TaylorRemainder`): the whole centered trace, not only its tail. Add the residual-orthogonality
      hypothesis `⟪u j, A (u j) − muVec a j • u j⟫ = 0` for each probe; get the first moments from
      `ReviewCandidates.residual_first_moment`, combine with `F' (μ_j)` into `HasSum linear 0`, then
      `countable_centered_remainder_bound` with `C = B/2`, `E = 16/a²`. Theorem: `affine_full_trace_le :
      Summable value ∧ |∑' p, value p| ≤ 8 * B / a ^ 2`. F table text: on the affine probes the full centered trace is
      `O(B/a²)` given `C¹,¹` regularity and residual orthogonality; for a growing family this route needs
      `B_L E_L = o(L)` and orthogonality for the actual identification (not automatic for tetrahedron–wedge).
- [x] G127. `SteklovAudit/TriangleQuadrature.lean` (imports Mathlib only): independent integrals on the reference
      triangle `{(s,t) : 0 ≤ s, 0 ≤ t, s + t ≤ 1}`, so that `TetraAffineFlux`'s midpoint sums can later be identified
      with boundary integrals. Prove `∫ 1 = 1/2`, `∫ s = 1/6`, `∫ s² = 1/12`, `∫ s t = 1/24` as iterated
      interval integrals (`intervalIntegral.integral_pow`, `integral_id`, `ring`), and that the edge-midpoint rule
      `(1/6)(f(½,0) + f(0,½) + f(½,½))` gives the same four values (`norm_num`). Theorem names: `tri_int_one`,
      `tri_int_s`, `tri_int_ss`, `tri_int_st`, `midpoint_rule_exact_deg2`. F table text: the midpoint rule used in
      `TetraAffineFlux` is exact for quadratics on a triangle (iterated-integral form; the surface measure on the
      tetrahedron's faces is not built here).

Ticked 2026-11-22 (interactive session): CI PASS 1209/1209 at db578cf; all 48 theorems of the eight modules below are `verified (standard axioms only)` (G123 and G127 needed one proof fix each, 8cdfecd; G112's `massLin` was repaired in a9f44a7/db578cf).
Status of G123–G127 (interactive session, 2026-11-22, commit 6e3a224, uncompiled at push): all five are written —
`H5CutoffObstruction.lean` (G123), `AffineWitnessFromOperator.lean` (G124: `AffineOperatorData`, `witnessOfOperator`,
`parseval_of_operator`, `cutoff_of_operator`), `TaylorRemainder.lean` (G125: `taylor_remainder_of_lipschitz_deriv`),
`AffineFullTrace.lean` (G126: `ResidualOrth`, `weighted_first_moment`, `affine_full_trace_le`), `TriangleQuadrature.lean`
(G127: `tri_int_one/s/ss/st`, `midpoint_rule_exact_deg2`, `midpoint_eq_integral`). Also added: `H5CutoffTerminalIff.lean`
(converse of G122: given (i) and (ii), `D = o(L)` ⇔ `FullTraceSmall`), `AffineParsevalDischarge.lean` (mass `4`, defect
`16/a²` and residual orthogonality derived from the named `BoundaryIdentification` via `TetraAffineFlux` and
`ResidualLink`), and `CumulativeBudgetSplit.lean` (`littleO_of_split`: fixed-`M` part `o(L)` plus uniform tail
`C L / M` gives `o(L)`). The formalize task should NOT rewrite these: next run, read STATUS; tick each item whose
theorems are verified, and if one failed, fix it minimally from the compiler messages (that counts as the run's one thing).

Items G128–G132 written by the formalize task on 2026-11-22 (requested by Josiah in an interactive session), after
G122–G127. They split the "later directions" below into one-run steps and attack the open row (iii) of G122. None of
them constructs the DtN operator or proves H1–H6, (7.29) or Theorem 1.3 / 11.1.

- [x] G128. `SteklovAudit/H5CutoffSplitTerminal.lean` (imports `SteklovAudit.H5CutoffTerminal`,
      `SteklovAudit.CumulativeBudgetSplit`): replace row (iii) `FullTraceSmall` by the split input. Named hypothesis
      `FullTraceSplit Y`: for each `M` a fixed-`M` part `P M L` with `P M L = o(L)` and a tail
      `|S_L − P M L| ≤ C L / M` (`C` independent of `M`, `L`). Theorems: `fullTraceSmall_of_split` (via
      `littleO_of_split`), `h5_of_cutoff_split` (feed it to `h5_of_cutoff_route`). F table text: (iii) reduces to a
      fixed-window estimate plus a uniform high-energy tail `C/M`, the same shape as the τ(M) row.
      Ticked 2026-11-22 by the formalize task: STATUS (CI PASS at 53fc56e) lists `fullTraceSmall_of_split`,
      `h5_of_cutoff_split`, `fullTraceSplit_of_small`, `fullTraceSplit_iff` as verified (standard axioms only).
- [x] G129. `SteklovAudit/DuhamelSpectral.lean` (imports Mathlib only): the HS Duhamel bound in spectral coordinates,
      keeping the `|t|` factor. For reals `a b t`: `duhamel_entry_le : ‖Complex.exp (-(t * a) * I) −
      Complex.exp (-(t * b) * I)‖ ≤ |t| * |a − b|` (via `‖e^{iθ} − 1‖ ≤ |θ|`). For finite `J : Fin m → Fin n → ℂ`,
      `lam`, `mu`: `duhamel_hs_le : ∑ i j, ‖J i j‖² * ‖e^{−itλ_i} − e^{−itμ_j}‖² ≤ t² * ∑ i j, ‖J i j‖² * (λ_i − μ_j)²`.
      F table text: the commutator defect (the HS defect row) controls the propagated difference linearly in `|t|`;
      no operator domain issues arise in finite spectral coordinates.
      Written by the formalize task 2026-11-22 in `SteklovAudit/DuhamelSpectral.lean` (uncompiled at push, commit
      928d6a6): `exp_sub_one_le`, `duhamel_entry_le` (phases stated with real arguments `((-(t * a) : ℝ) : ℂ) * I`),
      `duhamel_hs_le`. Next run: tick if STATUS shows it compiled.
      Ticked 2026-11-22: CI run 514 (on the G129 roadmap-note commit) Build and Axiom audit steps succeeded with the file present;
      the dependency map lists `DuhamelSpectral` with 3 theorems. Its "Commit status if changed" step lost a push race,
      so STATUS.md still shows the 20:22 UTC run; the next status write will list the three theorems.
- [x] G130. `SteklovAudit/FourierOneOverT.lean` (imports Mathlib only): the `1/t` cancellation in the cumulative
      Fourier integral. Hypotheses: `g w : ℝ → ℝ`, `|g t| ≤ |t| * ε`, `|w t| * |t| ≤ C` for all `t`, `0 ≤ T`,
      `IntervalIntegrable (fun t => w t * g t) volume (-T) T`. Theorem `fourier_cancel_le :
      |∫ t in (-T)..T, w t * g t| ≤ 2 * T * C * ε` (`intervalIntegral.abs_integral_le_integral_abs`,
      `intervalIntegral.integral_mono_on`, constant integral). F table text: with G129, a Fourier window of width
      `T` turns an `O(|t| ε)` propagated defect into an `O(T ε)` count error.
      Done 2026-11-22 by the formalize task (commit e08737d; CI PASS 1220/1220): `fourier_cancel_le` (no integrability
      hypothesis needed, via `intervalIntegral.norm_integral_le_of_norm_le_const`), `fourier_cancel_inv` (weight
      `t⁻¹`), `inv_weight_ok`, `eps_nonneg_of_bound`.
- [x] G131. `SteklovAudit/HSBasisIndependence.lean` (imports Mathlib only): basis independence of the HS sum in finite
      dimension. For `T : E →ₗ[ℝ] F` (finite-dimensional inner product spaces) and orthonormal bases `b c` of `E`
      (`OrthonormalBasis ι ℝ E`, `OrthonormalBasis κ ℝ E`): `hs_sum_basis_indep : ∑ i, ‖T (b i)‖² = ∑ j, ‖T (c j)‖²`
      (expand in an orthonormal basis `d` of `F` and use Parseval, `OrthonormalBasis.sum_sq_norm_inner`, on both
      sides; the common value is `∑ i k, ⟪d k, T (b i)⟫²`). Theorem `hs_sum_eq_double` records that common value.
      F table text: the HS defect row does not depend on the eigenbasis chosen for the model or the true operator.
      Written by the formalize task 2026-11-22 (commit e837800, uncompiled at push): `parseval_sq` (via
      `OrthonormalBasis.sum_inner_mul_inner`, fallback through `repr`), `hs_sum_eq_double`, `hs_sum_eq_adjoint`
      (common value `∑ k, ‖T† (d k)‖²`, via `LinearMap.adjoint_inner_right`), `hs_sum_basis_indep` (through
      `stdOrthonormalBasis ℝ F`), `hs_sum_id` (non-vacuity: `T = id` gives `card ι`). Next run: tick if STATUS shows it compiled.
      Ticked 2026-11-22: all `HSBasisIndependence` theorems verified in STATUS at a299b9a (1239/1239).
- [x] G132. `SteklovAudit/FullTraceSmallSeparate.lean` (imports `SteklovAudit.H5CutoffTerminal`): (iii) is not the
      target in disguise. Build an `H5EdgeFamilyCutoff` with `S_L = 0` for all `L` (zero weights, if
      `CountableCutoffTail.Cert` allows them; check its fields first) and `D L := L`. Theorems: `fullTraceSmall_zero`
      (`FullTraceSmall` holds), `not_littleO_D` (`D` is not `o(L)`), `traceMatches_fails` (so (ii) is what
      links (iii) to `D`). If `Cert` cannot carry zero weights, use the smallest admissible certificate and say so
      in the docstring. F table text: (iii) is a statement about the probe family alone and carries no information
      about `E − E_mod` without (ii).
      Done 2026-11-22 by the formalize task (commit 6df61ee; CI PASS 1239/1239 at a299b9a): `zeroCert`/`zeroFamily`
      (zero weights are allowed), `S_zero`, `fullTraceSmall_zero`, `ratio_small`, `not_littleO_idD`, `traceMatches_fails`,
      `fullTraceSmall_not_target`.
- [x] G133. `SteklovAudit/CumulativeBudgetQuantifiers.lean` (imports `SteklovAudit.CumulativeBudget`,
      `SteklovAudit.CumulativeBudgetSplit`): close the remaining quantifier / order-of-limits forms of the (7.29) budget
      (table row "Abstract cumulative budget refinement"). Theorems: `littleO_of_approx`, `approx_of_littleO`,
      `approx_iff` (`r = o(L)` iff every `δ > 0` has an `o(L)` approximant `m` with `|r − m| ≤ δ L` eventually);
      `littleO_of_split_rate` (tail `c(M) L` with `c(M) → 0` suffices; `C/M` uniform is a special case);
      `littleO_of_split_nat` (integer cutoffs `M ≥ 1` suffice); `littleO_of_window_defect`,
      `littleO_of_window_defect'` (for every window `T > 0`, `|r L| ≤ C L / T + K T L ε(1/L)` with `C, K ≥ 0` uniform
      and `ε(h) → 0` gives `o(L)`: the shape after G129/G130); `window_needs_vanishing` (`ε ≡ 1`, `r = id`: the
      vanishing of `ε` cannot be dropped). F table text: every order-of-limits step of (7.29) is closed at the scalar
      level; the uniform tails `C L / M`, `C L / T` and the HS defect `ε(h) → 0` for the actual operator stay open.
      Written by an interactive session 2026-11-22 (commit d4f634b, uncompiled at push; Josiah said "go ahead" on this row).
      Next run: tick if STATUS shows its 8 theorems verified; if it failed, fix it minimally from the compiler messages.
      Ticked 2026-11-22: all 8 theorems verified in STATUS at a299b9a (1239/1239).

Items G134–G137 written by the formalize task on 2026-11-22 (requested by Josiah in an interactive session). They connect
G129/G130 to G133 and restate rows (i) and (iii) of the H5 cutoff route as weaker named inputs. None of them constructs
the DtN operator or proves H1–H6, (7.29) or Theorem 1.3 / 11.1.

- [x] G134. `SteklovAudit/DuhamelWindow.lean` (imports `SteklovAudit.DuhamelSpectral`, `SteklovAudit.FourierOneOverT`):
      chain G129 into G130 for finite spectral data `J lam mu`. Define `hsDiff t := √(∑ i j, ‖J i j‖² ‖e^{−itλ_i} −
      e^{−itμ_j}‖²)` and `hsDefect := √(∑ i j, ‖J i j‖² (λ_i − μ_j)²)`. Theorems: `hsDiff_le : hsDiff t ≤ |t| * hsDefect`
      (`Real.sqrt_le_sqrt` on `duhamel_hs_le`, `Real.sqrt_mul_self` / `Real.sqrt_sq_eq_abs`), `window_hsDiff_le :
      |∫ t in (-T)..T, t⁻¹ * hsDiff t| ≤ 2 * T * hsDefect` (`fourier_cancel_inv`). F table text: a window of width `T`
      turns the HS commutator defect into an `O(T · defect)` bound, the `K T L ε(1/L)` term of G133.
      Written by the formalize task 2026-11-22 (uncompiled at push): `hsDiff`, `hsDefect`, `hsDiff_nonneg`,
      `hsDefect_nonneg`, `hsDiff_le`, `window_hsDiff_le`, `hsDiff_zero`, `hsDiff_eq_zero_of_defect`, `hsDefect_example`.
      Next run: tick if STATUS shows it compiled. Note: the earlier commit 5f07cf2 labelled "G134" added
      `SteklovAudit/ModelEdgeLawReduction.lean` (scalar reductions behind (7.38)/(7.45)); it is not this item. It compiled
      after the fixes 49864a0/59e06b5 (CI run #531: 1249/1249 verified at 59e06b5).
      Ticked 2026-11-22: all 7 `DuhamelWindow` theorems verified at ec4e551 (1256/1256) after the fix that passes
      `|hsDiff t| ≤ |t| hsDefect` (via `hsDiff_nonneg`) to `fourier_cancel_inv`.
- [x] G135. `SteklovAudit/WindowDefectFullTrace.lean` (imports `SteklovAudit.H5CutoffTerminal`,
      `SteklovAudit.CumulativeBudgetQuantifiers`): replace row (iii) by the window-shaped input. Named hypothesis
      `WindowTraceBound Y C K ε`: `0 ≤ C`, `0 ≤ K`, `ε h → 0` as `h → 0⁺` (in the form G133 uses), and for every
      `T > 0`, eventually `|S_L| ≤ C L / T + K T L ε (1/L)`. Theorems: `fullTraceSmall_of_window` (via
      `littleO_of_window_defect`), `h5_of_cutoff_window` (with (i), (ii) and `h5_of_cutoff_route`). F table text: (iii)
      follows from a uniform window tail `C/T` plus a vanishing HS defect, the shape G129/G130 produce.
      Written by the formalize task 2026-11-22 (uncompiled at push): structure `WindowTraceBound` (fields `C_nonneg`,
      `K_nonneg`, `eps_small`, `bound`), `fullTraceSmall_of_window`, `h5_of_cutoff_window`,
      `windowTraceBound_of_trace_zero` (non-vacuity). Next run: tick if STATUS shows it compiled.
      Ticked 2026-11-23: all 3 theorems verified at a44d808 (CI run #537, 1259/1259; the run is marked failed only
      after verification, in the status push).
- [x] G136. `SteklovAudit/H5CutoffRatioSufficient.lean` (imports `SteklovAudit.H5CutoffInterface`): replace row (i)
      by two named inputs. `GapLinear Y c L₁`: `0 < c` and `c * L ≤ L − μ*(L)` for `L ≥ L₁`; `EnergySmall Y`:
      `∀ η > 0, eventually Lip L * E_L ≤ η * L²` (with `E_L` the certificate's `E`). Theorem
      `ratioLittleO_of_gap_energy` (`div_le_iff₀`, `nlinarith`); also `ratio_le_of_gap` (`ratio L ≤ Lip L * E_L /
      (c L)` for `L ≥ max L₁ 1`). F table text: (i) holds if the comparison values keep a linear gap below the cutoff
      and `Lip · E = o(L²)`; both stay open for the actual edge family.
      Written by the formalize task 2026-11-23 (uncompiled at push): `GapLinear`, `EnergySmall`, `ratio_le_of_gap`
      (with the extra hypothesis `0 ≤ Lip L · E_L`, needed for monotonicity in the denominator),
      `ratioLittleO_of_gap_energy`. Next run: tick if STATUS shows it compiled.
      Ticked 2026-11-23: all theorems of `H5CutoffRatioSufficient` verified at d9fc37b (CI PASS, 1261/1261).
- [x] G137. `SteklovAudit/H5CutoffWeakRows.lean` (imports `SteklovAudit.WindowDefectFullTrace`,
      `SteklovAudit.H5CutoffRatioSufficient`, `SteklovAudit.FullTraceSmallSeparate`): assemble and check. Theorem
      `h5_of_weak_rows`: (ii) + `GapLinear` + `EnergySmall` + `WindowTraceBound` give `|D L| = o(L)`. Non-vacuity:
      `zeroFamily` (G132) satisfies `GapLinear` (`c = 1/2`, `L₁ = 1`), `EnergySmall` and `WindowTraceBound`
      (`C = K = 0`, `ε = 0`); theorem `weak_rows_zeroFamily`. F table text: the cutoff route now runs on (ii) plus three
      weaker named inputs, each satisfiable; (ii) remains the geometric question.
      Written by Josiah's interactive session 2026-11-23 at c629c72 (uncompiled at push): `h5_of_weak_rows`,
      `gapLinear_zeroFamily`, `energySmall_zeroFamily`, `windowTraceBound_zeroFamily`, `weak_rows_zeroFamily`, and
      `weak_rows_need_traceMatches` ((ii) cannot be dropped: the zero family meets the three weaker inputs but not
      `TraceMatches idD`). Next run: tick if STATUS shows it compiled; if it failed, fix it first.
      Ticked 2026-11-23: all 6 theorems verified at 9cc1a86 (CI PASS, 1267/1267).

Later directions from the same review (too large for one run; listed so they are not lost): the HS-valued Duhamel
identity with domain hypotheses and the bound `‖(e^{−itA}J − Je^{−itB})Z_h‖_HS ≤ |t| ε(h)` (keep the `|t|` factor so
the cumulative Fourier integral's `1/t` cancels), then the trace comparison with local mass `O(h⁻¹)`; basis
independence of the HS norm; affine harmonic functions in the DtN domain with the stated normal derivatives. These are now G138–G142
below.

Items G138–G142 added by Josiah's interactive session on 2026-11-23. They split the "later directions" above into
one-run steps. Everything stays finite-dimensional: the operators are matrices given with their diagonalizations,
and the Steklov / DtN operator, its domain and its eigenbasis remain named hypotheses. Each file states in its
docstring what it does NOT prove, and none claims (7.29), H5 or Theorem 1.3 / 11.1.

- [x] G138. `SteklovAudit/HSBasisIndependence.lean` (imports Mathlib only): the HS norm does not depend on the
      orthonormal basis. For `M : Matrix (Fin m) (Fin n) ℂ` put `hsSq M := ∑ i, ∑ j, ‖M i j‖ ^ 2`. Theorems:
      `hsSq_eq_trace` (`hsSq M = (Matrix.trace (Mᴴ * M)).re`; `Matrix.trace`, `Matrix.mul_apply`,
      `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`), `hsSq_unitary_left` (`U ∈ Matrix.unitaryGroup (Fin m) ℂ →
      hsSq (U * M) = hsSq M`: `Mᴴ Uᴴ U M = Mᴴ M`), `hsSq_unitary_right` (`V ∈ unitaryGroup (Fin n) ℂ → hsSq (M * V)
      = hsSq M`: `Matrix.trace_mul_comm` to move `V Vᴴ` together), `hsSq_conj_unitary` (both sides), and
      `hsSq_nonneg`. F table text: the spectral-coordinate HS norms used in G129/G134 equal the HS norm of the
      operator in any orthonormal basis.
      Written by the formalize task 2026-11-23 (uncompiled at push): `hsSq`, `re_star_mul_self`, `hsSq_nonneg`,
      `hsSq_zero`, `hsSq_eq_trace`, `unitary_ct_mul_self`, `unitary_mul_ct_self`, `hsSq_unitary_left`,
      `hsSq_unitary_right`, `hsSq_conj_unitary` (types are general `Fintype`s, so `Fin m`, `Fin n` apply).
      Next run: tick if STATUS shows it compiled.
      Ticked 2026-11-23: all 9 theorems of `HSBasisIndependence` verified (CI PASS at e5f24d5, 1271/1271; #548 at
      24a73a2 also passed).
- [x] G139. `SteklovAudit/DuhamelOperatorFin.lean` (imports `SteklovAudit.DuhamelSpectral`,
      `SteklovAudit.HSBasisIndependence`): the HS Duhamel bound for matrices given with diagonalizations, the
      finite-dimensional stand-in for "domain hypotheses". `structure Diag (n)`: `U ∈ unitaryGroup (Fin n) ℂ`, real
      eigenvalues `ev : Fin n → ℝ`. `def Diag.op D := U * diagonal (fun i => (ev i : ℂ)) * Uᴴ` and `def Diag.prop D
      t := U * diagonal (fun i => exp ((-(t * ev i) : ℝ) * I)) * Uᴴ` (the propagator `e^{−itA}`; no matrix
      exponential needed). For `DA : Diag m`, `DB : Diag n`, `J : Matrix (Fin m) (Fin n) ℂ` put `Jhat := DA.Uᴴ * J *
      DB.U`. Theorems: `defect_coords` (`DA.Uᴴ * (DA.op * J − J * DB.op) * DB.U = fun i j => (ev_A i − ev_B j) *
      Jhat i j`), `prop_coords` (same for `DA.prop t * J − J * DB.prop t` with the phase differences), and
      `duhamel_hs_matrix : hsSq (DA.prop t * J − J * DB.prop t) ≤ t ^ 2 * hsSq (DA.op * J − J * DB.op)` (G138 to
      pass to coordinates, then `duhamel_hs_le` on `Jhat`; `Matrix.ext`, `Matrix.mul_apply`, `Matrix.diagonal_mul`,
      `Matrix.mul_diagonal`, `unitary.star_mul_self`). Use `Fin m`, `Fin n` throughout so `duhamel_hs_le` applies
      unchanged. F table text: the HS Duhamel bound with the `|t|` factor holds for the operators, not only in
      spectral coordinates, whenever both sides are given with orthonormal eigenbases.
      Written by the formalize task 2026-11-23 (uncompiled at push): `Diag` (fields `U`, `hU`, `ev`), `Diag.op`,
      `Diag.prop`, `conj_comm_coords`, `defect_coords`, `prop_coords`, `hsSq_ct_left`, `hsSq_coords`, `hsSq_of_mul`,
      `norm_ofReal_sub_sq`, `duhamel_hs_matrix`, `duhamel_hs_matrix_zero` (non-vacuity). Next run: tick if STATUS
      shows it compiled.
      Ticked 2026-11-23: all 9 theorems verified at 2b43bc9 (CI PASS, 1285/1285), after a repair of the ill-typed
      `duhamel_hs_matrix_zero` statement (second `0` annotated).
- [x] G140. `SteklovAudit/DuhamelLocalized.lean` (imports `SteklovAudit.DuhamelOperatorFin`): the localized
      form `‖(e^{−itA}J − Je^{−itB}) Z_h‖_HS ≤ |t| ε(h)`. `Z` is a function of `B`: `Zof DB z := DB.U * diagonal z *
      DB.Uᴴ` with `z : Fin n → ℂ`. Theorems: `prop_comm_Z` (`DB.prop t * Zof DB z = Zof DB z * DB.prop t`, diagonal
      matrices commute), `op_comm_Z`, `localized_eq` (`(DA.prop t * J − J * DB.prop t) * Z = DA.prop t * (J * Z) − (J
      * Z) * DB.prop t`), `duhamel_localized_sq` (`hsSq ((DA.prop t * J − J * DB.prop t) * Z) ≤ t ^ 2 * hsSq ((DA.op *
      J − J * DB.op) * Z)`, G139 with `J * Z`), and with the named hypothesis `DefectSmall (Zh : ℝ → Matrix ..) (ε :
      ℝ → ℝ) : ∀ h, 0 < h → hsSq ((DA.op * J − J * DB.op) * Zh h) ≤ ε h ^ 2` the square-root form
      `duhamel_localized_le` (`√(hsSq ..) ≤ |t| * |ε h|`, as in G134). Non-vacuity: `J = 0` (or `A = B`, `J = 1`)
      satisfies `DefectSmall` with `ε = 0`. F table text: once the localized defect `‖(AJ − JB) Z_h‖_HS ≤ ε(h)` is
      known, the localized propagated difference is `≤ |t| ε(h)`; the defect bound itself is the open HS row.
      Written by the formalize task 2026-11-23 (uncompiled at push): `Zof`, `conj_diag_mul`, `diagonal_mul_comm`,
      `conj_diag_comm`, `prop_comm_Z`, `op_comm_Z`, `localized_eq` (general `P J Q Z` with `Q Z = Z Q`),
      `duhamel_localized_sq`, `DefectSmall` (with `Z_h = Zof DB (zh h)`), `duhamel_localized_le`, `defectSmall_zero`
      (non-vacuity, `J = 0`, `ε = 0`). Next run: tick if STATUS shows it compiled.
      Ticked 2026-11-23: all 9 theorems of `DuhamelLocalized` verified (CI PASS at 8cf3cb6, 1298/1298).
- [x] G141. `SteklovAudit/TraceLocalMass.lean` (imports `SteklovAudit.AbstractTransfer`): the trace comparison with
      local mass `O(h⁻¹)`. For `D : AbstractTransfer.Data ι κ` (finite), Lipschitz `f` with constant `Lf ≥ 0`:
      `trace_cs : |∑ i, ∑ j, (f (D.a i) − f (D.b j)) * D.J i j ^ 2| ≤ Lf * √(hs2 D.K) * √(hs2 D.J)` (from
      `trace_transfer`, then Cauchy–Schwarz `Finset.inner_mul_le_norm_mul_norm` or `Finset.sum_mul_sq_le_sq_mul_sq`,
      as in G109). Named inputs at scale `h > 0`: `hs2 D.K ≤ ε ^ 2` (defect) and `hs2 D.J ≤ Mloc / h` (local mass).
      `trace_local_mass_le : .. ≤ Lf * |ε| * √(Mloc / h)`. Scalar corollary `littleO_of_bounded_defect`: if along a
      family `Lf L ≤ Λ`, `|ε L| ≤ ε₀` and `h = 1/L`, the bound `Λ ε₀ √(Mloc L)` is `o(L)` (`√L ≤ η L` for large `L`).
      Docstring must say plainly that `Lf` of the paper's cumulative multipliers may grow with `L`, so this corollary
      is the bounded-Lipschitz case only. F table text: with a bounded defect and `O(h⁻¹)` local mass, the
      Lipschitz trace comparison is `O(√L)`, hence `o(L)`, for multipliers with bounded Lipschitz constant.
      Written by the formalize task 2026-11-23 at 2ae625a (roadmap note was missing). Ticked 2026-11-23: `trace_cs`,
      `trace_local_mass_le`, `littleO_of_bounded_defect`, `hs2_zero_array` verified (CI PASS at 8cf3cb6, 1298/1298).
- [x] G142. `SteklovAudit/Foundations/AffineHarmonic3D.lean` (imports Mathlib; Foundations, so the audit's
      subdirectory rule from G118 applies): affine functions on `ℝ³` and their normal derivatives on the reference
      tetrahedron of `TetraAffineFlux` (vertices `(1,1,1)`, `(1,−1,−1)`, `(−1,1,−1)`, `(−1,−1,1)`; face opposite `v`
      has outward normal `−v / √3`). Work with `x y z : ℝ` as in `HalfPlaneDtN`. `u c p q r x y z := c + p x + q y
      + r z`. Theorems: `hasDerivAt_u_x`, `_y`, `_z` (first partials `p`, `q`, `r`), `second_partials_zero` (each
      second partial is `0`, so `Δu = 0`), `normal_derivative` (`HasDerivAt (fun s => u .. (x + s n₁) (y + s n₂) (z +
      s n₃)) (p n₁ + q n₂ + r n₃) 0`), and `face_flux_values` (the four normal derivatives with `n = −v / √3`, e.g.
      `−(p + q + r) / √3` on the face opposite `(1,1,1)`), plus `face_flux_sum_zero` (the four values sum to `0`, the
      discrete divergence theorem for affine `u`). What it does NOT prove: that `u|∂T` lies in the DtN domain
      (`H^{1/2}` traces, weak normal derivative), that the DtN map sends the trace to these values, the Green
      identity, or Parseval for the probes. F table text: affine harmonic functions have constant normal derivative
      on each face, with the values that `docs/affine-dtn-cutoff.md` uses; membership in the DtN domain stays a
      paper step.
      Written by the formalize task 2026-11-23 at d8d89a5 (uncompiled at push): `u`, `hasDerivAt_u_x`, `_y`, `_z`,
      `second_partials_zero`, `laplacian_zero`, `normal_derivative_at`, `normal_derivative`, `flux`,
      `face_normal_derivative`, `face_flux_values`, `face_flux_sum_zero`. Next run: tick if the build compiled it
      (STATUS may not list Foundations files, see G118); if it failed, fix it first.
      Ticked 2026-11-23 by the formalize task: STATUS PASS 1308/1308 at d8d89a5 lists all 10 theorems of
      `Foundations/AffineHarmonic3D` as verified (standard axioms only).

Items G143–G145 written by the formalize task on 2026-11-23 (no unchecked A–G item was left after G142; the F3.1–F5.3
items below belong to the separate foundations task). Rows served, from Josiah's priority table: G143 and G144 serve
row 2 (affine Parseval discharge: the spectral-theorem passage and a non-vacuity check of `BoundaryIdentification`);
G145 serves row 3 (abstract cumulative budget refinement) as a one-run reduction toward row 5 (localized HS defect).
Everything is finite-dimensional or scalar. None of them constructs the DtN operator or proves H1–H6, (7.29) or
Theorem 1.3 / 11.1.

- [ ] G143. `SteklovAudit/AffineSpectralPassageFin.lean` (imports `SteklovAudit.AffineParsevalDischarge`): the
      finite-dimensional spectral-theorem passage for `AffineOperatorPre` (row 2). For a finite-dimensional real
      inner-product space `E` with `hn : Module.finrank ℝ E = n`, `T : E →ₗ[ℝ] E` with `hT : T.IsSymmetric` and probes
      `u : Fin 4 → E`, define `preOfSymmetric hT hn u : AffineOperatorPre E (Fin n)` with `D := ⊤`,
      `A := T ∘ₗ (⊤ : Submodule ℝ E).subtype`, `b := (hT.eigenvectorBasis hn).toHilbertBasis`, `mem` from
      `Submodule.mem_top`, `lam := hT.eigenvalues hn`, `eig` from `hT.apply_eigenvectorBasis` and
      `OrthonormalBasis.coe_toHilbertBasis`, `symm` from `hT`, `u j := ⟨u j, Submodule.mem_top⟩`. Theorems:
      `preOfSymmetric_lam` (rfl), `preOfSymmetric_A_apply` (`A ⟨x, _⟩ = T x`), `full_trace_fin` (given
      `BoundaryIdentification (preOfSymmetric hT hn u) a`, `0 < a` and `C¹,¹` data `F F' B`, the `8 * B / a ^ 2` bound
      via `full_trace_discharged`). Docstring: the DtN operator is infinite-dimensional, so this does NOT discharge the
      Hilbert-basis hypothesis for it; it shows that hypothesis is the only spectral input once the space is finite.
      F table text: in finite dimension the eigenbasis fields of `AffineOperatorPre` come from Mathlib's spectral
      theorem; only `BoundaryIdentification` remains.
- [ ] G144. `SteklovAudit/AffineIdentificationNonvacuous.lean` (imports `SteklovAudit.AffineSpectralPassageFin`):
      `BoundaryIdentification` is satisfiable, so the G126/G143 bounds are not vacuous (row 2, definition check). Target
      values: mass `1` per probe (`mass_phi0`–`mass_phi3` divided by `12`), residual energy `r_j ^ 2` with
      `r_0 = 0` and `r_j ^ 2 = 24 / 12 / (√3 * tPar a) ^ 2` for `j = 1, 2, 3` (`residual_energy_phi0`–`phi3`), mixed
      pairing `0` (`residual_orthogonal`). Model: `E := EuclideanSpace ℝ (Fin 4 × Fin 2)`, `T` block-diagonal with
      blocks `!![muVec a j, r j; r j, 0]` (as `Matrix.toEuclideanLin` of a symmetric matrix), `u j := single (j, 0) 1`,
      so `T u_j − μ_j u_j = r_j • single (j, 1) 1` is orthogonal to `u_j` with norm `|r_j|`. Theorems: `block_residual`,
      `T_symm`, `identification_of_block`, `exists_identification (ha : 0 < a) : ∃ T hT u, BoundaryIdentification
      (preOfSymmetric hT hn u) a`. If this exceeds about 120 lines, prove only `block_residual` and `T_symm` here and
      record the assembly as G144b. F table text: the identification hypothesis is consistent; it carries the geometry
      but is not contradictory.
- [ ] G145. `SteklovAudit/TraceLocalMassGrowth.lean` (imports `SteklovAudit.TraceLocalMass`): relax G141's
      bounded-Lipschitz corollary to growing constants (row 3, toward row 5). Theorems: `littleO_of_growing_lipschitz`
      (for `Λ ε : ℝ → ℝ` with `0 ≤ Λ L`, `0 ≤ ε L`, `0 ≤ Mloc`: if `∀ η > 0, ∃ L₀, ∀ L ≥ L₀, Λ L * ε L ≤ η * √L` then
      `∀ η > 0, ∃ L₀, ∀ L ≥ L₀, Λ L * ε L * √(Mloc * L) ≤ η * L`; `Real.sqrt_mul`, `Real.mul_self_sqrt`, take
      `η / (√Mloc + 1)`), `growing_needs_rate` (`Λ L = √L`, `ε = 1`, `Mloc = 1`: the bound equals `L` for `L ≥ 0`, so
      `Λ ε = O(√L)` alone does not give `o(L)`), and `trace_littleO_of_growth` (a family `D L : Data ι κ` with
      `Lf L`-Lipschitz `f L`, defect `hs2 (D L).K ≤ ε L ^ 2` and local mass `hs2 (D L).J ≤ Mloc * L` (that is `h = 1/L`)
      has trace comparison `o(L)` when `Lf L * ε L = o(√L)`, via `trace_local_mass_le`). F table text: the
      Lipschitz trace comparison is `o(L)` whenever `Lip · defect = o(√L)`; the defect rate for the actual operator
      stays open.

## Foundations (long-term)

Analytic machinery that Mathlib lacks and that the main theorem needs: (G1) Sobolev traces, (G2) Dirichlet-to-Neumann /
Steklov operators, (G3) Kontorovich–Lebedev transform and K_{iν}, (G4) Krein spectral shift, (G5) Mourre estimates and
propagation. Worked by a separate hourly foundations task, one item per run, independent of sections A–G (the item IDs
F1.1–F5.3 are not the section F items F1–F3). Each item is a new file `SteklovAudit/Foundations/<Name>.lean` importing
Mathlib, whose docstring states exactly what is proved and what is not. These are toy, one-dimensional or
finite-dimensional models, not the paper's operator: none of them proves the main theorem or any of `[H1]`–`[H6]`.

- [x] F1.1 1D trace inequality: |f(0)|² ≤ 2∫₀¹(|f|²+|f'|²) for f ∈ C¹[0,1] — file SteklovAudit/Foundations/Trace1D.lean
      Attempted twice 2026-11-21 (9891351, 47f99e7); both failed at the FTC derivative step (`ring` on an
      unreduced `(fun y => y - 1) x` from `HasDerivAt.mul`). Reverted to a docstring-only stub (f28800a), which
      records the diagnosis and the suggested fix `congr_deriv (by beta_reduce; ring)`.
      Third attempt written by an interactive session 2026-11-22 at c395f25 (uncompiled at push): full proof in
      `SteklovAudit/Foundations/Trace1D.lean`, theorems `pointwise_bound`, `trace_1d`. The derivative now uses
      `hasDerivAt_id'` (no `id x` atom) and `congr_deriv` with a separately proved equation. Next run: tick if
      STATUS shows both theorems verified; if it failed, fix from the compiler messages or split F1.1.
      Ticked 2026-11-22 by an interactive session: CI run 45044864204 on 826368c built
      `SteklovAudit.Foundations.Trace1D` with no errors (only unused-fallback warnings, removed in b216ed1).
      STATUS does not list it because `axiom_audit.py` scans only top-level `SteklovAudit/*.lean` (see G118).
- [x] F1.2 half-line trace with constant 1: |f(0)|² ≤ ∫₀^∞(|f|²+|f'|²) for suitable decaying f — file SteklovAudit/Foundations/TraceHalfLine.lean
      Written by an interactive session 2026-11-22 at b216ed1 (uncompiled at push): theorems `cross_abs_le`,
      `trace_halfLine` (hypotheses: `f` C¹ on ℝ, `f → 0` at ∞, `f²`, `f'²` integrable on (0, ∞)). Next run:
      tick if the CI build log shows `SteklovAudit.Foundations.TraceHalfLine` built without errors.
      Ticked 2026-11-22 by an interactive session: STATUS PASS 1121/1121 at bbcf097 (CI run 45052545358), all of
      this file's theorems verified (standard axioms only).
- [x] F2.1 disk Steklov eigenfunctions: r^n cos(nθ), r^n sin(nθ) are harmonic, with normal derivative n·value on the unit circle — file SteklovAudit/Foundations/DiskSteklov.lean
      Written by an interactive session 2026-11-22 at 51d2a38 (uncompiled at push), for real exponent α (α = n gives the
      disk): `hasDerivAt_u_r`, `hasDerivAt_u_rr`, `hasDerivAt_u_θ`, `hasDerivAt_u_θθ` (and `v` versions), `lap_core`,
      `laplacian_polar_u`, `laplacian_polar_v`, `steklov_u`, `steklov_v`. Harmonicity is in polar form
      (u_rr + u_r/r + u_θθ/r² = 0 for r > 0); the Cartesian Laplacian is not derived. Next run: tick if STATUS
      lists these as verified.
      Ticked 2026-11-22 by an interactive session: STATUS PASS 1121/1121 at bbcf097 (CI run 45052545358), all of
      this file's theorems verified (standard axioms only).
- [x] F2.2 half-plane DtN symbol: e^{ikx−|k|y} is harmonic and −∂_y equals |k|·value at y = 0 — file SteklovAudit/Foundations/HalfPlaneDtN.lean
      Written by an interactive session 2026-11-22 at bbcf097, in real form u = cos(kx + φ)·e^{−|k|y}:
      `hasDerivAt_u_x`, `hasDerivAt_u_xx`, `hasDerivAt_u_y`, `hasDerivAt_u_yy`, `laplacian_u`, `dtn_symbol`,
      `tendsto_u_atTop`. Not proved: uniqueness of the bounded extension, the L² Fourier-multiplier statement.
      Ticked 2026-11-22 by an interactive session: STATUS PASS 1121/1121 at bbcf097 (CI run 45052545358), all of
      this file's theorems verified (standard axioms only).
- [ ] F3.1 K_{iν}(r) = ∫₀^∞ e^{−r cosh t} cos(νt) dt: integrand integrable for r > 0, value real, |K_{iν}(r)| ≤ K_0(r) — file SteklovAudit/Foundations/KIntegral.lean
- [ ] F3.2 K_{iν}(r) even in ν and continuous in r on (0, ∞) — file SteklovAudit/Foundations/KContinuity.lean
- [ ] F3.3 K_{iν} satisfies the modified Bessel ODE r²K'' + rK' − (r² − ν²)K = 0 — file SteklovAudit/Foundations/KBesselODE.lean
- [ ] F4.1 finite-dimensional spectral shift: for symmetric matrices, ξ(λ) = N_B(λ) − N_A(λ) and Tr(f(B) − f(A)) = −∫ f' ξ for C¹ f (sign corrected 2026-11-22: for A = 0, B = 1, f(x) = x the trace difference is 1 and ∫ f' ξ = −1; equivalently use ξ = N_A − N_B without the minus) — file SteklovAudit/Foundations/SpectralShiftFin.lean
- [ ] F5.1 virial theorem for matrices: ⟨v, [H, A] v⟩ = 0 for an eigenvector v of a symmetric H — file SteklovAudit/Foundations/VirialMatrix.lean
- [ ] F5.2 finite-dimensional Mourre-type bound: if 1_I(H) i[H, A] 1_I(H) ≥ c·1_I(H), c > 0, then no eigenvalue of H lies in I — file SteklovAudit/Foundations/MourreFin.lean
- [ ] F5.3 d'Alembert's formula for the 1D wave equation and finite speed of propagation — file SteklovAudit/Foundations/DAlembert.lean

## Not attempted here

Constructing the Dirichlet-to-Neumann operator, Sobolev traces on Lipschitz domains, and the
PDE estimates (2.2), (5.5), (7.1), (7.15), propagation (9.1). These stay named hypotheses.
