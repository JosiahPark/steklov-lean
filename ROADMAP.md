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
- [ ] G65. `SteklovAudit/H5LowLinearStrict.lean` (imports `SteklovAudit.H5EvLowCountIndep`): the linear low
      count is strictly weaker than the L-uniform `lowCount`. `flatD_linearCount : ∀ M L : ℝ, ((Finset.univ.filter
      fun i => (flatD ⌊L⌋₊).a i ≤ M).card : ℝ) ≤ 1 * (1 + |L|)` (card of a filter ≤ `Fintype.card (Fin ⌊L⌋₊) =
      ⌊L⌋₊`; `Nat.floor_le` for `0 ≤ L`, `Nat.floor_eq_zero`/`Nat.floor_of_nonpos` for `L < 0`; `le_abs_self`),
      and `linearCount_strictly_weaker`: the conjunction of `flatD_linearCount` with G61's `flatD_not_lowCount`.
      F table text: on `flatD` the G64 low row holds with `c = 1` while no L-uniform `c` exists. Theorem
      names: `flatD_linearCount`, `linearCount_strictly_weaker`.
      Written by the formalize task 2026-11-16 in `SteklovAudit/H5LowLinearStrict.lean` (uncompiled at push,
      commit 1cee561): theorems `floor_le_one_add_abs`, `flatD_filter_card_le`, `flatD_linearCount`,
      `flatD_linearCount_exists`, `linearCount_strictly_weaker`. Next run: tick if STATUS shows it compiled.

## Foundations (long-term)

Analytic machinery that Mathlib lacks and that the main theorem needs: (G1) Sobolev traces, (G2) Dirichlet-to-Neumann /
Steklov operators, (G3) Kontorovich–Lebedev transform and K_{iν}, (G4) Krein spectral shift, (G5) Mourre estimates and
propagation. Worked by a separate hourly foundations task, one item per run, independent of sections A–G (the item IDs
F1.1–F5.3 are not the section F items F1–F3). Each item is a new file `SteklovAudit/Foundations/<Name>.lean` importing
Mathlib, whose docstring states exactly what is proved and what is not. These are toy, one-dimensional or
finite-dimensional models, not the paper's operator: none of them proves the main theorem or any of `[H1]`–`[H6]`.

- [ ] F1.1 1D trace inequality: |f(0)|² ≤ 2∫₀¹(|f|²+|f'|²) for f ∈ C¹[0,1] — file SteklovAudit/Foundations/Trace1D.lean
- [ ] F1.2 half-line trace with constant 1: |f(0)|² ≤ ∫₀^∞(|f|²+|f'|²) for suitable decaying f — file SteklovAudit/Foundations/TraceHalfLine.lean
- [ ] F2.1 disk Steklov eigenfunctions: r^n cos(nθ), r^n sin(nθ) are harmonic, with normal derivative n·value on the unit circle — file SteklovAudit/Foundations/DiskSteklov.lean
- [ ] F2.2 half-plane DtN symbol: e^{ikx−|k|y} is harmonic and −∂_y equals |k|·value at y = 0 — file SteklovAudit/Foundations/HalfPlaneDtN.lean
- [ ] F3.1 K_{iν}(r) = ∫₀^∞ e^{−r cosh t} cos(νt) dt: integrand integrable for r > 0, value real, |K_{iν}(r)| ≤ K_0(r) — file SteklovAudit/Foundations/KIntegral.lean
- [ ] F3.2 K_{iν}(r) even in ν and continuous in r on (0, ∞) — file SteklovAudit/Foundations/KContinuity.lean
- [ ] F3.3 K_{iν} satisfies the modified Bessel ODE r²K'' + rK' − (r² − ν²)K = 0 — file SteklovAudit/Foundations/KBesselODE.lean
- [ ] F4.1 finite-dimensional spectral shift: for symmetric matrices, ξ(λ) = N_B(λ) − N_A(λ) and Tr(f(B) − f(A)) = ∫ f' ξ for C¹ f — file SteklovAudit/Foundations/SpectralShiftFin.lean
- [ ] F5.1 virial theorem for matrices: ⟨v, [H, A] v⟩ = 0 for an eigenvector v of a symmetric H — file SteklovAudit/Foundations/VirialMatrix.lean
- [ ] F5.2 finite-dimensional Mourre-type bound: if 1_I(H) i[H, A] 1_I(H) ≥ c·1_I(H), c > 0, then no eigenvalue of H lies in I — file SteklovAudit/Foundations/MourreFin.lean
- [ ] F5.3 d'Alembert's formula for the 1D wave equation and finite speed of propagation — file SteklovAudit/Foundations/DAlembert.lean

## Not attempted here

Constructing the Dirichlet-to-Neumann operator, Sobolev traces on Lipschitz domains, and the
PDE estimates (2.2), (5.5), (7.1), (7.15), propagation (9.1). These stay named hypotheses.
