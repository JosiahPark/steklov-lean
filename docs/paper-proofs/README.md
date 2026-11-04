# Paper proofs from the hourly runs

The hourly Steklov runs (continuations 01–43, archive `Steklov_All_Continuations_02-43_Combined.zip`) proved
many results on paper in their reports, and most of these were never put into Lean. This folder is the
complete record of them.

- [`runs-01-24.md`](runs-01-24.md): 33 results from runs 01–24.
- [`runs-25-43.md`](runs-25-43.md): 24 results from runs 25–43 (no reports exist for runs 28 and 31).
- The original run reports are in the archive (`HOURLY_RUN_NN_REPORT.md` inside each run's zip; runs 04–06
  also cite four Section 7 companion notes, `SECTION7_*.md`, in the same archives). They are not copied here.

Each entry gives the source run, the manuscript location, a precise statement, the full proof, sharpness
examples, the numeric checks the run reported (examples, not proofs), its Lean status, and caveats. Where the
extraction completed a routine step that the report skipped, the added text is marked "(filled in)". Each
file ends with a list of claims the reports **asserted without proof**.

## What these results are, and are not

All of them are statements about abstract finite-dimensional operators, model operators on the circle or
torus, or real functions. **None is an estimate for the Dirichlet-to-Neumann operator of the regular
tetrahedron**, and none proves a step of the manuscript for that operator. Their value is in checking the
manuscript's *logic*: which reductions are valid, which need extra hypotheses, and which fail.

## Lean status (57 results)

| Status | Count | Meaning |
|---|---|---|
| Formalized | 20 | A compiled theorem in this repo states essentially this result (often in finite spectral coordinates; differences are noted in the entry) |
| Partly formalized | 2 | Some parts compiled, others not |
| Scalar fragments only | 30 | Only scalar or algebraic pieces are compiled; the result itself is not |
| Not formalized | 5 | Nothing in Lean |

## Findings that bear directly on the manuscript

- **Lemma 7.1 / (7.2).** Runs 22–24 give model examples (a circle multiplier, the flat 2-torus, a fixed-width
  window in 2D) where a uniform, energy-independent Hilbert–Schmidt bound of the localized defect fails or
  grows with the energy. This is why the repo replaces (7.2) by Lemma 7.1′. Run 39 gives the matching lower
  bound: a positive counting excess forces a localized squared defect of order δ²L.
- **From HS bounds to trace bounds.** Runs 17, 27 and 43 show that a Hilbert–Schmidt bound converts to a
  trace bound only at the cost of a factor √rank (or √dim), and that this factor cannot be removed in
  general. Any passage from (7.23)–(7.24) to the trace comparison (7.25)–(7.29) needs rank control,
  cancellation, or a trace-class estimate.
- **Counting transfer needs a spectral shift.** Runs 30–34 prove a one-sided and two-sided counting
  transfer with a shift δ > 0; run 33 shows δ = 0 is impossible even for an exactly unitary
  identification with vanishing defect; run 34 finds the optimal δ ≈ L^(−1/3) for a bounded defect.
- **Unsmoothing.** Run 35 shows that a sharp law for one fixed smoothing width does not give the sharp
  law for the count. Runs 36–41 show that it does if the smoothed law holds with the same coefficients
  for widths shrinking to 0. Caveat found while documenting: the manuscript's smoothing kernel ρ_S in
  (7.18) is a signed Schwartz function, not a nonnegative compactly supported kernel, and Section 11.1
  goes through the window-mass bound (11.1)–(11.2) rather than a Tauberian unsmoothing step, so runs
  36–41 do not apply to the manuscript's route as written.
- **An error in run 35.** The report states ∫ s·sin(2π(L+s)) ds = −cos(2πL)/(2π) over [−1/2, 1/2]; the
  correct value is +cos(2πL)/(2π). The conclusion is unaffected (the term is O(1)), and the run's checks
  could not catch it because every test point had cos(2πL) = 0.
- **Duplicate charts (run 14).** A perfect frame with zero defect still does not give a sharp count when
  charts overlap; run 15 gives the weighted trace localization that avoids the duplicate-chart factor.

## Index

| ID | Result | Manuscript location | Lean status |
|---|---|---|---|
| [R01.1](runs-01-24.md#r011--three-region-remainder-bookkeeping) | Three-region remainder bookkeeping | §11.2, the proof of Theorem 11.1 (vertex/edge/face assembly, (11.5)). | Formalized |
| [R02.1](runs-01-24.md#r021--squared-partition-trace-identity-for-a-finite-rank-spectral-projector) | Squared-partition trace identity for a finite-rank spectral projector | §11.2 (squared spatial partition in the proof of Theorem 11.1); ledger item H1 "trace … | Formalized |
| [R03.1](runs-01-24.md#r031--noncommutative-discrete-duhamel-identity-and-contraction-bound) | Noncommutative discrete Duhamel identity and contraction bound | §7.4, (7.24) (the "bounded-quasicommutator Duhamel" step). | Formalized |
| [R03.2](runs-01-24.md#r032--bounded-hs-families-need-not-have-uniform-spectral-tails-moving-rank-one-example) | Bounded HS families need not have uniform spectral tails (moving rank-one example) | §7.4, (7.23)–(7.29), and the sentence after (7.29) about normalized annuli; also §7.8. | Scalar fragments only |
| [R04.1](runs-01-24.md#r041--truncated-exponential-taylor-duhamel-identity-and-hs-estimate) | Truncated-exponential (Taylor) Duhamel identity and HS estimate | §7.4, (7.24). | Formalized |
| [R04.2](runs-01-24.md#r042--a-fixed-hs-operator-has-vanishing-spectral-tail-the-decay-is-uniform-over-hs-precompact-families) | A fixed HS operator has vanishing spectral tail; the decay is uniform over HS-precompact families | §7.4, (7.23): "Since ψ(hB) → 0 strongly and F ∈ S₂, finite-rank approximation gives … | Scalar fragments only |
| [R04.3](runs-01-24.md#r043--finite-relative-spectral-primitive-n_a--n_b-μ²-dμ--σ-1a_j--σ-1b_k) | Finite relative spectral primitive: ∫(N_A − N_B) μ⁻² dμ = Σ 1/a_j − Σ 1/b_k | §7.7, (7.38)–(7.45) (relative wedge primitive and negative-energy normalization). | Scalar fragments only |
| [R04.4](runs-01-24.md#r044--continuous-time-hilbertschmidt-duhamel-lemma-for-unbounded-self-adjoint-generators-with-a-localized-corollary) | Continuous-time Hilbert–Schmidt Duhamel lemma for unbounded self-adjoint generators, with a localized corollary | §7.4, (7.23)–(7.24). | Not formalized |
| [R05.1](runs-01-24.md#r051--noncommutative-off-band-neumann-series-for-746-with-uniform-bounds-on-normalized-annuli) | Noncommutative off-band Neumann series for (7.46), with uniform bounds on normalized annuli | §7.8, (7.46), and the equation (5.10) it solves. | Scalar fragments only |
| [R05.2](runs-01-24.md#r052--dyadic-exterior-primitive-summability-l¹-bound-and-riemannlebesgue-decay) | Dyadic exterior primitive: summability, L¹ bound and Riemann–Lebesgue decay | §7.7, (7.42)–(7.43). | Scalar fragments only |
| [R05.3](runs-01-24.md#r053--sharp-real-axis-law-implies-ol-multiplicities-so-strict-and-nonstrict-counts-agree-to-ol) | Sharp real-axis law implies o(L) multiplicities, so strict and nonstrict counts agree to o(L) | end of §11.2, the paragraph after the proof of Theorem 11.1. The manuscript gives … | Scalar fragments only |
| [R07.1](runs-01-24.md#r071--finite-spectral-markov-inequality-moment-bound-implies-tail-bound) | Finite spectral Markov inequality (moment bound implies tail bound) | §7.4, (7.23)/(7.29) (uniform spectral tails of HS defects). | Formalized |
| [R08.1](runs-01-24.md#r081--spectral-gap-hilbertschmidt-estimate-for-the-off-band-block) | Spectral-gap Hilbert–Schmidt estimate for the off-band block | §7.8 (off-band block X = EJ(1−Q)) and the off-band step of Lemma 5.1. | Formalized |
| [R09.1](runs-01-24.md#r091--spectral-sylvester-identity-k_ij--a_i--b_j-j_ij-and-the-squared-gap-sum) | Spectral Sylvester identity K_ij = (a_i − b_j) J_ij and the squared gap sum | §7.8, Lemma 5.1 (off-band block). | Scalar fragments only |
| [R10.1](runs-01-24.md#r101--window-counting-from-a-lower-frame-bound-plus-a-spectral-gap-defect) | Window counting from a lower frame bound plus a spectral-gap defect | §7.8 ("The band calculation is unchanged") and the band/off-band counting in Lemma 5.1. | Scalar fragments only |
| [R11.1](runs-01-24.md#r111--near-isometry-version-of-the-window-count) | Near-isometry version of the window count | §7.8 and Lemma 5.1 (as R10.1). | Scalar fragments only |
| [R12.1](runs-01-24.md#r121--integer-rank-loss-bound-c-d²-n--m--k-e²_hs) | Integer rank-loss bound: c d² (n − m)₊ ≤ ‖K E‖²_HS | §7.8 and Lemma 5.1 (counting transfer). | Scalar fragments only |
| [R13.1](runs-01-24.md#r131--joint-localization-multi-chart-rank-loss-bound) | Joint-localization (multi-chart) rank-loss bound | §7.8 and §11.2 (squared partitions), via Lemma 5.1. | Scalar fragments only |
| [R14.1](runs-01-24.md#r141--duplicate-chart-counterexample-a-perfect-frame-and-zero-defect-do-not-give-a-sharp-count) | Duplicate-chart counterexample: a perfect frame and zero defect do not give a sharp count | §7.7–7.8 and §11.2 (summing local wedge counts over a partition). | Scalar fragments only |
| [R15.1](runs-01-24.md#r151--weighted-polynomial-trace-localization-with-no-duplicate-chart-factor) | Weighted polynomial trace localization, with no duplicate-chart factor | §7.4 (trace comparison (7.25)–(7.29)), §11.2 (partition). | Scalar fragments only |
| [R16.1](runs-01-24.md#r161--resolvent-localization-identity-and-trace-bound) | Resolvent localization identity and trace bound | §7 (localized trace comparison), general. | Scalar fragments only |
| [R16.2](runs-01-24.md#r162--scale-error-budget-geometric-decay-is-summable-a-constant-per-scale-error-is-not) | Scale-error budget: geometric decay is summable, a constant per-scale error is not | §9, (9.1)/(9.12) (multi-scale propagation remainder). | Formalized |
| [R17.1](runs-01-24.md#r171--the-dim-factor-in-hs-to-trace-resolvent-comparison-cannot-be-removed) | The √dim factor in HS-to-trace resolvent comparison cannot be removed | §7 (trace comparison), general. | Scalar fragments only |
| [R18.1](runs-01-24.md#r181--continuous-density-tauberian-obstruction-a-two-term-heat-expansion-does-not-give-a-sharp-two-term-count) | Continuous-density Tauberian obstruction: a two-term heat expansion does not give a sharp two-term count | §11 (unsmoothing); the manuscript itself says it avoids a heat-to-sharp Tauberian … | Scalar fragments only |
| [R19.1](runs-01-24.md#r191--discrete-positive-spectrum-tauberian-obstruction-with-a-three-term-heat-expansion) | Discrete positive-spectrum Tauberian obstruction with a three-term heat expansion | §11 (unsmoothing), general. | Scalar fragments only |
| [R20.1](runs-01-24.md#r201--unit-window-local-mass-bound-implies-a-sharp-versus-smoothed-estimate) | Unit-window local mass bound implies a sharp-versus-smoothed estimate | §11.1, (11.1)–(11.2), and §7.8 ("all normalized local windows satisfy C(VL + 1) … … | Not formalized |
| [R20.2](runs-01-24.md#r202--two-parameter-squeeze-sharp-ol-from-smoothed-estimates-needs-a-second-limit) | Two-parameter squeeze: sharp o(L) from smoothed estimates needs a second limit | §11.1–11.2, Theorem 11.1 (fix the cutoff and ε, let L → ∞, then let γ ↓ 0 and ε ↓ 0). | Formalized |
| [R21.1](runs-01-24.md#r211--bounded-operator-duhamel-identity-with-hs-bound-t-k_hs) | Bounded-operator Duhamel identity with HS bound /t/ ‖K‖_HS | §7.4, (7.24). | Scalar fragments only |
| [R21.2](runs-01-24.md#r212--weighted-trace-error-for-eita-under-a-frame-partition) | Weighted trace error for e^{itA} under a frame partition | §7.4 (wave-trace comparison (7.25)–(7.26)), general. | Not formalized |
| [R22.1](runs-01-24.md#r221--a-smooth-multiplier-whose-commutator-with-d-on-the-circle-is-bounded-but-not-hilbertschmidt) | A smooth multiplier whose commutator with /D/ on the circle is bounded but not Hilbert–Schmidt | Lemma 7.1, (7.2), and its uniform normalized-annulus version used in §7.8. | Scalar fragments only |
| [R22.2](runs-01-24.md#r222--flat-2-torus-quadratic-growth-of-the-truncated-hs-defect-for-δ-and-eix₁) | Flat 2-torus: quadratic growth of the truncated HS defect for √(−Δ) and e^{ix₁} | Lemma 7.1, (7.2) (uniform version), §7.8. | Scalar fragments only |
| [R23.1](runs-01-24.md#r231--spectrally-sandwiched-commutator-on-the-circle-exact-hs-formula-and-a-bound-linear-in-n) | Spectrally sandwiched commutator on the circle: exact HS formula and a bound linear in N | Lemma 7.1, (7.2) (spectrally localized form ‖1_{[0,L]}(A) K‖_{S₂} ≤ C(1 + L)). | Scalar fragments only |
| [R24.1](runs-01-24.md#r241--fixed-width-two-sided-spectral-window-no-energy-uniform-hs-bound-in-dimension-two) | Fixed-width two-sided spectral window: no energy-uniform HS bound in dimension two | Lemma 7.1, (7.2) (uniform localized version), §7.8. | Scalar fragments only |
| [R25.1](runs-25-43.md#r251--spectral-window-gap-leakage-bound-for-the-intertwining-defect) | Spectral-window gap leakage bound for the intertwining defect | Section 9.3. The defect K_h = P_h E_χ − E_χ P_h^C in (9.9) and the propagation … | Formalized |
| [R26.1](runs-25-43.md#r261--exact-resonantnon-resonant-splitting-of-the-identification) | Exact resonant/non-resonant splitting of the identification | Section 9.3, (9.9)–(9.10) (near-resonant propagation). | Scalar fragments only |
| [R26.2](runs-25-43.md#r262--near-resonance-obstruction-the-defect-cannot-control-the-identification-without-a-gap) | Near-resonance obstruction: the defect cannot control the identification without a gap | Section 9 (near-resonant face propagation). | Scalar fragments only |
| [R27.1](runs-25-43.md#r271--tracerank-amplification-an-hs-bound-costs-rank-as-a-trace-bound) | Trace–rank amplification: an HS bound costs √rank as a trace bound | Section 7.4, the passage from HS bounds (7.23)–(7.24) to traces (7.25)–(7.26). The … | Formalized |
| [R27.2](runs-25-43.md#r272--propagator-difference-trace-bound-conditional) | Propagator-difference trace bound (conditional) | Section 7.4: V(t) = e^{−itA}J − Je^{−itB}, (7.24) and (7.25)–(7.26). | Not formalized |
| [R29.1](runs-25-43.md#r291--rank-difference-budget-for-an-approximate-identification) | Rank-difference budget for an approximate identification | Section 7, the identification J = ηR and cumulative counts (7.19)/(7.29). Section 5.3 … | Formalized |
| [R30.1](runs-25-43.md#r301--one-sided-counting-transfer-with-spectral-shift) | One-sided counting transfer with spectral shift | Section 7 (comparison of the counts N_A and N_B through J). Lemma 7.1 / (7.2) for the … | Formalized |
| [R32.1](runs-25-43.md#r321--two-sided-shifted-counting-squeeze) | Two-sided shifted counting squeeze | Section 11 and Proposition 7.3 / (7.19). This is a replacement for the transfer between … | Formalized |
| [R32.2](runs-25-43.md#r322--conditional-sharp-law-transfer-from-the-model-side-only) | Conditional sharp-law transfer from the model side only | Section 11, Theorem 11.1 / (11.4). The wedge-coefficient law (7.45). | Formalized |
| [R33.1](runs-25-43.md#r331--threshold-instability-zero-spectral-shift-is-impossible-even-with-exact-unitarity) | Threshold instability: zero spectral shift is impossible even with exact unitarity | Section 11 (sharp counting). It shows why the transfer of R30.1/R32.1 needs δ > 0. | Formalized |
| [R33.2](runs-25-43.md#r332--admissible-spectral-shift-rates-for-the-squeeze) | Admissible spectral-shift rates for the squeeze | Section 11. | Formalized |
| [R34.1](runs-25-43.md#r341--optimal-spectral-shift-for-the-squeeze-error) | Optimal spectral shift for the squeeze error | Section 11 (error budget of the shifted squeeze R32.1). | Scalar fragments only |
| [R35.1](runs-25-43.md#r351--counterexample-fixed-width-smoothing-does-not-imply-the-sharp-ol-law) | Counterexample: fixed-width smoothing does not imply the sharp o(L) law | Section 11.1, (11.2)–(11.3), and the smoothed counts N^S (7.18). This concerns the … | Partly formalized |
| [R36.1](runs-25-43.md#r361--monotone-sandwich-between-shifted-smoothings) | Monotone sandwich between shifted smoothings | Section 11 (unsmoothing). | Formalized |
| [R36.2](runs-25-43.md#r362--unsmoothing-under-a-uniform-shrinking-scale-estimate-quantitative) | Unsmoothing under a uniform shrinking-scale estimate (quantitative) | Section 11, Theorem 11.1 (the o(L) remainder in (11.4)). | Scalar fragments only |
| [R37.1](runs-25-43.md#r371--tauberian-unsmoothing-from-all-fixed-small-scales-no-uniformity-needed) | Tauberian unsmoothing from all fixed small scales (no uniformity needed) | Section 11, Theorem 11.1. Compare the paper's choice of one fixed time S0 per edge … | Formalized |
| [R38.1](runs-25-43.md#r381--approximate-fixed-scale-tauberian-stability-scale-dependent-errors-and-coefficients) | Approximate fixed-scale Tauberian stability (scale-dependent errors and coefficients) | Section 11, (11.3) (an O(γ) error at each fixed collar width) and Theorem 11.1. | Scalar fragments only |
| [R39.1](runs-25-43.md#r391--spectral-rank-leakage-lower-bound-for-the-localized-defect-with-sharpness) | Spectral-rank leakage lower bound for the localized defect (with sharpness) | Section 7, Lemma 7.1 / (7.2): a lower bound on ‖1_{[0,L]}(A)K‖_S2 forced by any count … | Formalized |
| [R40.1](runs-25-43.md#r401--fixed-scale-tauberian-bracket-for-the-linear-coefficient) | Fixed-scale Tauberian bracket for the linear coefficient | Section 11, (11.3) (a limsup bracket of size C_ε γ) and Theorem 11.1. | Scalar fragments only |
| [R40.2](runs-25-43.md#r402--exact-discrete-obstruction-to-one-scale-unsmoothing) | Exact discrete obstruction to one-scale unsmoothing | Section 11. | Scalar fragments only |
| [R41.1](runs-25-43.md#r411--local-window-spectral-mass-from-smoothed-counts) | Local-window spectral mass from smoothed counts | Section 11.1, (11.1) (a local window spectral mass bound). Compare (2.2). | Scalar fragments only |
| [R42.1](runs-25-43.md#r421--weighted-spectral-leakage-and-its-layer-cake-form) | Weighted spectral leakage and its layer-cake form | Section 7: Lemma 7.1 / (7.2) (‖1_{[0,L]}(A)K‖_S2) and the off-band series (7.46) in … | Partly formalized |
| [R43.1](runs-25-43.md#r431--lipschitz-functional-calculus-transfer-in-hilbertschmidt-norm) | Lipschitz functional-calculus transfer in Hilbert–Schmidt norm | Section 7.2, Lemma 7.2 / (7.6) (the smooth functional calculus bound ‖(ψ(hA)J − … | Formalized |
| [R43.2](runs-25-43.md#r432--hs-smallness-does-not-give-trace-control) | HS smallness does not give trace control | Section 7.4 (passing from (7.24) to the trace comparison (7.26)/(7.29)). | Not formalized |
