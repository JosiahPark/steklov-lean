import Mathlib
import SteklovAudit.RieszMeans

/-!
# Section 8: positive Riesz asymptotics do not determine the sharp second coefficient

The end of Section 8 gives an example: for `A > 0`, `B` and `0 < ε < 2A`, the count
`N(L) = ⌊A L² + B L + ε L sin L⌋` (adjusted on a bounded interval) is monotone, satisfies every positive
Riesz law with coefficients `A, B`, but "its order-L counting remainder does not converge". This module
proves those three claims:

* `Fc_monotoneOn`, `Nc_monotone`: `F(L) = A L² + B L + ε L sin L` has `F' > 0` beyond the explicit
  threshold `L0c`, and `N(L) = ⌊F(max(L, L0c))⌋` is monotone on all of ℝ;
* `osc_riesz_bound`: `|∫₀^L (L−u)^(r−1) u sin u du| ≤ 2L + L^r + L/r` (`L ≥ 1`, `r > 0`), by integration
  by parts on `[0, L−1]` and a direct bound on `[L−1, L]`;
* `Nc_riesz`: for every `r > 0`,
  `r ∫₀^L (L−u)^(r−1) N(u) du = 2A L^(r+2)/((r+1)(r+2)) + B L^(r+1)/(r+1) + o(L^(r+1))`;
* `Nc_not_sharp`: for every `B'`, `N` is not `A L² + B' L + o(L)`;
* `riesz_does_not_imply_sharp`: hence, unlike `RieszMeans.riesz_of_sharp` (sharp ⇒ Riesz), the converse fails.

What this module does NOT prove: the heat expansion (8.1) for this example, or Lemma 8.1.
-/

namespace SteklovAudit.RieszCounterexample

open SteklovAudit SteklovAudit.RieszMeans MeasureTheory
/-- `φ(u) = sin u − u cos u`, an antiderivative of `u sin u`. -/
noncomputable def phiS (u : ℝ) : ℝ := Real.sin u - u * Real.cos u

theorem hasDerivAt_phiS (u : ℝ) : HasDerivAt phiS (u * Real.sin u) u := by
  have h := (Real.hasDerivAt_sin u).sub ((hasDerivAt_id' u).mul (Real.hasDerivAt_cos u))
  exact h.congr_deriv (by ring)

theorem abs_phiS_le (u : ℝ) (hu : 0 ≤ u) : |phiS u| ≤ 1 + u := by
  unfold phiS
  have h1 := Real.abs_sin_le_one u
  have h2 := Real.abs_cos_le_one u
  calc |Real.sin u - u * Real.cos u| ≤ |Real.sin u| + |u * Real.cos u| := abs_sub _ _
    _ ≤ 1 + u := by
      rw [abs_mul, abs_of_nonneg hu]
      nlinarith [abs_nonneg (Real.cos u)]

/-- The oscillatory Riesz integral: for `r > 0`, `L ≥ 1`,
`|∫₀^L (L−u)^(r−1) u sin u du| ≤ 2L + L^r + L/r`. -/
theorem osc_riesz_bound (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L) :
    |∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (u * Real.sin u)| ≤ 2 * L + L ^ r + L / r := by
  have hL0 : 0 ≤ L := by linarith
  have hk := kernel_ii r L hr
  have iAll : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (u * Real.sin u))
      MeasureTheory.volume 0 L :=
    hk.mul_continuousOn (by fun_prop : Continuous fun u : ℝ => u * Real.sin u).continuousOn
  have i1 : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (u * Real.sin u)) MeasureTheory.volume 0 (L - 1) :=
    iAll.mono_set (by rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hL0]
                      exact Set.Icc_subset_Icc le_rfl (by linarith))
  have i2 : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (u * Real.sin u)) MeasureTheory.volume (L - 1) L :=
    iAll.mono_set (by rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hL0]
                      exact Set.Icc_subset_Icc (by linarith) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  -- second piece
  have hI2 : |∫ u in (L - 1)..L, (L - u) ^ (r - 1) * (u * Real.sin u)| ≤ L / r := by
    have hk2 : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1)) MeasureTheory.volume (L - 1) L :=
      hk.mono_set (by rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hL0]
                      exact Set.Icc_subset_Icc (by linarith) le_rfl)
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs (by linarith)) ?_
    have hm : ∫ u in (L - 1)..L, |(L - u) ^ (r - 1) * (u * Real.sin u)| ≤
        ∫ u in (L - 1)..L, L * (L - u) ^ (r - 1) := by
      refine intervalIntegral.integral_mono_on (by linarith) i2.abs (hk2.const_mul L) ?_
      intro u hu
      have hk0 : 0 ≤ (L - u) ^ (r - 1) := Real.rpow_nonneg (by linarith [hu.2]) _
      rw [abs_mul, abs_of_nonneg hk0, abs_mul, abs_of_nonneg (by linarith [hu.1] : (0:ℝ) ≤ u)]
      have : u * |Real.sin u| ≤ L := by
        have := Real.abs_sin_le_one u
        nlinarith [abs_nonneg (Real.sin u), hu.2]
      nlinarith
    refine le_trans hm (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun t => t ^ (r - 1)) L, sub_self,
      show L - (L - 1) = 1 by ring, int_rpow (r - 1) 1 (by linarith) zero_le_one, sub_add_cancel,
      Real.one_rpow]
    ring
  -- first piece: integration by parts
  have hkd : ∀ x ∈ Set.uIcc (0:ℝ) (L - 1), HasDerivAt (fun u => (L - u) ^ (r - 1))
      (-1 * (r - 1) * (L - x) ^ (r - 1 - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact ((hasDerivAt_id' x).const_sub L).rpow_const (Or.inl (by linarith [hx.2]))
  have hkc : ContinuousOn (fun x => -1 * (r - 1) * (L - x) ^ (r - 1 - 1)) (Set.uIcc 0 (L - 1)) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact (continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).rpow_const
      (Or.inl (by intro h; simp only [Pi.sub_apply, id] at h; linarith [hx.2])))).continuousWithinAt
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hkd (fun x _ => hasDerivAt_phiS x)
    hkc.intervalIntegrable ((by fun_prop : Continuous fun u : ℝ => u * Real.sin u).intervalIntegrable _ _)
  rw [ibp]
  have hb1 : (L - (L - 1)) ^ (r - 1) * phiS (L - 1) = phiS (L - 1) := by
    rw [show L - (L - 1) = 1 by ring, Real.one_rpow, one_mul]
  have hb0 : (L - 0) ^ (r - 1) * phiS 0 = 0 := by simp [phiS]
  rw [hb1, hb0, sub_zero]
  have hphi : |phiS (L - 1)| ≤ L := by
    have := abs_phiS_le (L - 1) (by linarith); linarith
  -- the derivative term
  have hD : |∫ x in (0:ℝ)..(L - 1), -1 * (r - 1) * (L - x) ^ (r - 1 - 1) * phiS x| ≤ L + L ^ r := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hkd hkc.intervalIntegrable
    rw [show L - (L - 1) = 1 by ring, Real.one_rpow, sub_zero] at hFTC
    have hLr : L * L ^ (r - 1) = L ^ r := by
      rw [← Real.rpow_one_add' hL0 (by linarith)]; ring_nf
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs (by linarith)) ?_
    have hm : ∫ x in (0:ℝ)..(L - 1), |-1 * (r - 1) * (L - x) ^ (r - 1 - 1) * phiS x| ≤
        ∫ x in (0:ℝ)..(L - 1), L * |-1 * (r - 1) * (L - x) ^ (r - 1 - 1)| := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
      · have hphic : Continuous phiS := by unfold phiS; fun_prop
        exact (hkc.mul hphic.continuousOn).intervalIntegrable.abs
      · exact (hkc.intervalIntegrable.abs).const_mul L
      · intro x hx
        rw [abs_mul, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have := abs_phiS_le x hx.1; linarith [hx.2]
    refine le_trans hm ?_
    rw [intervalIntegral.integral_const_mul]
    have hsign : ∫ x in (0:ℝ)..(L - 1), |-1 * (r - 1) * (L - x) ^ (r - 1 - 1)| =
        |∫ x in (0:ℝ)..(L - 1), -1 * (r - 1) * (L - x) ^ (r - 1 - 1)| := by
      rcases le_total r 1 with h | h
      · rw [abs_of_nonneg (intervalIntegral.integral_nonneg (by linarith) fun x hx => ?_)]
        · refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Set.uIcc_of_le (by linarith)] at hx
          exact abs_of_nonneg (mul_nonneg (by nlinarith) (Real.rpow_nonneg (by linarith [hx.2]) _))
        · exact mul_nonneg (by nlinarith) (Real.rpow_nonneg (by linarith [hx.2]) _)
      · have e : ∫ x in (0:ℝ)..(L - 1), |-1 * (r - 1) * (L - x) ^ (r - 1 - 1)| =
            ∫ x in (0:ℝ)..(L - 1), -(-1 * (r - 1) * (L - x) ^ (r - 1 - 1)) := by
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Set.uIcc_of_le (by linarith)] at hx
          exact abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by nlinarith)
            (Real.rpow_nonneg (by linarith [hx.2]) _))
        have n : 0 ≤ ∫ x in (0:ℝ)..(L - 1), -(-1 * (r - 1) * (L - x) ^ (r - 1 - 1)) :=
          intervalIntegral.integral_nonneg (by linarith) fun x hx =>
            neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (by nlinarith)
              (Real.rpow_nonneg (by linarith [hx.2]) _))
        rw [e, intervalIntegral.integral_neg] at *
        rw [abs_of_nonpos (by linarith)]
    rw [hsign, hFTC]
    have hpos : 0 ≤ L ^ (r - 1) := Real.rpow_nonneg hL0 _
    simp only [sub_zero] at *
    have : |1 - L ^ (r - 1)| ≤ 1 + L ^ (r - 1) := by
      rw [abs_le]; constructor <;> linarith
    nlinarith
  have := abs_add_le (phiS (L - 1) - ∫ x in (0:ℝ)..(L - 1), -1 * (r - 1) * (L - x) ^ (r - 1 - 1) * phiS x)
    (∫ u in (L - 1)..L, (L - u) ^ (r - 1) * (u * Real.sin u))
  have := abs_sub (phiS (L - 1)) (∫ x in (0:ℝ)..(L - 1), -1 * (r - 1) * (L - x) ^ (r - 1 - 1) * phiS x)
  linarith


/-! ### The counterexample at the end of Section 8 -/

/-- `F(L) = A L² + B L + ε L sin L`. -/
noncomputable def Fc (A B ε L : ℝ) : ℝ := A * L ^ 2 + B * L + ε * L * Real.sin L

/-- Threshold beyond which `F' > 0` (for `0 < ε < 2A`). -/
noncomputable def L0c (A B ε : ℝ) : ℝ := max 1 ((|B| + ε + 1) / (2 * A - ε))

theorem hasDerivAt_Fc (A B ε L : ℝ) :
    HasDerivAt (Fc A B ε) (2 * A * L + B + ε * Real.sin L + ε * L * Real.cos L) L := by
  have h := ((((hasDerivAt_id' L).pow 2).const_mul A).add ((hasDerivAt_id' L).const_mul B)).add
    (((hasDerivAt_id' L).const_mul ε).mul (Real.hasDerivAt_sin L))
  refine h.congr_deriv ?_
  simp; ring

theorem deriv_Fc_pos (A B ε L : ℝ) (hε : 0 < ε) (hεA : ε < 2 * A) (hL : L0c A B ε ≤ L) :
    0 < 2 * A * L + B + ε * Real.sin L + ε * L * Real.cos L := by
  have h1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have h2 : (|B| + ε + 1) / (2 * A - ε) ≤ L := le_trans (le_max_right _ _) hL
  have hpos : 0 < 2 * A - ε := by linarith
  rw [div_le_iff₀ hpos] at h2
  have s1 := Real.neg_one_le_sin L
  have c1 := Real.neg_one_le_cos L
  have hb := neg_abs_le B
  have hεL : 0 ≤ ε * L := by positivity
  have c2 := mul_le_mul_of_nonneg_left c1 hεL
  have s2 := mul_le_mul_of_nonneg_left s1 hε.le
  nlinarith

theorem Fc_monotoneOn (A B ε : ℝ) (hε : 0 < ε) (hεA : ε < 2 * A) :
    MonotoneOn (Fc A B ε) (Set.Ici (L0c A B ε)) := by
  refine (strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_).monotoneOn
  · exact fun x _ => (hasDerivAt_Fc A B ε x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_Fc A B ε x).deriv]
    exact deriv_Fc_pos A B ε x hε hεA (le_of_lt hx)

/-- The counting model `N(L) = ⌊F(max(L, L₀))⌋`: `⌊A L² + B L + ε L sin L⌋` for `L ≥ L₀`,
adjusted on the bounded interval `[0, L₀)` to keep it monotone. -/
noncomputable def Nc (A B ε : ℝ) (L : ℝ) : ℝ := (⌊Fc A B ε (max L (L0c A B ε))⌋ : ℝ)

theorem Nc_monotone (A B ε : ℝ) (hε : 0 < ε) (hεA : ε < 2 * A) : Monotone (Nc A B ε) := by
  intro x y hxy
  unfold Nc
  exact_mod_cast Int.floor_mono (Fc_monotoneOn A B ε hε hεA (Set.mem_Ici.mpr (le_max_right _ _))
    (Set.mem_Ici.mpr (le_max_right _ _)) (max_le_max hxy le_rfl))

theorem Nc_eq (A B ε L : ℝ) (hL : L0c A B ε ≤ L) : Nc A B ε L = (⌊Fc A B ε L⌋ : ℝ) := by
  simp [Nc, max_eq_left hL]

/-- The count has no sharp two-term law with leading coefficient `A`, for any `B'`: the order-`L`
remainder `ε L sin L` does not converge. -/
theorem Nc_not_sharp (A B ε : ℝ) (hε : 0 < ε) (B' : ℝ) :
    ¬ HasSharpRealLaw (Nc A B ε) A B' := by
  intro hlaw
  obtain ⟨L1, _, h1⟩ := hlaw (ε / 4) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_gt (L1 + L0c A B ε + 4 / ε + 1)
  have hpi := Real.pi_pos
  have h2pi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_d2]
  have L0_1 : 1 ≤ L0c A B ε := le_max_left _ _
  set La := Real.pi / 2 + n * (2 * Real.pi) with hLa
  set Lb := Real.pi / 2 + Real.pi + n * (2 * Real.pi) with hLb
  have hna : (n : ℝ) ≤ n * (2 * Real.pi) := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hLa1 : L1 + L0c A B ε + 4 / ε + 1 < La := by linarith
  have hLb1 : L1 + L0c A B ε + 4 / ε + 1 < Lb := by linarith
  have hsa : Real.sin La = 1 := by rw [hLa, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have hsb : Real.sin Lb = -1 := by
    rw [hLb, Real.sin_add_nat_mul_two_pi, Real.sin_add_pi, Real.sin_pi_div_two]
  have pos4 : 0 < 4 / ε := by positivity
  have key : ∀ L, L1 + L0c A B ε + 4 / ε + 1 < L →
      |(B - B') * L + ε * L * Real.sin L| ≤ ε / 4 * L + 1 := by
    intro L hL
    have hl := h1 L (by linarith)
    rw [Nc_eq A B ε L (by linarith)] at hl
    have f1 := Int.floor_le (Fc A B ε L)
    have f2 := Int.lt_floor_add_one (Fc A B ε L)
    have hF : Fc A B ε L = A * L ^ 2 + B * L + ε * L * Real.sin L := rfl
    unfold realWeylPolynomial at hl
    rw [abs_le] at hl ⊢
    constructor <;> linarith [hl.1, hl.2]
  have ka := key La hLa1
  have kb := key Lb hLb1
  rw [hsa, mul_one] at ka
  rw [hsb] at kb
  rw [abs_le] at ka kb
  have hLa0 : 4 / ε < La := by linarith
  have : ε * La > 4 := by
    have := mul_lt_mul_of_pos_left hLa0 hε
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have : ε * Lb > 4 := by
    have hLb0 : 4 / ε < Lb := by linarith
    have := mul_lt_mul_of_pos_left hLb0 hε
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have hab : Lb = La + Real.pi := by rw [hLa, hLb]; ring
  nlinarith [ka.1, ka.2, kb.1, kb.2]


/-- The count obeys every positive Riesz law (1.9)-type expansion with coefficients `A, B`:
for every `r > 0`, `R_r(L) = 2A L^(r+2)/((r+1)(r+2)) + B L^(r+1)/(r+1) + o(L^(r+1))`. -/
theorem Nc_riesz (A B ε r : ℝ) (hε : 0 < ε) (hεA : ε < 2 * A) (hr : 0 < r) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      |rieszMean r (Nc A B ε) L - (2 * A / ((r + 1) * (r + 2)) * L ^ (r + 2) + B / (r + 1) * L ^ (r + 1))|
        ≤ δ * L ^ (r + 1) := by
  intro δ hδ
  set L0 := L0c A B ε with hL0def
  have L01 : 1 ≤ L0 := le_max_left _ _
  set N := Nc A B ε with hN
  have hNm : Monotone N := Nc_monotone A B ε hε hεA
  set D := |Fc A B ε L0| + 2 + |A| * L0 ^ 2 + |B| * L0 + ε * L0 with hD
  have hD0 : 0 ≤ D := by positivity
  -- the bounded remainder
  have hd : ∀ u, 0 ≤ u → |N u - (A * u ^ 2 + B * u + ε * (u * Real.sin u))| ≤ D := by
    intro u hu
    have hF : Fc A B ε u = A * u ^ 2 + B * u + ε * (u * Real.sin u) := by unfold Fc; ring
    rcases le_or_gt L0 u with h | h
    · rw [hN, Nc_eq A B ε u h, ← hF]
      have f1 := Int.floor_le (Fc A B ε u)
      have f2 := Int.lt_floor_add_one (Fc A B ε u)
      rw [abs_le]; constructor <;> nlinarith [abs_nonneg (Fc A B ε L0), abs_nonneg A, abs_nonneg B]
    · have hNu : N u = (⌊Fc A B ε L0⌋ : ℝ) := by
        rw [hN]; unfold Nc; rw [max_eq_right h.le]
      have f1 := Int.floor_le (Fc A B ε L0)
      have f2 := Int.lt_floor_add_one (Fc A B ε L0)
      have hFu : |A * u ^ 2 + B * u + ε * (u * Real.sin u)| ≤ |A| * L0 ^ 2 + |B| * L0 + ε * L0 := by
        have hs := Real.abs_sin_le_one u
        calc |A * u ^ 2 + B * u + ε * (u * Real.sin u)|
            ≤ |A * u ^ 2| + |B * u| + |ε * (u * Real.sin u)| := by
              have := abs_add_le (A * u ^ 2) (B * u)
              have := abs_add_le (A * u ^ 2 + B * u) (ε * (u * Real.sin u))
              linarith
          _ = |A| * u ^ 2 + |B| * u + ε * (u * |Real.sin u|) := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg u), abs_of_nonneg hu,
                abs_of_pos hε]
          _ ≤ |A| * L0 ^ 2 + |B| * L0 + ε * L0 := by
              have hu2 : u ^ 2 ≤ L0 ^ 2 := by nlinarith
              have h3 : u * |Real.sin u| ≤ L0 := by nlinarith [abs_nonneg (Real.sin u)]
              have := mul_le_mul_of_nonneg_left hu2 (abs_nonneg A)
              have := mul_le_mul_of_nonneg_left h.le (abs_nonneg B)
              have := mul_le_mul_of_nonneg_left h3 hε.le
              linarith
      have hFL := le_abs_self (Fc A B ε L0)
      have hFL' := neg_abs_le (Fc A B ε L0)
      rw [hNu]
      have := abs_sub (⌊Fc A B ε L0⌋ : ℝ) (A * u ^ 2 + B * u + ε * (u * Real.sin u))
      have : |(⌊Fc A B ε L0⌋ : ℝ)| ≤ |Fc A B ε L0| + 1 := by
        rw [abs_le]; constructor <;> linarith
      linarith
  -- constants
  set K1 := ε * (2 * r + 1) with hK1
  set K2 := r * ε + D with hK2
  have hK1p : 0 < K1 := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  refine ⟨max 1 (max (2 * K2 / δ) ((2 * K1 / δ) ^ r⁻¹)), fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hKL2 : K2 ≤ δ / 2 * L := by
    have := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hL)
    rw [div_le_iff₀ hδ] at this; linarith
  have hKL1 : K1 ≤ δ / 2 * L ^ r := by
    have h := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hL)
    have h' := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h hr.le
    rw [Real.rpow_inv_rpow (by positivity) hr.ne'] at h'
    rw [div_le_iff₀ hδ] at h'; linarith
  have hLr : L ^ (r + 1) = L ^ r * L := by rw [Real.rpow_add hLpos, Real.rpow_one]
  have hLrp : 0 < L ^ r := Real.rpow_pos_of_pos hLpos r
  -- integrability
  have hk := kernel_ii r L hr
  have iN : IntervalIntegrable (fun u => (L - u) ^ (r - 1) * N u) MeasureTheory.volume 0 L :=
    kernel_mul_ii r L hr hL0 N (|N 0| + |N L|) hNm.measurable (fun u hu => by
      have a := hNm hu.1; have b := hNm hu.2
      rw [abs_le]; constructor
      · linarith [neg_abs_le (N 0), abs_nonneg (N L)]
      · linarith [le_abs_self (N L), abs_nonneg (N 0)])
  have i0 : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * u) MeasureTheory.volume 0 L :=
    hk.mul_continuousOn continuous_id.continuousOn
  have i2 : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * u ^ 2) MeasureTheory.volume 0 L :=
    hk.mul_continuousOn (continuous_pow 2).continuousOn
  have iP : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (A * u ^ 2 + B * u))
      MeasureTheory.volume 0 L := hk.mul_continuousOn (by fun_prop)
  have iS : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (u * Real.sin u))
      MeasureTheory.volume 0 L :=
    hk.mul_continuousOn (by fun_prop : Continuous fun u : ℝ => u * Real.sin u).continuousOn
  have iD : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) *
      (N u - (A * u ^ 2 + B * u + ε * (u * Real.sin u)))) MeasureTheory.volume 0 L := by
    refine ((iN.sub iP).sub (iS.const_mul ε)).congr (fun u _ => ?_)
    ring
  have hP : ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (A * u ^ 2 + B * u) =
      A * (2 * L ^ (r + 2) / (r * (r + 1) * (r + 2))) + B * (L ^ (r + 1) / (r * (r + 1))) := by
    have e : (fun u : ℝ => (L - u) ^ (r - 1) * (A * u ^ 2 + B * u)) =
        fun u => A * ((L - u) ^ (r - 1) * u ^ 2) + B * ((L - u) ^ (r - 1) * u) := by
      funext u; ring
    rw [e, intervalIntegral.integral_add (i2.const_mul A) (i0.const_mul B),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      kernel_moment2 r L hr hL0, kernel_moment1 r L hr hL0]
  have hsplit : ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * N u =
      (∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (A * u ^ 2 + B * u)) +
        ε * (∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (u * Real.sin u)) +
        ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u + ε * (u * Real.sin u))) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add iP (iS.const_mul ε),
      ← intervalIntegral.integral_add (iP.add (iS.const_mul ε)) iD]
    congr 1; funext u; ring
  have hbD : |∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u + ε * (u * Real.sin u)))|
      ≤ D * (L ^ r / r) := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hL0) ?_
    have hm : ∫ u in (0:ℝ)..L, |(L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u + ε * (u * Real.sin u)))|
        ≤ ∫ u in (0:ℝ)..L, D * (L - u) ^ (r - 1) := by
      refine intervalIntegral.integral_mono_on hL0 iD.abs (hk.const_mul D) ?_
      intro u hu
      have hk0 : 0 ≤ (L - u) ^ (r - 1) := Real.rpow_nonneg (by linarith [hu.2]) _
      rw [abs_mul, abs_of_nonneg hk0, mul_comm D]
      exact mul_le_mul_of_nonneg_left (hd u hu.1) hk0
    refine le_trans hm (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, kernel_moment0 r L hr hL0]
  have hbS := osc_riesz_bound r L hr hL1
  unfold rieszMean
  rw [hsplit, hP]
  set IS := ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (u * Real.sin u)
  set ID := ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u + ε * (u * Real.sin u)))
  have key : r * (A * (2 * L ^ (r + 2) / (r * (r + 1) * (r + 2))) + B * (L ^ (r + 1) / (r * (r + 1))) +
      ε * IS + ID) - (2 * A / ((r + 1) * (r + 2)) * L ^ (r + 2) + B / (r + 1) * L ^ (r + 1)) =
      r * ε * IS + r * ID := by
    field_simp; ring
  rw [key]
  have b1 : |r * ε * IS| ≤ r * ε * (2 * L + L ^ r + L / r) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < r * ε)]
    exact mul_le_mul_of_nonneg_left hbS (by positivity)
  have b2 : |r * ID| ≤ D * L ^ r := by
    rw [abs_mul, abs_of_pos hr]
    calc r * |ID| ≤ r * (D * (L ^ r / r)) := mul_le_mul_of_nonneg_left hbD hr.le
      _ = D * L ^ r := by field_simp
  have e1 : r * ε * (2 * L + L ^ r + L / r) + D * L ^ r = K1 * L + K2 * L ^ r := by
    rw [hK1, hK2]; field_simp; ring
  have t1 : K1 * L ≤ δ / 2 * L ^ (r + 1) := by
    rw [hLr]; nlinarith
  have t2 : K2 * L ^ r ≤ δ / 2 * L ^ (r + 1) := by
    rw [hLr]; nlinarith
  calc |r * ε * IS + r * ID| ≤ |r * ε * IS| + |r * ID| := abs_add_le _ _
    _ ≤ K1 * L + K2 * L ^ r := by linarith
    _ ≤ δ * L ^ (r + 1) := by linarith


/-- Positive Riesz laws for all `r > 0` do not imply the sharp two-term law: the monotone count
`N = Nc 1 0 1` satisfies all of them with coefficients `(1, 0)` and has no sharp law `L² + B'L + o(L)`. -/
theorem riesz_does_not_imply_sharp :
    Monotone (Nc 1 0 1) ∧
    (∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      |rieszMean r (Nc 1 0 1) L - (2 * 1 / ((r + 1) * (r + 2)) * L ^ (r + 2) + 0 / (r + 1) * L ^ (r + 1))|
        ≤ δ * L ^ (r + 1)) ∧
    (∀ B' : ℝ, ¬ HasSharpRealLaw (Nc 1 0 1) 1 B') :=
  ⟨Nc_monotone 1 0 1 one_pos (by norm_num),
    fun r hr => Nc_riesz 1 0 1 r one_pos (by norm_num) hr,
    fun B' => Nc_not_sharp 1 0 1 one_pos B'⟩

end SteklovAudit.RieszCounterexample
