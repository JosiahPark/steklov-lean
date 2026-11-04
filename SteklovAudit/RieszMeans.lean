import Mathlib
import SteklovAudit.MainConditional

/-!
# Riesz means from the sharp counting law: formula (1.9) and identity (8.4)

The paper states (1.9): for every fixed `r > 0`,
`Σ_j (L − σ_j)₊^r = √3 a² L^(r+2) / (2π (r+1)(r+2)) + 6 a c_{α₀} L^(r+1) / (r+1) + o(L^(r+1))`,
and in Section 8 writes the Riesz mean as `r ∫₀^L (L − u)^(r−1) N(u) du` (8.4). This module proves:

* `kernel_moment0/1/2`: `∫₀^L (L−u)^(r−1) u^k du` for `k = 0, 1, 2` (exact, `r > 0`);
* `riesz_single`, `riesz_finite`: identity (8.4) for a finite nonnegative spectrum,
  `Σ_j max(L − σ_j, 0)^r = r ∫₀^L (L − u)^(r−1) N(u) du` with `N(u) = #{j : σ_j ≤ u}`;
* `riesz_of_sharp`: if `N` is monotone and `N(L) = A L² + B L + o(L)`, then
  `r ∫₀^L (L−u)^(r−1) N = 2A L^(r+2)/((r+1)(r+2)) + B L^(r+1)/(r+1) + o(L^(r+1))` for every `r > 0`
  (the Abelian direction; no Tauberian step);
* `riesz_of_inputs`: (1.9) with the paper's constants, from the Theorem 11.1 ledger
  (`MainConditional.Thm111Inputs`) and monotonicity of `N`;
* `first_riesz_coefficients_paper`: at `r = 1` the coefficients are `√3 a²/(12π)` and `3 a c`.

The paper derives (1.9) from the heat expansion (1.8) and (7.50) (Section 8); here it is derived from
the sharp law (1.3) instead, which the paper also states implies it ("consequently").

What this module does NOT prove: the heat expansion (1.8), the Tauberian lemma of Section 8, or any
of the hypotheses H1–H6. `riesz_of_inputs` is conditional on the same ledger as Theorem 11.1.
-/

namespace SteklovAudit.RieszMeans

open SteklovAudit SteklovAudit.MainConditional intervalIntegral

/-- `∫₀^L t^(s) dt = L^(s+1)/(s+1)` for `s > -1`, `L ≥ 0`. -/
theorem int_rpow (s L : ℝ) (hs : -1 < s) (hL : 0 ≤ L) :
    ∫ t in (0:ℝ)..L, t ^ s = L ^ (s + 1) / (s + 1) := by
  rw [integral_rpow (Or.inl hs), Real.zero_rpow (by linarith), sub_zero]

theorem kernel_moment0 (r L : ℝ) (hr : 0 < r) (hL : 0 ≤ L) :
    ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) = L ^ r / r := by
  rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ (r - 1)) L, sub_self, sub_zero,
    int_rpow (r - 1) L (by linarith) hL, sub_add_cancel]

theorem kernel_moment1 (r L : ℝ) (hr : 0 < r) (hL : 0 ≤ L) :
    ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * u = L ^ (r + 1) / (r * (r + 1)) := by
  have e : ∀ u, (L - u) ^ (r - 1) * u = (fun t => t ^ (r - 1) * (L - t)) (L - u) := by
    intro u; simp
  simp_rw [e]
  rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ (r - 1) * (L - t)) L, sub_self,
    sub_zero]
  have hpt : Set.EqOn (fun t : ℝ => t ^ (r - 1) * (L - t))
      (fun t => L * t ^ (r - 1) - t ^ r) (Set.uIcc 0 L) := by
    intro t ht
    rw [Set.uIcc_of_le hL] at ht
    rcases ht.1.eq_or_lt with h | h
    · subst h; simp [Real.zero_rpow hr.ne', Real.zero_rpow (show r - 1 + 1 ≠ 0 by linarith)]
      rcases eq_or_ne (r - 1) 0 with h1 | h1
      · simp [h1]
      · simp [Real.zero_rpow h1]
    · have : t ^ r = t ^ (r - 1) * t := by
        rw [← Real.rpow_add_one h.ne', sub_add_cancel]
      simp only [this]; ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, int_rpow (r - 1) L (by linarith) hL,
    int_rpow r L (by linarith) hL, sub_add_cancel]
  · rcases hL.eq_or_lt with h | h
    · subst h; simp [Real.zero_rpow hr.ne', Real.zero_rpow (show r + 1 ≠ 0 by linarith)]
    · rw [Real.rpow_add h, Real.rpow_one]; field_simp; ring
  · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul L
  · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)


theorem kernel_moment2 (r L : ℝ) (hr : 0 < r) (hL : 0 ≤ L) :
    ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * u ^ 2 = 2 * L ^ (r + 2) / (r * (r + 1) * (r + 2)) := by
  have e : ∀ u, (L - u) ^ (r - 1) * u ^ 2 = (fun t => t ^ (r - 1) * (L - t) ^ 2) (L - u) := by
    intro u; simp
  simp_rw [e]
  rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ (r - 1) * (L - t) ^ 2) L, sub_self,
    sub_zero]
  have hpt : Set.EqOn (fun t : ℝ => t ^ (r - 1) * (L - t) ^ 2)
      (fun t => L ^ 2 * t ^ (r - 1) - 2 * L * t ^ r + t ^ (r + 1)) (Set.uIcc 0 L) := by
    intro t ht
    rw [Set.uIcc_of_le hL] at ht
    rcases ht.1.eq_or_lt with h | h
    · subst h
      simp [Real.zero_rpow hr.ne', Real.zero_rpow (show r + 1 ≠ 0 by linarith)]
      rcases eq_or_ne (r - 1) 0 with h1 | h1
      · simp [h1]
      · simp [Real.zero_rpow h1]
    · have h1 : t ^ r = t ^ (r - 1) * t := by
        rw [← Real.rpow_add_one h.ne', sub_add_cancel]
      have h2 : t ^ (r + 1) = t ^ (r - 1) * t * t := by
        rw [← h1, Real.rpow_add_one h.ne']
      simp only [h1, h2]; ring
  have i1 := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := L) (r := r - 1) (by linarith)
  have i2 := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := L) (r := r) (by linarith)
  have i3 := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := L) (r := r + 1) (by linarith)
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add ((i1.const_mul _).sub
      (i2.const_mul _)) i3, intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    int_rpow (r - 1) L (by linarith) hL, int_rpow r L (by linarith) hL,
    int_rpow (r + 1) L (by linarith) hL, sub_add_cancel]
  rcases hL.eq_or_lt with h | h
  · subst h
    simp [Real.zero_rpow hr.ne', Real.zero_rpow (show r + 1 ≠ 0 by linarith),
      Real.zero_rpow (show r + 1 + 1 ≠ 0 by linarith), Real.zero_rpow (show r + 2 ≠ 0 by linarith)]
  · have a1 : L ^ (r + 1) = L ^ r * L := by rw [Real.rpow_add h, Real.rpow_one]
    have a2 : L ^ (r + 1 + 1) = L ^ r * L * L := by rw [Real.rpow_add h, Real.rpow_one, a1]
    have a3 : L ^ (r + 2) = L ^ r * L * L := by rw [show r + 2 = r + 1 + 1 by ring, a2]
    rw [a1, a2, a3]
    field_simp
    ring

/-- Kernel integrability on `[0, L]`. -/
theorem kernel_ii (r L : ℝ) (hr : 0 < r) :
    IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1)) MeasureTheory.volume 0 L := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := L) (b := 0) (r := r - 1)
    (by linarith)).comp_sub_left L
  simpa using h

/-- Riesz mean `r ∫₀^L (L − u)^(r−1) N(u) du`, (8.4). -/
noncomputable def rieszMean (r : ℝ) (N : ℝ → ℝ) (L : ℝ) : ℝ :=
  r * ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * N u

theorem kernel_mul_ii (r L : ℝ) (hr : 0 < r) (hL : 0 ≤ L) (g : ℝ → ℝ) (C : ℝ)
    (hg : Measurable g) (hgb : ∀ u ∈ Set.Icc 0 L, |g u| ≤ C) :
    IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * g u) MeasureTheory.volume 0 L := by
  have hk := kernel_ii r L hr
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL] at hk ⊢
  refine hk.mul_bdd (c := C) hg.aestronglyMeasurable ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
  rw [Real.norm_eq_abs]
  exact hgb u ⟨hu.1.le, hu.2⟩


/-- (8.4) with the sharp law: the Riesz mean of order `r > 0` of a monotone `N` obeying
`N(L) = A L² + B L + o(L)` is `2A L^(r+2)/((r+1)(r+2)) + B L^(r+1)/(r+1) + o(L^(r+1))`. -/
theorem riesz_of_sharp (N : ℝ → ℝ) (hN : Monotone N) (A B r : ℝ) (hr : 0 < r)
    (hlaw : ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, 0 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      |N L - (A * L ^ 2 + B * L)| ≤ δ * L) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      |rieszMean r N L - (2 * A / ((r + 1) * (r + 2)) * L ^ (r + 2) + B / (r + 1) * L ^ (r + 1))|
        ≤ δ * L ^ (r + 1) := by
  intro δ hδ
  have hε : 0 < δ * (r + 1) / 2 := by positivity
  obtain ⟨L1, hL1, h1⟩ := hlaw _ hε
  set ε := δ * (r + 1) / 2 with hεdef
  set K := |N 0| + |N L1| + |A| * L1 ^ 2 + |B| * L1 with hK
  have hK0 : 0 ≤ K := by positivity
  have hb : ∀ u, 0 ≤ u → |N u - (A * u ^ 2 + B * u)| ≤ ε * u + K := by
    intro u hu
    rcases le_or_gt L1 u with h | h
    · have := h1 u h; nlinarith
    · have hn : |N u| ≤ |N 0| + |N L1| := by
        have a := hN hu; have b := hN h.le
        rw [abs_le]; constructor
        · linarith [neg_abs_le (N 0), abs_nonneg (N L1)]
        · linarith [le_abs_self (N L1), abs_nonneg (N 0)]
      have hp : |A * u ^ 2 + B * u| ≤ |A| * L1 ^ 2 + |B| * L1 := by
        calc |A * u ^ 2 + B * u| ≤ |A * u ^ 2| + |B * u| := abs_add_le _ _
          _ = |A| * u ^ 2 + |B| * u := by
              rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg u), abs_of_nonneg hu]
          _ ≤ |A| * L1 ^ 2 + |B| * L1 := by
              gcongr
      have := abs_sub (N u) (A * u ^ 2 + B * u)
      have : 0 ≤ ε * u := by positivity
      linarith
  refine ⟨max 1 (2 * K / δ), fun L hL => ?_⟩
  have hL1' : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hKL : K ≤ δ / 2 * L := by
    have := le_trans (le_max_right _ _) hL
    rw [div_le_iff₀ hδ] at this; linarith
  -- integrability
  have iN : IntervalIntegrable (fun u => (L - u) ^ (r - 1) * N u) MeasureTheory.volume 0 L :=
    kernel_mul_ii r L hr hL0 N (|N 0| + |N L|) hN.measurable (fun u hu => by
      have a := hN hu.1; have b := hN hu.2
      rw [abs_le]; constructor
      · linarith [neg_abs_le (N 0), abs_nonneg (N L)]
      · linarith [le_abs_self (N L), abs_nonneg (N 0)])
  have hk := kernel_ii r L hr
  have i0 : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * u) MeasureTheory.volume 0 L :=
    hk.mul_continuousOn continuous_id.continuousOn
  have i2 : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * u ^ 2) MeasureTheory.volume 0 L :=
    hk.mul_continuousOn (continuous_pow 2).continuousOn
  have iP : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (A * u ^ 2 + B * u))
      MeasureTheory.volume 0 L :=
    hk.mul_continuousOn (by fun_prop)
  have iE : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u)))
      MeasureTheory.volume 0 L := by
    have := iN.sub iP
    refine this.congr (fun u _ => ?_)
    ring
  have iB : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (ε * u + K))
      MeasureTheory.volume 0 L :=
    hk.mul_continuousOn (by fun_prop)
  -- the polynomial part
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
        ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u)) := by
    rw [← intervalIntegral.integral_add iP iE]
    congr 1; funext u; ring
  have hbound : |∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u))| ≤
      ε * (L ^ (r + 1) / (r * (r + 1))) + K * (L ^ r / r) := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hL0) ?_
    have hmono : ∫ u in (0:ℝ)..L, |(L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u))| ≤
        ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (ε * u + K) := by
      refine intervalIntegral.integral_mono_on hL0 iE.abs iB ?_
      intro u hu
      have hk0 : 0 ≤ (L - u) ^ (r - 1) := Real.rpow_nonneg (by linarith [hu.2]) _
      rw [abs_mul, abs_of_nonneg hk0]
      exact mul_le_mul_of_nonneg_left (hb u hu.1) hk0
    refine le_trans hmono (le_of_eq ?_)
    have e : (fun u : ℝ => (L - u) ^ (r - 1) * (ε * u + K)) =
        fun u => ε * ((L - u) ^ (r - 1) * u) + K * (L - u) ^ (r - 1) := by
      funext u; ring
    rw [e, intervalIntegral.integral_add (i0.const_mul ε) (hk.const_mul K),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      kernel_moment1 r L hr hL0, kernel_moment0 r L hr hL0]
  have hLr : L ^ (r + 1) = L ^ r * L := by rw [Real.rpow_add hLpos, Real.rpow_one]
  have hLr2 : L ^ (r + 2) = L ^ r * L * L := by
    rw [show r + 2 = (r + 1) + 1 by ring, Real.rpow_add hLpos, Real.rpow_one, hLr]
  have hLrpos : 0 < L ^ r := Real.rpow_pos_of_pos hLpos r
  unfold rieszMean
  rw [hsplit, hP]
  have key : r * ((A * (2 * L ^ (r + 2) / (r * (r + 1) * (r + 2))) +
      B * (L ^ (r + 1) / (r * (r + 1)))) +
        ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u))) -
      (2 * A / ((r + 1) * (r + 2)) * L ^ (r + 2) + B / (r + 1) * L ^ (r + 1)) =
      r * ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u)) := by
    field_simp; ring
  rw [key, abs_mul, abs_of_pos hr]
  calc r * |∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (N u - (A * u ^ 2 + B * u))|
      ≤ r * (ε * (L ^ (r + 1) / (r * (r + 1))) + K * (L ^ r / r)) :=
        mul_le_mul_of_nonneg_left hbound hr.le
    _ = ε / (r + 1) * L ^ (r + 1) + K * L ^ r := by field_simp
    _ ≤ δ / 2 * L ^ (r + 1) + δ / 2 * L ^ (r + 1) := by
        have e1 : ε / (r + 1) * L ^ (r + 1) = δ / 2 * L ^ (r + 1) := by rw [hεdef]; field_simp
        have e2 : K * L ^ r ≤ δ / 2 * L ^ (r + 1) := by rw [hLr]; nlinarith
        linarith
    _ = δ * L ^ (r + 1) := by ring


/-- One eigenvalue: `r ∫₀^L (L − u)^(r−1) 1[σ ≤ u] du = max(L − σ, 0)^r` for `σ ≥ 0`. -/
theorem riesz_single (r L σ : ℝ) (hr : 0 < r) (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    r * ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (if σ ≤ u then (1:ℝ) else 0) =
      max (L - σ) 0 ^ r := by
  rcases le_or_gt σ L with h | h
  · have hk := kernel_ii r L hr
    have ia : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (if σ ≤ u then (1:ℝ) else 0))
        MeasureTheory.volume 0 σ := by
      refine (IntervalIntegrable.mono_set (kernel_mul_ii r L hr (hσ.trans h) _ 1
        (measurable_const.ite measurableSet_Ici measurable_const) (fun u _ => by
          split_ifs <;> simp)) ?_)
      rw [Set.uIcc_of_le hσ, Set.uIcc_of_le (hσ.trans h)]
      exact Set.Icc_subset_Icc le_rfl h
    have ib : IntervalIntegrable (fun u : ℝ => (L - u) ^ (r - 1) * (if σ ≤ u then (1:ℝ) else 0))
        MeasureTheory.volume σ L := by
      refine (IntervalIntegrable.mono_set (kernel_mul_ii r L hr (hσ.trans h) _ 1
        (measurable_const.ite measurableSet_Ici measurable_const) (fun u _ => by
          split_ifs <;> simp)) ?_)
      rw [Set.uIcc_of_le h, Set.uIcc_of_le (hσ.trans h)]
      exact Set.Icc_subset_Icc hσ le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals ia ib]
    have z : ∫ u in (0:ℝ)..σ, (L - u) ^ (r - 1) * (if σ ≤ u then (1:ℝ) else 0) = 0 := by
      rw [intervalIntegral.integral_of_le hσ]
      refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume σ] with u hu hmem
      have : ¬ σ ≤ u := fun hle => hu (le_antisymm hmem.2 hle)
      simp [this]
    have o : ∫ u in σ..L, (L - u) ^ (r - 1) * (if σ ≤ u then (1:ℝ) else 0) =
        ∫ u in σ..L, (L - u) ^ (r - 1) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le h] at hu
      simp [hu.1]
    rw [z, o, zero_add, intervalIntegral.integral_comp_sub_left (fun t => t ^ (r - 1)) L,
      sub_self, int_rpow (r - 1) (L - σ) (by linarith) (by linarith), sub_add_cancel,
      max_eq_left (by linarith)]
    field_simp
  · rw [max_eq_right (by linarith), Real.zero_rpow hr.ne']
    have : ∫ u in (0:ℝ)..L, (L - u) ^ (r - 1) * (if σ ≤ u then (1:ℝ) else 0) = 0 := by
      refine (intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) fun u hu => ?_).trans
        (by simp)
      rw [Set.uIcc_of_le hL] at hu
      have : ¬ σ ≤ u := by linarith [hu.2]
      simp [this]
    rw [this, mul_zero]

/-- (8.4) for a finite nonnegative spectrum: `Σ_j (L − σ_j)₊^r = r ∫₀^L (L − u)^(r−1) N(u) du`. -/
theorem riesz_finite {n : ℕ} (σ : Fin n → ℝ) (hσ : ∀ j, 0 ≤ σ j) (r L : ℝ) (hr : 0 < r)
    (hL : 0 ≤ L) :
    ∑ j, max (L - σ j) 0 ^ r =
      rieszMean r (fun u => ∑ j, if σ j ≤ u then (1:ℝ) else 0) L := by
  unfold rieszMean
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · exact Finset.sum_congr rfl fun j _ => (riesz_single r L (σ j) hr (hσ j) hL).symm
  · intro j _
    exact kernel_mul_ii r L hr hL _ 1 (measurable_const.ite measurableSet_Ici measurable_const)
      (fun u _ => by split_ifs <;> simp)


/-- `riesz_of_sharp` stated with the project's `HasSharpRealLaw`. -/
theorem riesz_of_sharpLaw (N : ℝ → ℝ) (hN : Monotone N) (A B r : ℝ) (hr : 0 < r)
    (hlaw : HasSharpRealLaw N A B) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      |rieszMean r N L - (2 * A / ((r + 1) * (r + 2)) * L ^ (r + 2) + B / (r + 1) * L ^ (r + 1))|
        ≤ δ * L ^ (r + 1) :=
  riesz_of_sharp N hN A B r hr hlaw

/-- The `L^(r+2)` coefficient in the paper's form: `2 |∂T_a|/(4π) / ((r+1)(r+2)) = √3 a²/(2π(r+1)(r+2))`. -/
theorem leading_coefficient (a r : ℝ) (hr : 0 < r) :
    2 * areaCoeff a / ((r + 1) * (r + 2)) =
      Real.sqrt 3 * a ^ 2 / (2 * Real.pi * (r + 1) * (r + 2)) := by
  unfold areaCoeff
  have := Real.pi_pos
  field_simp
  ring

/-- (1.9) with the paper's constants, from the Theorem 11.1 ledger and monotonicity of `N`. -/
theorem riesz_of_inputs (N : ℝ → ℝ) (hN : Monotone N) (a r : ℝ) (hr : 0 < r)
    (H : Thm111Inputs N a (dihedralCoeff tetraAngle)) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      |rieszMean r N L - (Real.sqrt 3 * a ^ 2 / (2 * Real.pi * (r + 1) * (r + 2)) * L ^ (r + 2) +
        6 * a * dihedralCoeff tetraAngle / (r + 1) * L ^ (r + 1))| ≤ δ * L ^ (r + 1) := by
  intro δ hδ
  obtain ⟨L₀, h⟩ := riesz_of_sharpLaw N hN _ _ r hr (formula_11_4_of_inputs N a H) δ hδ
  refine ⟨L₀, fun L hL => ?_⟩
  have := h L hL
  rwa [leading_coefficient a r hr] at this

/-- At `r = 1` the coefficients of (1.9) are `√3 a²/(12π)` and `3 a c`, as stated after (1.9). -/
theorem first_riesz_coefficients_paper (a c : ℝ) :
    Real.sqrt 3 * a ^ 2 / (2 * Real.pi * (1 + 1) * (1 + 2)) = Real.sqrt 3 * a ^ 2 / (12 * Real.pi) ∧
      6 * a * c / (1 + 1) = 3 * a * c := by
  constructor <;> ring

end SteklovAudit.RieszMeans
