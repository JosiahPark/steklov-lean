import Mathlib

/-!
# Section 5: the scalar steps of (5.2), (5.9) and (5.10)

Section 5 proves the spectral-window bounds of Theorem 1.2 from homogeneity and an intertwiner.
The operator facts (the diagonal bound `0 ≤ F ≤ C` of Section 2, the scaling (5.1), the Carleson
estimate (5.5), the commutator theorem) are not formalized. This module proves the inequalities that
the text derives from them:

* `strip_trace_increment`: (5.2). With `H(R) = ∫_{−R}^{R} F`, `0 ≤ F ≤ C` and `a_L(γ) = L H(Lγ)`,
  `0 ≤ a_{L₂}(γ) − a_{L₁}(γ) ≤ 2Cγ(L₂² − L₁²)` for `0 ≤ L₁ ≤ L₂` (the paper's `C` absorbs the 2);
* `lorentz_integral_le`, `band_resolvent_integral`: (5.9),
  `∫_{L/2}^{2L} t/((t−L)² + w²) dt ≤ 2πL/w` (narrow windows `w = 1`; the wide-window `O(VL/w)` remark);
* `off_band_gap`: off the band `[L/2, 2L]`, `|t − L| ≥ L/2`, so `‖S_o‖ ≤ 2/L`;
* `off_band_absorb`: (5.10), from `x ≤ w x (2/L) + k (2/L)` and `L > 4w`, `x ≤ 4k/L`.

What this module does NOT prove: (5.1), (5.3), (5.5)–(5.8), Lemma 5.1 itself, or Theorem 1.2.
-/

namespace SteklovAudit.WindowBounds

open MeasureTheory intervalIntegral

/-- `∫_a^b F ≤ C (b − a)` and `≥ 0` for `0 ≤ F ≤ C`, `a ≤ b`. -/
theorem int_bounds (F : ℝ → ℝ) (C a b : ℝ) (hab : a ≤ b) (hF : IntervalIntegrable F volume a b)
    (h0 : ∀ u, 0 ≤ F u) (hC : ∀ u, F u ≤ C) :
    0 ≤ ∫ u in a..b, F u ∧ ∫ u in a..b, F u ≤ C * (b - a) := by
  refine ⟨intervalIntegral.integral_nonneg hab fun u _ => h0 u, ?_⟩
  have := intervalIntegral.integral_mono_on hab hF intervalIntegrable_const fun u _ => hC u
  simpa [mul_comm] using this

/-- `H(R) = ∫_{−R}^{R} F`. -/
noncomputable def Hc (F : ℝ → ℝ) (R : ℝ) : ℝ := ∫ u in (-R)..R, F u

theorem Hc_increment (F : ℝ → ℝ) (C R1 R2 : ℝ) (h12 : R1 ≤ R2)
    (hF : ∀ a b, IntervalIntegrable F volume a b) (h0 : ∀ u, 0 ≤ F u) (hC : ∀ u, F u ≤ C) :
    0 ≤ Hc F R2 - Hc F R1 ∧ Hc F R2 - Hc F R1 ≤ 2 * C * (R2 - R1) := by
  have e : Hc F R2 = (∫ u in (-R2)..(-R1), F u) + Hc F R1 + ∫ u in R1..R2, F u := by
    unfold Hc
    rw [intervalIntegral.integral_add_adjacent_intervals (hF _ _) (hF _ _),
      intervalIntegral.integral_add_adjacent_intervals (hF _ _) (hF _ _)]
  obtain ⟨a0, a1⟩ := int_bounds F C (-R2) (-R1) (by linarith) (hF _ _) h0 hC
  obtain ⟨b0, b1⟩ := int_bounds F C R1 R2 h12 (hF _ _) h0 hC
  rw [e]
  constructor <;> nlinarith

/-- (5.2): with `a_L(γ) = L H(Lγ)`, for `0 ≤ L₁ ≤ L₂` and `γ ≥ 0`,
`0 ≤ a_{L₂}(γ) − a_{L₁}(γ) ≤ 2Cγ(L₂² − L₁²)`. -/
theorem strip_trace_increment (F : ℝ → ℝ) (C γ L1 L2 : ℝ) (hγ : 0 ≤ γ) (h1 : 0 ≤ L1)
    (h12 : L1 ≤ L2) (hF : ∀ a b, IntervalIntegrable F volume a b) (h0 : ∀ u, 0 ≤ F u)
    (hC : ∀ u, F u ≤ C) :
    0 ≤ L2 * Hc F (L2 * γ) - L1 * Hc F (L1 * γ) ∧
      L2 * Hc F (L2 * γ) - L1 * Hc F (L1 * γ) ≤ 2 * C * γ * (L2 ^ 2 - L1 ^ 2) := by
  have hR : L1 * γ ≤ L2 * γ := mul_le_mul_of_nonneg_right h12 hγ
  obtain ⟨i0, i1⟩ := Hc_increment F C (L1 * γ) (L2 * γ) hR hF h0 hC
  obtain ⟨z0, z1⟩ := Hc_increment F C 0 (L2 * γ) (mul_nonneg (h1.trans h12) hγ) hF h0 hC
  have hz : Hc F 0 = 0 := by simp [Hc]
  rw [hz] at z0 z1
  simp only [sub_zero] at z0 z1
  have e : L2 * Hc F (L2 * γ) - L1 * Hc F (L1 * γ) =
      (L2 - L1) * Hc F (L2 * γ) + L1 * (Hc F (L2 * γ) - Hc F (L1 * γ)) := by ring
  rw [e]
  have hL : 0 ≤ L2 - L1 := by linarith
  constructor
  · exact add_nonneg (mul_nonneg hL z0) (mul_nonneg h1 i0)
  · have p1 : (L2 - L1) * Hc F (L2 * γ) ≤ (L2 - L1) * (2 * C * (L2 * γ)) :=
      mul_le_mul_of_nonneg_left z1 hL
    have p2 : L1 * (Hc F (L2 * γ) - Hc F (L1 * γ)) ≤ L1 * (2 * C * (L2 * γ - L1 * γ)) :=
      mul_le_mul_of_nonneg_left i1 h1
    nlinarith


/-- `∫_a^b dt/((t − L)² + w²) ≤ π/w` for `w > 0`, `a ≤ b`. -/
theorem lorentz_integral_le (a b L w : ℝ) (hab : a ≤ b) (hw : 0 < w) :
    ∫ t in a..b, 1 / ((t - L) ^ 2 + w ^ 2) ≤ Real.pi / w := by
  have hd : ∀ t, HasDerivAt (fun t => Real.arctan ((t - L) / w) / w) (1 / ((t - L) ^ 2 + w ^ 2)) t := by
    intro t
    have h := (((hasDerivAt_id' t).sub_const L).div_const w).arctan.div_const w
    refine h.congr_deriv ?_
    have : (t - L) ^ 2 + w ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hcont : Continuous fun t : ℝ => 1 / ((t - L) ^ 2 + w ^ 2) := by
    fun_prop (disch := intro t; positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable _ _)]
  have h1 := Real.arctan_lt_pi_div_two ((b - L) / w)
  have h2 := Real.neg_pi_div_two_lt_arctan ((a - L) / w)
  rw [← sub_div, div_le_div_iff_of_pos_right hw]
  linarith

/-- (5.9): `∫_{L/2}^{2L} t/((t − L)² + w²) dt ≤ 2πL/w` (narrow windows: `w = 1`, `≤ 2πL`;
wide windows: `O(L/w)`). -/
theorem band_resolvent_integral (L w : ℝ) (hL : 0 < L) (hw : 0 < w) :
    ∫ t in (L / 2)..(2 * L), t / ((t - L) ^ 2 + w ^ 2) ≤ 2 * Real.pi * L / w := by
  have hab : L / 2 ≤ 2 * L := by linarith
  have hcont : Continuous fun t : ℝ => 1 / ((t - L) ^ 2 + w ^ 2) := by
    fun_prop (disch := intro t; positivity)
  have hmono : ∫ t in (L / 2)..(2 * L), t / ((t - L) ^ 2 + w ^ 2) ≤
      ∫ t in (L / 2)..(2 * L), 2 * L * (1 / ((t - L) ^ 2 + w ^ 2)) := by
    refine intervalIntegral.integral_mono_on hab ?_ ((hcont.intervalIntegrable _ _).const_mul _) ?_
    · have hc2 : Continuous fun t : ℝ => t / ((t - L) ^ 2 + w ^ 2) := by
        fun_prop (disch := intro t; positivity)
      exact hc2.intervalIntegrable _ _
    · intro t ht
      have hpos : 0 < (t - L) ^ 2 + w ^ 2 := by positivity
      rw [div_eq_mul_one_div t]
      exact mul_le_mul_of_nonneg_right ht.2 (by positivity)
  rw [intervalIntegral.integral_const_mul] at hmono
  have := lorentz_integral_le (L / 2) (2 * L) L w hab hw
  calc _ ≤ _ := hmono
    _ ≤ 2 * L * (Real.pi / w) := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * Real.pi * L / w := by ring

/-- `‖S_o‖ ≤ 2/L`: off the band `[L/2, 2L]`, a point `t ≥ 0` has `|t − L| ≥ L/2`. -/
theorem off_band_gap (L t : ℝ) (ht : 0 ≤ t) (hout : t < L / 2 ∨ 2 * L < t) (hL : 0 < L) :
    L / 2 ≤ |t - L| := by
  rcases hout with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- (5.10), the absorption step: from `X = (A − L) X S_o − E K S_o` with `‖(A − L)E‖ ≤ w` and
`‖S_o‖ ≤ 2/L`, the norms satisfy `x ≤ w x (2/L) + k (2/L)`; if `L > 4w` then `x ≤ 4k/L`. -/
theorem off_band_absorb (x k w L : ℝ) (hx : 0 ≤ x) (hw : 0 ≤ w) (hL : 4 * w < L)
    (h : x ≤ w * x * (2 / L) + k * (2 / L)) : x ≤ 4 * k / L := by
  have hL0 : 0 < L := by linarith
  rw [le_div_iff₀ hL0]
  have h' : x * L ≤ 2 * w * x + 2 * k := by
    have := mul_le_mul_of_nonneg_right h hL0.le
    field_simp at this
    linarith
  nlinarith

end SteklovAudit.WindowBounds
