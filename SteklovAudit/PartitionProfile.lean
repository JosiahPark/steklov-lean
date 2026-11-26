import Mathlib

/-!
# The transition profile of the tetrahedral partition (roadmap item K6)

First step of the explicit partition of `∂T_a` (Josiah's construction, 2026-11-26) that is meant to
prove the ledger inputs H1–H3 of `MainConditional.lean` for the actual tetrahedral geometry.

A profile is a continuous `β : ℝ → ℝ` with `β t = 0` for `t ≤ 1`, `β t = π/2` for `t ≥ 2`, and the
reflection symmetry `β t + β (3 - t) = π/2`. With `c = cos ∘ β`, `s = sin ∘ β`:

* `cos_sq_add_sin_sq_profile`: `c² + s² = 1` (so vertex weights `ζ_v = c(R_v/ε)` and the complement
  `s(R_v/ε)` square-sum to `1` without square roots);
* `cos_sq_reflect`: `c(3 - t)² = s(t)²`;
* `integral_cos_sq`: `∫₀² c² = 3/2`, and `integral_sin_sq`: `∫₀² s² = 1/2`. These give the kept edge
  length `a − 3ε` per edge (`6a − 18ε` in total) and the transverse width `3γ/2` per face side used
  by the later items;
* `smoothProfile`: an explicit SMOOTH profile `t ↦ π/2 · smoothTransition (t − 1)`, with
  `smoothProfile_isProfile`, `smoothProfile_contDiff` and `smoothProfile_integral`.

What this file does NOT prove: the pointwise partition identity on `∂T_a`, the kept-length and
edge-area identities themselves (items K7, K8), the ledger inputs H1–H3 for the paper's operator, or
anything about H4–H6 or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.PartitionProfile

open Real

/-- **K6.** A transition profile: `0` below `1`, `π/2` above `2`, reflection-symmetric about `3/2`. -/
def IsProfile (β : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, t ≤ 1 → β t = 0) ∧ (∀ t : ℝ, 2 ≤ t → β t = π / 2) ∧
    ∀ t : ℝ, β t + β (3 - t) = π / 2

/-- **K6.** The two weights of a profile square-sum to `1`. -/
theorem cos_sq_add_sin_sq_profile (β : ℝ → ℝ) (t : ℝ) : cos (β t) ^ 2 + sin (β t) ^ 2 = 1 :=
  cos_sq_add_sin_sq (β t)

/-- **K6.** Reflection: `cos (β (3 - t))² = sin (β t)²`. -/
theorem cos_sq_reflect (β : ℝ → ℝ) (h : IsProfile β) (t : ℝ) :
    cos (β (3 - t)) ^ 2 = sin (β t) ^ 2 := by
  have e : β (3 - t) = π / 2 - β t := by linarith [h.2.2 t]
  rw [e, cos_pi_div_two_sub]

/-- **K6.** `∫₀² cos(β t)² dt = 3/2`. -/
theorem integral_cos_sq (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) :
    ∫ t in (0 : ℝ)..2, cos (β t) ^ 2 = 3 / 2 := by
  have hc : Continuous (fun t => cos (β t) ^ 2) := (continuous_cos.comp hβ).pow 2
  have hs : Continuous (fun t => sin (β t) ^ 2) := (continuous_sin.comp hβ).pow 2
  have h01 : ∫ t in (0 : ℝ)..1, cos (β t) ^ 2 = 1 := by
    have e : ∫ t in (0 : ℝ)..1, cos (β t) ^ 2 = ∫ t in (0 : ℝ)..1, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      show cos (β t) ^ 2 = 1
      rw [h.1 t ht.2, cos_zero, one_pow]
    rw [e]
    simp
  have hrefl : ∫ t in (1 : ℝ)..2, sin (β t) ^ 2 = ∫ t in (1 : ℝ)..2, cos (β t) ^ 2 := by
    have e1 : ∫ t in (1 : ℝ)..2, sin (β t) ^ 2 = ∫ t in (1 : ℝ)..2, cos (β (3 - t)) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      show sin (β t) ^ 2 = cos (β (3 - t)) ^ 2
      rw [cos_sq_reflect β h t]
    have e2 : ∫ t in (1 : ℝ)..2, cos (β (3 - t)) ^ 2 = ∫ t in (1 : ℝ)..2, cos (β t) ^ 2 := by
      first
        | (have e3 := intervalIntegral.integral_comp_sub_left (fun t => cos (β t) ^ 2) (3 : ℝ)
            (a := 1) (b := 2)
           norm_num at e3
           exact e3)
        | (rw [intervalIntegral.integral_comp_sub_left (fun t => cos (β t) ^ 2)]
           norm_num)
    rw [e1]
    exact e2
  have h12 : ∫ t in (1 : ℝ)..2, cos (β t) ^ 2 = 1 / 2 := by
    have hsum : ∫ t in (1 : ℝ)..2, (cos (β t) ^ 2 + sin (β t) ^ 2) = 1 := by
      have e : ∫ t in (1 : ℝ)..2, (cos (β t) ^ 2 + sin (β t) ^ 2) = ∫ t in (1 : ℝ)..2, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t _
        show cos (β t) ^ 2 + sin (β t) ^ 2 = 1
        exact cos_sq_add_sin_sq (β t)
      rw [e]
      norm_num
    rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hs.intervalIntegrable _ _),
      hrefl] at hsum
    linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 1)
    (hc.intervalIntegrable 1 2), h01, h12]
  norm_num

/-- **K6.** `∫₀² sin(β t)² dt = 1/2`. -/
theorem integral_sin_sq (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) :
    ∫ t in (0 : ℝ)..2, sin (β t) ^ 2 = 1 / 2 := by
  have hc : Continuous (fun t => cos (β t) ^ 2) := (continuous_cos.comp hβ).pow 2
  have hs : Continuous (fun t => sin (β t) ^ 2) := (continuous_sin.comp hβ).pow 2
  have hsum : ∫ t in (0 : ℝ)..2, (cos (β t) ^ 2 + sin (β t) ^ 2) = 2 := by
    have e : ∫ t in (0 : ℝ)..2, (cos (β t) ^ 2 + sin (β t) ^ 2) = ∫ t in (0 : ℝ)..2, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t _
      show cos (β t) ^ 2 + sin (β t) ^ 2 = 1
      exact cos_sq_add_sin_sq (β t)
    rw [e]
    norm_num
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hs.intervalIntegrable _ _),
    integral_cos_sq β hβ h] at hsum
  linarith

/-- **K6.** `smoothTransition x + smoothTransition (1 - x) = 1`. -/
theorem smoothTransition_add_reflect (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  have hd := Real.smoothTransition.pos_denom x
  unfold Real.smoothTransition
  rw [show (1 : ℝ) - (1 - x) = x by ring,
    add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x), ← add_div]
  exact div_self (ne_of_gt hd)

/-- **K6.** An explicit smooth profile. -/
noncomputable def smoothProfile (t : ℝ) : ℝ := π / 2 * Real.smoothTransition (t - 1)

/-- **K6.** `smoothProfile` is a profile. -/
theorem smoothProfile_isProfile : IsProfile smoothProfile := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t => ?_⟩
  · unfold smoothProfile
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]
  · unfold smoothProfile
    rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one]
  · unfold smoothProfile
    have e := smoothTransition_add_reflect (t - 1)
    rw [show (1 : ℝ) - (t - 1) = 3 - t - 1 by ring] at e
    rw [← mul_add, e, mul_one]

/-- **K6.** `smoothProfile` is smooth. -/
theorem smoothProfile_contDiff {n : ℕ∞} : ContDiff ℝ n smoothProfile := by
  first
    | exact contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
    | (unfold smoothProfile
       exact contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))
    | (unfold smoothProfile; fun_prop)

/-- **K6.** For the smooth profile, `∫₀² cos² = 3/2`. -/
theorem smoothProfile_integral : ∫ t in (0 : ℝ)..2, cos (smoothProfile t) ^ 2 = 3 / 2 :=
  integral_cos_sq smoothProfile ((smoothProfile_contDiff (n := 0)).continuous)
    smoothProfile_isProfile

end SteklovAudit.PartitionProfile
