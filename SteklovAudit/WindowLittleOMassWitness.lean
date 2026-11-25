import Mathlib
import SteklovAudit.WindowLittleOMass

/-!
# The local-mass weakening of G158 is strict and non-vacuous (roadmap item G159)

Row 3 of the priority table (abstract cumulative budget refinement). G158
(`WindowLittleOMass.littleO_of_window_littleO_mass`) replaces the local spectral mass input `O(L)`
on the bounded-defect window route by `o(L²)`. This file checks, on one explicit model, that the new
input is strictly weaker and that all hypotheses of G158 can hold at once.

Model: mass `wm L = max L 0 · √(max L 0)` (that is, `L^{3/2}` for `L ≥ 0`), remainder
`wr L = √(max L 0)`, constants `C = K = ε₀ = 1`.

* `wm_nonneg`: the model mass is nonnegative.
* `wm_littleO_sq`: the model mass is `o(L²)`.
* `wm_not_linear`: the model mass is NOT `O(L)`, so the weakening is strict.
* `witness_window_hyp`: the window hypothesis of G158 holds for `wr`, `wm`.
* `witness_littleO`: G158 applied to the model.

What this file does NOT prove: any local mass bound for the actual operator, the window bound for the
localized tetrahedron–wedge error, Lemma 7.1′ / (7.2), Proposition 7.3, (7.29), H5, or
Theorem 1.3 / 11.1. Everything here is real analysis of explicit scalar functions.
-/

namespace SteklovAudit.WindowLittleOMassWitness

open Filter

/-- Model local mass `L^{3/2}` (for `L ≥ 0`). -/
noncomputable def wm (L : ℝ) : ℝ := max L 0 * Real.sqrt (max L 0)

/-- Model remainder `√(max L 0)`. -/
noncomputable def wr (L : ℝ) : ℝ := Real.sqrt (max L 0)

/-- **G159.** The model mass is nonnegative. -/
theorem wm_nonneg : ∀ L : ℝ, 0 ≤ wm L := fun L =>
  mul_nonneg (le_max_right L 0) (Real.sqrt_nonneg _)

/-- **G159.** The model mass is `o(L²)`. -/
theorem wm_littleO_sq : ∀ δ : ℝ, 0 < δ → ∀ᶠ L in atTop, wm L ≤ δ * L ^ 2 := by
  intro δ hδ
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ((1 / δ) ^ 2)] with L hL1 hL2
  have hL0 : 0 ≤ L := by linarith
  have hmax : max L 0 = L := max_eq_left hL0
  have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0
  have hs : 1 / δ ≤ Real.sqrt L := by
    have h := Real.sqrt_le_sqrt hL2
    rwa [Real.sqrt_sq (le_of_lt (one_div_pos.mpr hδ))] at h
  have hds : 1 ≤ Real.sqrt L * δ := by
    first
      | exact (div_le_iff₀ hδ).1 hs
      | exact (div_le_iff hδ).1 hs
  show max L 0 * Real.sqrt (max L 0) ≤ δ * L ^ 2
  rw [hmax]
  have h1 : L * Real.sqrt L * 1 ≤ L * Real.sqrt L * (Real.sqrt L * δ) :=
    mul_le_mul_of_nonneg_left hds (mul_nonneg hL0 hs0)
  have e : L * Real.sqrt L * (Real.sqrt L * δ) = δ * L ^ 2 := by
    calc L * Real.sqrt L * (Real.sqrt L * δ) = δ * L * Real.sqrt L ^ 2 := by ring
      _ = δ * L ^ 2 := by rw [hsq]; ring
  linarith

/-- **G159.** The model mass is not `O(L)`: the `o(L²)` input of G158 is strictly weaker. -/
theorem wm_not_linear : ¬ ∃ M : ℝ, ∀ᶠ L in atTop, wm L ≤ M * L := by
  rintro ⟨M, hM⟩
  obtain ⟨L, h1, h2⟩ := (hM.and (eventually_ge_atTop ((|M| + 1) ^ 2))).exists
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg |M|]
  have hL0 : 0 ≤ L := by linarith
  have hmax : max L 0 = L := max_eq_left hL0
  have hs : |M| + 1 ≤ Real.sqrt L := by
    have h := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (by linarith)] at h
  have h1' : max L 0 * Real.sqrt (max L 0) ≤ M * L := h1
  rw [hmax] at h1'
  nlinarith [mul_le_mul_of_nonneg_left hs hL0, mul_le_mul_of_nonneg_left (le_abs_self M) hL0]

/-- **G159.** The window hypothesis of `littleO_of_window_littleO_mass` holds for the model with
`C = K = ε₀ = 1`. -/
theorem witness_window_hyp : ∀ T : ℝ, 0 < T → ∀ᶠ L in atTop,
    |wr L| ≤ 1 * L / T + 1 * T * 1 * Real.sqrt (wm L) := by
  intro T hT
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (T ^ 2)] with L hL1 hL2
  have hL0 : 0 ≤ L := by linarith
  have hmax : max L 0 = L := max_eq_left hL0
  have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0
  have hTs : T ≤ Real.sqrt L := by
    have h := Real.sqrt_le_sqrt hL2
    rwa [Real.sqrt_sq hT.le] at h
  have hsT : Real.sqrt L * T ≤ L := by nlinarith [mul_le_mul_of_nonneg_left hTs hs0]
  have hdiv : Real.sqrt L ≤ L / T := by
    first
      | exact (le_div_iff₀ hT).2 hsT
      | exact (le_div_iff hT).2 hsT
  have hpos : 0 ≤ 1 * T * 1 * Real.sqrt (wm L) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have e : 1 * L / T = L / T := by ring
  show |Real.sqrt (max L 0)| ≤ 1 * L / T + 1 * T * 1 * Real.sqrt (wm L)
  rw [hmax, abs_of_nonneg hs0]
  linarith

/-- **G159.** G158 applied to the model: `wr = o(L)` with local mass `L^{3/2}`, which is not `O(L)`. -/
theorem witness_littleO : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |wr L| ≤ η * L :=
  SteklovAudit.WindowLittleOMass.littleO_of_window_littleO_mass wr wm 1 1 1
    zero_le_one zero_le_one zero_le_one
    (by filter_upwards with L; exact wm_nonneg L) wm_littleO_sq witness_window_hyp

end SteklovAudit.WindowLittleOMassWitness
