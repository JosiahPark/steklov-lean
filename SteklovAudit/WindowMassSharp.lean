import Mathlib
import SteklovAudit.WindowLittleOMass

/-!
# The `o(L²)` local-mass input of the window route is sharp (roadmap item G165)

Row 3 of the priority table (abstract cumulative budget refinement); a definition check on the F-table
row "Localized spectral mass". G158 (`WindowLittleOMass.littleO_of_window_littleO_mass`) derives
`r = o(L)` from the window bound `|r L| ≤ C L / T + K T ε₀ √(m L)` (bounded defect `ε₀`) when the local
mass satisfies `m L = o(L²)`. This file shows that `o(L²)` cannot be weakened to `O(L²)` on this route:
with `r L = L`, `m L = L²`, `C = K = ε₀ = 1`, the window hypothesis holds for every `T > 0`, the mass is
`O(L²)` but not `o(L²)`, and `r` is not `o(L)`.

* `sq_mass_window_hyp`: the window hypothesis holds for the model.
* `sq_mass_nonneg`, `sq_mass_bounded`: the model mass is nonnegative and `O(L²)`.
* `sq_mass_not_littleO_sq`: the model mass is not `o(L²)`.
* `sq_mass_conclusion_fails`: the model remainder is not `o(L)`.
* `bounded_mass_insufficient`: all of this packaged as one existence statement.

What this file does NOT prove: any local mass bound (neither `O(L)` nor `o(L²)`) for the actual
operator, the window bound for the localized tetrahedron–wedge error, the HS defect bound (Lemma 7.1′),
Proposition 7.3, (7.29), H5, or Theorem 1.3 / 11.1. It is real analysis of explicit scalar functions;
no analytic input about the Steklov problem is used or assumed.
-/

namespace SteklovAudit.WindowMassSharp

open Filter

/-- **G165.** The window hypothesis of G158 holds for `r L = L`, `m L = L²`, `C = K = ε₀ = 1`. -/
theorem sq_mass_window_hyp : ∀ T : ℝ, 0 < T → ∀ᶠ L in atTop,
    |L| ≤ 1 * L / T + 1 * T * 1 * Real.sqrt (L ^ 2) := by
  intro T hT
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  rw [abs_of_nonneg hL, Real.sqrt_sq hL]
  have hu0 : 0 ≤ L / T := div_nonneg hL hT.le
  have huT : L / T * T = L := div_mul_cancel₀ L (ne_of_gt hT)
  have e : 1 * L / T + 1 * T * 1 * L = L / T + T * L := by ring
  rw [e]
  rcases le_or_gt 1 T with h1 | h1
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) hL]
  · nlinarith [mul_nonneg hu0 (sub_nonneg.2 h1.le), mul_nonneg hT.le hL]

/-- **G165.** The model mass `L²` is nonnegative. -/
theorem sq_mass_nonneg : ∀ᶠ L in atTop, (0 : ℝ) ≤ L ^ 2 := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L _
  positivity

/-- **G165.** The model mass `L²` is `O(L²)` (constant `1`). -/
theorem sq_mass_bounded : ∀ᶠ (L : ℝ) in atTop, L ^ 2 ≤ 1 * L ^ 2 := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L _
  linarith

/-- **G165.** The model mass `L²` is not `o(L²)`. -/
theorem sq_mass_not_littleO_sq : ¬ ∀ δ : ℝ, 0 < δ → ∀ᶠ L in atTop, L ^ 2 ≤ δ * L ^ 2 := by
  intro h
  obtain ⟨L, h1, h2⟩ := ((h (1 / 2) (by norm_num)).and (eventually_gt_atTop (0 : ℝ))).exists
  have hL2 : 0 < L ^ 2 := by positivity
  linarith

/-- **G165.** The model remainder `r L = L` is not `o(L)`. -/
theorem sq_mass_conclusion_fails : ¬ ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |L| ≤ η * L := by
  intro h
  obtain ⟨L, h1, h2⟩ := ((h (1 / 2) (by norm_num)).and (eventually_gt_atTop (0 : ℝ))).exists
  rw [abs_of_pos h2] at h1
  linarith

/-- **G165.** On the window route, an `O(L²)` local mass (in place of G158's `o(L²)`) together with
all the other hypotheses of `littleO_of_window_littleO_mass` does not give `r = o(L)`. -/
theorem bounded_mass_insufficient :
    ∃ r m : ℝ → ℝ, ∃ C K ε₀ : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ 0 ≤ ε₀ ∧ (∀ᶠ L in atTop, 0 ≤ m L) ∧
      (∀ᶠ L in atTop, m L ≤ 1 * L ^ 2) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ L in atTop, |r L| ≤ C * L / T + K * T * ε₀ * Real.sqrt (m L)) ∧
      ¬ ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L :=
  ⟨fun L => L, fun L => L ^ 2, 1, 1, 1, zero_le_one, zero_le_one, zero_le_one, sq_mass_nonneg,
    sq_mass_bounded, sq_mass_window_hyp, sq_mass_conclusion_fails⟩

end SteklovAudit.WindowMassSharp
