import Mathlib
import SteklovAudit.DihedralIntegrable

/-!
# C7: sanity checks on the dihedral coefficient and the tetrahedral angle

Roadmap item C7. Definition checks for `MainConditional.dihedralCoeff` and
`MainConditional.tetraAngle`, complementing C2 (integrability) and C3 (`c_{π/2} = 1/(2π)`):

* `dihedralCoeff_pi`: `c_π = 0` (a flat "edge" contributes nothing to the linear term);
* `integrand_pos`: the integrand of (1.4) is strictly positive on `(0, ∞)` for `0 < α < π`;
* `dihedralCoeff_pos`: `0 < c_α` for `0 < α < π`, so the edge correction has a definite sign and
  `6 a c_{α₀}` is a genuinely nonzero linear coefficient;
* `cos_tetraAngle`: `cos α₀ = 1/3`; `tetraAngle_lt_pi_div_two`: `α₀ < π/2`.

What this file does NOT prove: any value of `c_{α₀}` (no closed form or numerics at
`α₀ = arccos(1/3)`), any hypothesis H1–H6, or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.DihedralSanity

open MeasureTheory SteklovAudit.MainConditional

/-- `c_π = 0`. -/
theorem dihedralCoeff_pi : dihedralCoeff Real.pi = 0 := by
  unfold dihedralCoeff
  simp

/-- The integrand of (1.4) is positive on `(0, ∞)`. -/
theorem integrand_pos (α v : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) (hv : 0 < v) :
    0 < Real.sinh ((Real.pi - α) * v) / (Real.cosh (Real.pi * v) * Real.sinh (α * v)) := by
  have h1 : 0 < Real.sinh ((Real.pi - α) * v) :=
    Real.sinh_pos_iff.mpr (mul_pos (by linarith) hv)
  have h2 : 0 < Real.sinh (α * v) := Real.sinh_pos_iff.mpr (mul_pos h0 hv)
  exact div_pos h1 (mul_pos (Real.cosh_pos _) h2)

/-- `0 < c_α` for `0 < α < π`. -/
theorem dihedralCoeff_pos (α : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) : 0 < dihedralCoeff α := by
  unfold dihedralCoeff
  have hint := DihedralIntegrable.integrableOn_dihedral α h0 hπ
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun v : ℝ => Real.sinh ((Real.pi - α) * v) /
        (Real.cosh (Real.pi * v) * Real.sinh (α * v))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (integrand_pos α v h0 hπ hv).le
  have hs : Function.support (fun v : ℝ => Real.sinh ((Real.pi - α) * v) /
      (Real.cosh (Real.pi * v) * Real.sinh (α * v))) ∩ Set.Ioi 0 = Set.Ioi 0 :=
    Set.inter_eq_right.mpr (fun v hv => Function.mem_support.mpr (integrand_pos α v h0 hπ hv).ne')
  have hI : 0 < ∫ v in Set.Ioi (0 : ℝ),
      Real.sinh ((Real.pi - α) * v) / (Real.cosh (Real.pi * v) * Real.sinh (α * v)) := by
    first
      | rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
      | rw [MeasureTheory.set_integral_pos_iff_support_of_nonneg_ae hnn hint]
    rw [hs, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  exact mul_pos (one_div_pos.mpr Real.pi_pos) hI

/-- `cos α₀ = 1/3`. -/
theorem cos_tetraAngle : Real.cos tetraAngle = 1 / 3 := by
  unfold tetraAngle
  exact Real.cos_arccos (by norm_num) (by norm_num)

/-- The tetrahedral dihedral angle is acute. -/
theorem tetraAngle_lt_pi_div_two : tetraAngle < Real.pi / 2 := by
  unfold tetraAngle
  first
    | exact Real.arccos_lt_pi_div_two.mpr (by norm_num)
    | (rw [Real.arccos_eq_pi_div_two_sub_arcsin]
       linarith [Real.arcsin_pos.mpr (show (0 : ℝ) < 1 / 3 by norm_num)])

/-- The linear coefficient at the tetrahedral angle is positive. -/
theorem dihedralCoeff_tetra_pos : 0 < dihedralCoeff tetraAngle :=
  dihedralCoeff_pos _ tetraAngle_mem.1 tetraAngle_mem.2

end SteklovAudit.DihedralSanity
