import Mathlib
import SteklovAudit.MainConditional

/-!
# Integrability of the dihedral integrand (roadmap item C2)

For `0 < α < π` the integrand of (1.4),
`f(v) = sinh((π−α)v) / (cosh(πv) sinh(αv))`, is integrable on `(0, ∞)`, so the Bochner integral
in `MainConditional.dihedralCoeff α` is a genuine integral and not Mathlib's junk value `0`.

Proof: with `a = α`, `b = π − α`, elementary exponential bounds give, for `v > 0`,
`sinh(bv) ≤ bv·e^{bv}`, `sinh(av) ≥ av/2` and `cosh(πv) ≥ e^{πv}/2`, hence
`0 ≤ f(v) ≤ (4b/a)·e^{−av}`, which is integrable on `(0, ∞)`.

What this file does NOT prove:
* Any value of `dihedralCoeff α` other than the right-angle case (see `RightAngleCalibration`);
  in particular no closed form at the tetrahedral angle `arccos(1/3)`.
* Any hypothesis H1–H6 of `MainConditional`, or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.DihedralIntegrable

open MeasureTheory

/-- `sinh y ≤ y · e^y` for `y ≥ 0`. -/
theorem sinh_le_mul_exp (y : ℝ) (hy : 0 ≤ y) : Real.sinh y ≤ y * Real.exp y := by
  have h1 := Real.add_one_le_exp (-y)
  have h0 := Real.add_one_le_exp y
  have hE := Real.exp_pos y
  have h3 : Real.exp y * (-y + 1) ≤ 1 := by
    calc Real.exp y * (-y + 1) ≤ Real.exp y * Real.exp (-y) :=
          mul_le_mul_of_nonneg_left h1 hE.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have h4 : 0 ≤ y * (Real.exp y - 1) := mul_nonneg hy (by linarith)
  rw [Real.sinh_eq]
  nlinarith [h3, h1, h4]

/-- `y / 2 ≤ sinh y` for `y ≥ 0`. -/
theorem half_le_sinh (y : ℝ) (hy : 0 ≤ y) : y / 2 ≤ Real.sinh y := by
  have h0 := Real.add_one_le_exp y
  have hE := Real.exp_pos (-y)
  have he : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have h1 : Real.exp (-y) ≤ 1 := by nlinarith [mul_nonneg hE.le (by linarith : 0 ≤ Real.exp y - 1)]
  rw [Real.sinh_eq]
  linarith

/-- `e^x / 2 ≤ cosh x`. -/
theorem exp_half_le_cosh (x : ℝ) : Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-x)]

/-- Pointwise bound: `0 ≤ f(v) ≤ (4b/a) e^{−av}` for `a, b, v > 0`. -/
theorem integrand_bound (a b v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) :
    0 ≤ Real.sinh (b * v) / (Real.cosh ((a + b) * v) * Real.sinh (a * v)) ∧
    Real.sinh (b * v) / (Real.cosh ((a + b) * v) * Real.sinh (a * v)) ≤
      4 * b / a * Real.exp (-a * v) := by
  have hav : 0 < a * v := mul_pos ha hv
  have hbv : 0 < b * v := mul_pos hb hv
  have h1 := sinh_le_mul_exp (b * v) hbv.le
  have h2 := half_le_sinh (a * v) hav.le
  have h3 := exp_half_le_cosh ((a + b) * v)
  have hs : 0 ≤ Real.sinh (b * v) := le_trans (by linarith) (half_le_sinh (b * v) hbv.le)
  have hS : 0 < Real.sinh (a * v) := by linarith
  have hC : 0 < Real.cosh ((a + b) * v) := Real.cosh_pos _
  have hD : 0 < Real.cosh ((a + b) * v) * Real.sinh (a * v) := mul_pos hC hS
  have h4 : Real.exp (b * v) = Real.exp ((a + b) * v) * Real.exp (-a * v) := by
    rw [← Real.exp_add]; congr 1; ring
  have hEb := Real.exp_pos (b * v)
  have hEa := Real.exp_pos (-a * v)
  refine ⟨div_nonneg hs hD.le, ?_⟩
  have key : a * Real.sinh (b * v) ≤
      4 * b * Real.exp (-a * v) * (Real.cosh ((a + b) * v) * Real.sinh (a * v)) := by
    calc a * Real.sinh (b * v) ≤ a * (b * v * Real.exp (b * v)) :=
          mul_le_mul_of_nonneg_left h1 ha.le
      _ = 2 * b * Real.exp (b * v) * (a * v / 2) := by ring
      _ ≤ 2 * b * Real.exp (b * v) * Real.sinh (a * v) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg (mul_nonneg (by norm_num) hb.le) hEb.le)
      _ = 2 * b * Real.sinh (a * v) * Real.exp (-a * v) * Real.exp ((a + b) * v) := by
          rw [h4]; ring
      _ ≤ 2 * b * Real.sinh (a * v) * Real.exp (-a * v) * (2 * Real.cosh ((a + b) * v)) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb.le) hS.le) hEa.le)
      _ = 4 * b * Real.exp (-a * v) * (Real.cosh ((a + b) * v) * Real.sinh (a * v)) := by ring
  rw [div_le_iff₀ hD]
  have e : 4 * b / a * Real.exp (-a * v) * (Real.cosh ((a + b) * v) * Real.sinh (a * v)) =
      (4 * b * Real.exp (-a * v) * (Real.cosh ((a + b) * v) * Real.sinh (a * v))) / a := by
    ring
  rw [e, le_div_iff₀ ha]
  linarith

/-- The generic integrand is integrable on `(0, ∞)` for `a, b > 0`. -/
theorem integrableOn_integrand (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun v : ℝ => Real.sinh (b * v) / (Real.cosh ((a + b) * v) * Real.sinh (a * v)))
      (Set.Ioi 0) := by
  have hg : IntegrableOn (fun v : ℝ => 4 * b / a * Real.exp (-a * v)) (Set.Ioi 0) :=
    by
      first
        | exact Integrable.const_mul (exp_neg_integrableOn_Ioi 0 ha) (4 * b / a)
        | exact (exp_neg_integrableOn_Ioi 0 ha).const_mul (4 * b / a)
  have hc1 : Continuous fun v : ℝ => Real.sinh (b * v) :=
    Real.continuous_sinh.comp (continuous_const.mul continuous_id)
  have hc2 : Continuous fun v : ℝ => Real.cosh ((a + b) * v) :=
    Real.continuous_cosh.comp (continuous_const.mul continuous_id)
  have hc3 : Continuous fun v : ℝ => Real.sinh (a * v) :=
    Real.continuous_sinh.comp (continuous_const.mul continuous_id)
  have hm : AEStronglyMeasurable
      (fun v : ℝ => Real.sinh (b * v) / (Real.cosh ((a + b) * v) * Real.sinh (a * v)))
      (volume.restrict (Set.Ioi 0)) :=
    (hc1.measurable.div (hc2.measurable.mul hc3.measurable)).aestronglyMeasurable
  refine Integrable.mono' hg hm ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro v hv
  try dsimp only
  obtain ⟨h0, h1⟩ := integrand_bound a b v ha hb hv
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- C2. For `0 < α < π` the integrand of (1.4) is integrable on `(0, ∞)`. -/
theorem integrableOn_dihedral (α : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) :
    IntegrableOn (fun v : ℝ => Real.sinh ((Real.pi - α) * v) /
        (Real.cosh (Real.pi * v) * Real.sinh (α * v))) (Set.Ioi 0) := by
  have h := integrableOn_integrand α (Real.pi - α) h0 (by linarith)
  have e : α + (Real.pi - α) = Real.pi := by ring
  simpa only [e] using h

/-- C2 at the tetrahedral angle `arccos(1/3)`. -/
theorem integrableOn_dihedral_tetra :
    IntegrableOn (fun v : ℝ => Real.sinh ((Real.pi - MainConditional.tetraAngle) * v) /
        (Real.cosh (Real.pi * v) * Real.sinh (MainConditional.tetraAngle * v))) (Set.Ioi 0) :=
  integrableOn_dihedral _ MainConditional.tetraAngle_mem.1 MainConditional.tetraAngle_mem.2

end SteklovAudit.DihedralIntegrable
