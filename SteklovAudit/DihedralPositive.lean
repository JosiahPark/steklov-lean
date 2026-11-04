import Mathlib
import SteklovAudit.DihedralIntegrable

/-!
# D1: sign of the dihedral invariant, and the flat-edge value

Roadmap item D1 (definition check on the conclusion of Theorem 11.1). Proved here:

* `integrand_pos`: for `0 < α < π` and `v > 0` the integrand of (1.4),
  `f_α(v) = sinh((π−α)v) / (cosh(πv) sinh(αv))`, is strictly positive;
* `integral_pos`, `dihedralCoeff_pos`: hence `c_α > 0` for `0 < α < π` (uses C2 integrability, so
  this is a statement about the genuine integral, not Mathlib's junk value);
* `dihedralCoeff_pi`: `c_π = 0`. A flat "edge" (dihedral angle `π`) contributes no linear term,
  which is consistent with `[H6 face]` carrying zero linear coefficient;
* `dihedralCoeff_tetra_pos`, `edge_term_pos`: at the tetrahedral angle `arccos(1/3)` the second
  coefficient `6 a c_{α₀}` of (11.4) is strictly positive for `a > 0`, so the second term of the
  claimed law is genuinely present (the law does not collapse to the one-term Weyl law).

What this file does NOT prove: any closed form or numerical value of `c_{α₀}`; any hypothesis
`[H1]`–`[H6]`; the main theorem (Theorem 1.3 / 11.1). The hypothesis count in STATUS.md is not
changed.
-/

namespace SteklovAudit.DihedralPositive

open MeasureTheory SteklovAudit.MainConditional

/-- The integrand of (1.4). -/
noncomputable def f (α v : ℝ) : ℝ :=
  Real.sinh ((Real.pi - α) * v) / (Real.cosh (Real.pi * v) * Real.sinh (α * v))

/-- `dihedralCoeff` written with `f`. -/
theorem dihedralCoeff_eq (α : ℝ) :
    dihedralCoeff α = (1 / Real.pi) * ∫ v in Set.Ioi (0 : ℝ), f α v := rfl

/-- C2 restated for `f`. -/
theorem integrableOn_f (α : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) :
    IntegrableOn (f α) (Set.Ioi 0) :=
  DihedralIntegrable.integrableOn_dihedral α h0 hπ

/-- The integrand is strictly positive on `(0, ∞)` for `0 < α < π`. -/
theorem integrand_pos (α v : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) (hv : 0 < v) :
    0 < f α v := by
  unfold f
  have h1 : 0 < Real.sinh ((Real.pi - α) * v) :=
    Real.sinh_pos_iff.mpr (mul_pos (by linarith) hv)
  have h2 : 0 < Real.sinh (α * v) := Real.sinh_pos_iff.mpr (mul_pos h0 hv)
  exact div_pos h1 (mul_pos (Real.cosh_pos _) h2)

/-- The integral in (1.4) is strictly positive for `0 < α < π`. -/
theorem integral_pos (α : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) :
    0 < ∫ v in Set.Ioi (0 : ℝ), f α v := by
  have hint := integrableOn_f α h0 hπ
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f α := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro v hv
    exact (integrand_pos α v h0 hπ hv).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support (f α) ∩ Set.Ioi 0 := by
    intro v hv
    exact ⟨(integrand_pos α v h0 hπ hv).ne', hv⟩
  have h1 : 0 < volume (Set.Ioi (0 : ℝ)) := by simp [Real.volume_Ioi]
  exact lt_of_lt_of_le h1 (measure_mono hsub)

/-- D1. `c_α > 0` for `0 < α < π`. -/
theorem dihedralCoeff_pos (α : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) : 0 < dihedralCoeff α := by
  rw [dihedralCoeff_eq]
  exact mul_pos (one_div_pos.mpr Real.pi_pos) (integral_pos α h0 hπ)

/-- D1. Flat edge: `c_π = 0`. -/
theorem dihedralCoeff_pi : dihedralCoeff Real.pi = 0 := by
  unfold dihedralCoeff
  simp

/-- D1 at the tetrahedral angle: `c_{α₀} > 0`. -/
theorem dihedralCoeff_tetra_pos : 0 < dihedralCoeff tetraAngle :=
  dihedralCoeff_pos _ tetraAngle_mem.1 tetraAngle_mem.2

/-- D1. The second coefficient `6 a c_{α₀}` of (11.4) is strictly positive for `a > 0`. -/
theorem edge_term_pos (a : ℝ) (ha : 0 < a) : 0 < 6 * a * dihedralCoeff tetraAngle :=
  mul_pos (by linarith) dihedralCoeff_tetra_pos

end SteklovAudit.DihedralPositive
