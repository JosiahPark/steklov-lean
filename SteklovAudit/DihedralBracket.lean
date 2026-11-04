import Mathlib
import SteklovAudit.DihedralBounds
import SteklovAudit.DihedralSanity

/-!
# C11: numeric bracket for the edge coefficient `c_{α₀}`

Roadmap item C11, for `c_α = MainConditional.dihedralCoeff α` (formula (1.4)) at the tetrahedral
dihedral angle `α₀ = tetraAngle = arccos(1/3)`:

* `pi_div_three_lt_tetraAngle`: `π/3 < α₀` (cosine is antitone on `[0, π]`, `cos(π/3) = 1/2`,
  `cos α₀ = 1/3`).
* `bound_le_of_ge`: for `π/3 ≤ α`, the C9 bound satisfies `4(π − α)/(π α²) ≤ 24/π²`
  (its value at `π/3`; the bound is antitone in `α`).
* `dihedralCoeff_tetra_le_bracket`: `c_{α₀} ≤ 24/π²`, from C9 (`dihedralCoeff_tetra_le`).
* `dihedralCoeff_tetra_bracket`: `1/(2π) ≤ c_{α₀} ≤ 24/π²`, with C10 (`dihedralCoeff_tetra_ge`).

What this file does NOT prove: the exact value of `c_{α₀}`, any hypothesis H1–H6 of
`MainConditional`, or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.DihedralBracket

open SteklovAudit.MainConditional

/-- `π/3 < α₀ = arccos(1/3)`. -/
theorem pi_div_three_lt_tetraAngle : Real.pi / 3 < tetraAngle := by
  have hpi := Real.pi_pos
  have h0 : 0 ≤ tetraAngle := tetraAngle_mem.1.le
  have hlt : tetraAngle < Real.pi := tetraAngle_mem.2
  by_contra h
  push_neg at h
  have hc : Real.cos (Real.pi / 3) ≤ Real.cos tetraAngle := by
    first
      | exact Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith) h
      | exact Real.strictAntiOn_cos.antitoneOn ⟨h0, hlt.le⟩ ⟨by positivity, by linarith⟩ h
  rw [Real.cos_pi_div_three, DihedralSanity.cos_tetraAngle] at hc
  norm_num at hc

/-- The C9 bound `4(π − α)/(π α²)` is at most its value `24/π²` at `α = π/3`, for `α ≥ π/3`. -/
theorem bound_le_of_ge (α : ℝ) (hα : Real.pi / 3 ≤ α) :
    4 * (Real.pi - α) / (Real.pi * α ^ 2) ≤ 24 / Real.pi ^ 2 := by
  have hpi := Real.pi_pos
  have hα0 : 0 < α := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : 0 ≤ 3 * α - Real.pi := by linarith
  have hkey : 0 ≤ Real.pi * (3 * α - Real.pi) * (2 * α + Real.pi) :=
    mul_nonneg (mul_nonneg hpi.le h3) (by linarith)
  nlinarith [hkey]

/-- C11, upper half: `c_{α₀} ≤ 24/π²`. -/
theorem dihedralCoeff_tetra_le_bracket : dihedralCoeff tetraAngle ≤ 24 / Real.pi ^ 2 :=
  le_trans DihedralBounds.dihedralCoeff_tetra_le
    (bound_le_of_ge tetraAngle pi_div_three_lt_tetraAngle.le)

/-- C11: `1/(2π) ≤ c_{α₀} ≤ 24/π²`. -/
theorem dihedralCoeff_tetra_bracket :
    1 / (2 * Real.pi) ≤ dihedralCoeff tetraAngle ∧ dihedralCoeff tetraAngle ≤ 24 / Real.pi ^ 2 :=
  ⟨DihedralBounds.dihedralCoeff_tetra_ge, dihedralCoeff_tetra_le_bracket⟩

end SteklovAudit.DihedralBracket
