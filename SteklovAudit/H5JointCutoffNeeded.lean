import Mathlib
import SteklovAudit.H5Compare

/-!
# G76: the `cutoff` row is the only link from the H5b rows to `E`

Roadmap item G76. With `E = L²` and `Emod = 0` the target `H5bTarget` fails
(`sq_target_fails`), while the vanishing condition of the joint row (G72, `jointVanish`)
holds when every row function (`Λ0`, `τ`, `mHi`, `lam`, `κ2`, `mLo`) is zero
(`zero_rows_hold`). So the rows other than `cutoff`/`disc` carry no information about
`E − Emod`: they constrain `E` only through the `cutoff` row.

F table text: all rows except `cutoff`/`disc` can hold with zero functions while `E − Emod`
grows like `L²`, so they constrain `E` only through `cutoff`.

What this file does NOT prove: no row of `H5bJointInputs` is proved for the Steklov operator
of the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain
conditional. This is an audit of the row shapes only.
-/

namespace SteklovAudit.H5JointCutoffNeeded

open SteklovAudit SteklovAudit.H5Compare

/-- `E − Emod = L²` violates the target `|E − Emod| = o(L)`. -/
theorem sq_target_fails : ¬ H5bTarget (fun _ _ L => L ^ 2) (fun _ _ _ => 0) := by
  intro h
  unfold H5bTarget at h
  obtain ⟨L₀, hL₀⟩ := h 1 1 one_pos one_pos 1 one_pos
  have hx : (2 : ℝ) ≤ max L₀ 2 := le_max_right _ _
  have h1 : |(max L₀ 2) ^ 2 - 0| ≤ 1 * max L₀ 2 := hL₀ _ (le_max_left _ _)
  rw [sub_zero, one_mul, abs_of_nonneg (sq_nonneg _)] at h1
  have h2 : 2 * max L₀ 2 ≤ max L₀ 2 * max L₀ 2 :=
    mul_le_mul_of_nonneg_right hx (by linarith)
  nlinarith

/-- The joint vanishing row holds when all row functions are zero. -/
theorem zero_rows_hold : ∀ η : ℝ, 0 < η → ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L →
    (0 : ℝ) * Real.sqrt (0 * 0) + 0 * Real.sqrt (0 * 0) ≤ η * L := by
  intro η hη
  refine ⟨0, 0, fun L hL => ?_⟩
  have h0 : (0 : ℝ) ≤ η * L := mul_nonneg hη.le hL
  simp only [zero_mul, add_zero]
  exact h0

/-- **G76.** The zero rows hold while the target fails for `E − Emod = L²`. -/
theorem cutoff_row_needed :
    ¬ H5bTarget (fun _ _ L => L ^ 2) (fun _ _ _ => 0) ∧
    (∀ η : ℝ, 0 < η → ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L →
      (0 : ℝ) * Real.sqrt (0 * 0) + 0 * Real.sqrt (0 * 0) ≤ η * L) :=
  ⟨sq_target_fails, zero_rows_hold⟩

end SteklovAudit.H5JointCutoffNeeded
