import Mathlib
import SteklovAudit.H5JointSelAudit
import SteklovAudit.H5JointIff

/-!
# G79: the F2 audit for the selector form of the H5b inputs

Roadmap item G79. With the cutoff data `D` unconstrained, the selector form
`H5bJointSelInputs E Emod` (G77, `H5JointSel.lean`) is equivalent to the target
`H5bTarget E Emod`: one direction is `h5b_of_jointSelInputs`, the other composes
`H5JointIff.jointOfTarget` (G75) with `H5JointSelAudit.ofJoint` (G78). The caveat therefore
sits in the `cutoff`/`disc` row, exactly as for F1, G72 and G75.

`selInputs_nonempty_zero` is a satisfiability check (non-vacuity): the structure has an
inhabitant for `E = Emod = 0`.

What this file does NOT prove: no field (row) of `H5bJointSelInputs` is proved for the Steklov
operator of the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1
remain conditional. This is an audit only.
-/

namespace SteklovAudit.H5JointSelIff

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
  SteklovAudit.H5Joint SteklovAudit.H5JointSel

/-- **G79 (F2 audit, selector form).** The selector inputs hold exactly when the target holds. -/
theorem selInputs_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bJointSelInputs E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_jointSelInputs H,
   fun h => ⟨H5JointSelAudit.ofJoint (H5JointIff.jointOfTarget h)⟩⟩

/-- Satisfiability: an explicit witness with `E = Emod = 0`. -/
theorem selInputs_nonempty_zero :
    Nonempty (H5bJointSelInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ))) := by
  refine (selInputs_iff_target _ _).2 ?_
  unfold H5bTarget
  intro ε γ _ _ η hη
  refine ⟨0, fun L hL => ?_⟩
  simp only [sub_self, abs_zero]
  exact mul_nonneg hη.le hL

end SteklovAudit.H5JointSelIff
