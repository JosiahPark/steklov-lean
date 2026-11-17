import Mathlib
import SteklovAudit.H5Joint

/-!
# G75: the F2 audit for the joint form of the H5b inputs

Roadmap item G75. `jointOfTarget` builds `H5bJointInputs E Emod` from the target
`H5bTarget E Emod` alone: empty cutoff data (`H5Compare.emptyData`), `disc = |E − Emod|`, and
every other function zero, exactly as `H5Compare.inputsOfTarget` does for `H5bInputs`.
Together with `h5b_of_jointInputs` this gives `jointInputs_iff_target`.

F table text: with the cutoff data `D` unconstrained, the joint form, like F1, is equivalent
to the target; the caveat sits in the `cutoff`/`disc` row.

What this file does NOT prove: no field (row) of `H5bJointInputs` is proved for the Steklov
operator of the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1
remain conditional. This is an audit showing that the joint form, like F1, carries content
only through the paper review of the `cutoff` row with `D` the actual spectral data.
-/

namespace SteklovAudit.H5JointIff

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5Joint

/-- From the target alone: empty cutoff, `disc = |E − Emod|`, all other inputs zero. -/
noncomputable def jointOfTarget {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    H5bJointInputs E Emod where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => emptyData
  F := fun _ _ _ _ => 0
  disc := fun ε γ L => |E ε γ L - Emod ε γ L|
  cutoff := by intro ε γ L; simp
  discVanish := fun ε γ hε hγ η hη => h ε γ hε hγ η hη
  Cm := fun _ _ => 0
  Ck := fun _ _ => 0
  hCm := fun _ _ => le_refl 0
  pde := fun _ _ _ => ⟨by simp [hs2], by simp [hs2]⟩
  τ := fun _ _ _ _ => 0
  tail := by intro ε γ M L _; simp [hs2]
  mHi := fun _ _ _ _ => 0
  hiMass := by intro ε γ M L; simp [hs2]
  κ2 := fun _ _ _ _ => 0
  lowDefect := by intro ε γ M L; simp [hs2]
  mLo := fun _ _ _ _ => 0
  lowMass := by intro ε γ M L; simp [hs2]
  Λ0 := fun _ _ => 0
  hΛ0 := fun _ _ => le_refl 0
  lam := fun _ _ _ _ => 0
  hlam := fun _ _ _ _ => le_refl 0
  lipHi := fun _ _ _ _ i => Fin.elim0 i
  lipLo := fun _ _ _ _ i => Fin.elim0 i
  jointVanish := fun _ _ _ _ η hη => ⟨0, 0, fun L hL => by
    show (0 : ℝ) * Real.sqrt (0 * 0) + 0 * Real.sqrt (0 * 0) ≤ η * L
    have h0 : (0 : ℝ) ≤ η * L := mul_nonneg hη.le hL
    simp only [zero_mul, add_zero]
    exact h0⟩

/-- **G75 (F2 audit, joint form).** The joint inputs hold exactly when the target holds. -/
theorem jointInputs_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bJointInputs E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_jointInputs H, fun h => ⟨jointOfTarget h⟩⟩

/-- Satisfiability: an explicit witness, `E = Emod`. -/
theorem jointInputs_nonempty (E : ℝ → ℝ → ℝ → ℝ) : Nonempty (H5bJointInputs E E) := by
  refine ⟨jointOfTarget ?_⟩
  unfold H5bTarget
  intro ε γ _ _ η hη
  refine ⟨0, fun L hL => ?_⟩
  rw [sub_self, abs_zero]
  exact mul_nonneg hη.le hL

end SteklovAudit.H5JointIff
