import Mathlib
import SteklovAudit.H5GlobalLip

/-!
# G87: the F2 audit for the global-Lipschitz form of the H5b inputs

Roadmap item G87. With the cutoff data `D` unconstrained, the global-Lipschitz form
`H5bGlobalLipInputs E Emod` (G86, `H5GlobalLip.lean`) is equivalent to the target
`H5bTarget E Emod`: one direction is `h5b_of_globalLipInputs`; the other is `ofTarget`, which
takes empty spectral data (`nA = nB = 0`), `F = 0`, `Λ = 0` and puts the whole comparison into
`disc ε γ L := |E ε γ L - Emod ε γ L|`. As with F2, G72, G77 and G82, the content of the
global-Lipschitz form sits in the `cutoff`/`disc` row; `lip` and `globalVanish` carry content
only once `D` is the operator's cutoff data.

`globalLip_nonempty_zero` is a satisfiability check (non-vacuity): the structure has an
inhabitant for `E = Emod = 0`.

What this file does NOT prove: no field (row) of `H5bGlobalLipInputs` is proved for the Steklov
operator of the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1
remain conditional. This is an audit only.
-/

namespace SteklovAudit.H5GlobalLipAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5GlobalLip

/-- **G87.** The target alone gives global-Lipschitz inputs (empty data, `F = 0`, `Λ = 0`). -/
noncomputable def ofTarget {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    H5bGlobalLipInputs E Emod where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => ⟨fun _ => 0, fun _ => 0, fun _ _ => 0⟩
  F := fun _ _ _ _ => 0
  disc := fun ε γ L => |E ε γ L - Emod ε γ L|
  cutoff := by
    intro ε γ L
    first
      | (simp; done)
      | (simp only [sub_self, zero_mul, Finset.sum_const_zero, sub_zero]; exact le_refl _)
  discVanish := h
  Λ := fun _ _ => 0
  hΛ := fun _ _ => le_refl _
  lip := by
    intro ε γ L x y
    simp
  globalVanish := by
    intro ε γ _ _ η hη
    refine ⟨0, fun L hL => ?_⟩
    have h0 : (0 : ℝ) ≤ η * L := mul_nonneg hη.le hL
    first
      | (simp only [zero_mul]; exact h0)
      | simpa using h0

theorem ofTarget_Λ {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    (ofTarget h).Λ = fun _ _ => 0 := rfl

/-- **G87 (F2 audit, global-Lipschitz form).** The global-Lipschitz inputs hold exactly when the
target holds. -/
theorem globalLip_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bGlobalLipInputs E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_globalLipInputs H, fun h => ⟨ofTarget h⟩⟩

/-- Satisfiability: an explicit witness with `E = Emod = 0`. -/
theorem globalLip_nonempty_zero :
    Nonempty (H5bGlobalLipInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ))) := by
  refine (globalLip_iff_target _ _).2 ?_
  unfold H5bTarget
  intro ε γ _ _ η hη
  refine ⟨0, fun L hL => ?_⟩
  simp only [sub_self, abs_zero]
  exact mul_nonneg hη.le hL

end SteklovAudit.H5GlobalLipAudit
