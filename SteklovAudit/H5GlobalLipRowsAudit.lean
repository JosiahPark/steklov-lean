import Mathlib
import SteklovAudit.H5GlobalLipRows

/-!
# G91: the F2 audit for the linear-scale rows of the H5b inputs

Roadmap item G91. With the cutoff data `D` unconstrained, the linear-scale form
`H5bGlobalLipRows E Emod` (G90, `H5GlobalLipRows.lean`) is equivalent to the target
`H5bTarget E Emod`: one direction is `h5b_of_globalLipRows`; the other is `ofTarget`, which
takes spectral data with zero coefficients over `Fin 0` (`nA = nB = 0`), `F = 0`,
`Λ = m = δ = 0`, and puts the whole comparison into `disc ε γ L := |E ε γ L - Emod ε γ L|`.
As with F2 and G87, the content of the form sits in the `cutoff`/`disc` row; `massLin`,
`defectLin` and `δVanish` carry content only once `D` is the operator's cutoff data.

`globalLipRows_nonempty_zero` is a satisfiability check (non-vacuity): the structure has an
inhabitant for `E = Emod = 0`.

What this file does NOT prove: no field (row) of `H5bGlobalLipRows` is proved for the Steklov
operator of the tetrahedron; whether the paper supplies `massLin` or `defectLin` at the scale `L`
is open; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
This is an audit only.
-/

namespace SteklovAudit.H5GlobalLipRowsAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows

/-- The zero coefficient array has zero Hilbert–Schmidt norm. -/
theorem rowsAudit_hs2_zero {ι κ : Type*} [Fintype ι] [Fintype κ] :
    hs2 (fun (_ : ι) (_ : κ) => (0 : ℝ)) = 0 := by
  first
    | (simp [hs2]; done)
    | (unfold hs2; simp)

/-- **G91.** The target alone gives linear-scale rows (empty data, `F = 0`, `Λ = m = δ = 0`). -/
noncomputable def ofTarget {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    H5bGlobalLipRows E Emod where
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
  m := fun _ _ => 0
  hm := fun _ _ => le_refl _
  massLin := by
    intro ε γ L _
    have h0 := rowsAudit_hs2_zero (ι := Fin 0) (κ := Fin 0)
    first
      | (simp [hs2]; done)
      | (simp only [zero_mul]; exact le_of_eq h0)
      | (unfold hs2; simp)
  δ := fun _ _ _ => 0
  defectLin := by
    intro ε γ L _
    first
      | (simp [hs2, Data.K]; done)
      | (unfold hs2 Data.K; simp)
  δVanish := by
    intro ε γ _ _ η hη
    exact ⟨0, fun _ _ => hη.le⟩

theorem ofTarget_m {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    (ofTarget h).m = fun _ _ => 0 := rfl

/-- **G91 (F2 audit, linear-scale rows).** The linear-scale rows hold exactly when the target
holds. -/
theorem globalLipRows_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bGlobalLipRows E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_globalLipRows H, fun h => ⟨ofTarget h⟩⟩

/-- Satisfiability: an explicit witness with `E = Emod = 0`. -/
theorem globalLipRows_nonempty_zero :
    Nonempty (H5bGlobalLipRows (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ))) := by
  refine (globalLipRows_iff_target _ _).2 ?_
  unfold H5bTarget
  intro ε γ _ _ η hη
  refine ⟨0, fun L hL => ?_⟩
  simp only [sub_self, abs_zero]
  exact mul_nonneg hη.le hL

end SteklovAudit.H5GlobalLipRowsAudit
