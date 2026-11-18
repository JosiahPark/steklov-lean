import Mathlib
import SteklovAudit.H5GlobalLip

/-!
# G88: the global-Lipschitz form (G86) is a special case of G83, not a replacement

Roadmap item G88. `steep_selMin` is an explicit `H5bSelMinInputs` (G83, `H5SelMin.lean`) with
empty cutoff data (`nA = nB = 0`), `E = Emod = 0`, and the test function
`steepF ε γ L x = L * x`, whose Lipschitz constant grows with `L`. `steepF_not_lip` shows that no
single constant `Λ` makes `steepF ε γ L` Lipschitz uniformly in `L`, so the row `lip` of
`H5bGlobalLipInputs` (G86, `H5GlobalLip.lean`) fails for this `F`.

F table text: the G83 rows admit a test `F` that is not Lipschitz uniformly in `L`; G86 needs the
extra input `lip`.

What this file does NOT prove: the witness has empty data, so it says nothing about the operator's
cutoff data or the paper's smoothed counting function; whether that function is Lipschitz uniformly
in `L` remains open (Josiah to say). No field is proved for the Steklov operator of the
tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5GlobalLipStrict

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip

/-- A test function whose Lipschitz constant is `L`. -/
def steepF : ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ L x => L * x

/-- **G88.** G83 inputs (empty data, `E = Emod = 0`) with the steep test function. -/
noncomputable def steep_selMin :
    H5bSelMinInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => ⟨fun _ => 0, fun _ => 0, fun _ _ => 0⟩
  F := steepF
  disc := fun _ _ _ => 0
  cutoff := by
    intro ε γ L
    first
      | (simp; done)
      | (simp only [sub_self, Finset.univ_eq_empty, Finset.sum_empty, abs_zero]; exact le_refl _)
  discVanish := by
    intro ε γ _ _ η hη
    refine ⟨0, fun L hL => ?_⟩
    show (0 : ℝ) ≤ η * L
    exact mul_nonneg hη.le hL
  Λ0 := fun _ _ => 0
  hΛ0 := fun _ _ => le_refl _
  lam := fun _ _ _ _ => 0
  hlam := fun _ _ _ _ => le_refl _
  lipHi := by
    intro ε γ M L i j _
    first
      | exact i.elim0
      | exact (Nat.not_lt_zero _ i.2).elim
      | exact absurd i.isLt (by simp)
  lipLo := by
    intro ε γ M L i j _
    first
      | exact i.elim0
      | exact (Nat.not_lt_zero _ i.2).elim
      | exact absurd i.isLt (by simp)
  directVanish := by
    intro ε γ _ _ η hη
    refine ⟨fun _ => 0, 0, fun L hL => ?_⟩
    have h0 : (0 : ℝ) ≤ η * L := mul_nonneg hη.le hL
    first
      | (simp only [zero_mul, add_zero]; exact h0)
      | simpa using h0

theorem steep_selMin_F : steep_selMin.F = steepF := rfl

/-- **G88.** `steepF` is not Lipschitz uniformly in `L`, for any constant `Λ`. -/
theorem steepF_not_lip : ∀ ε γ Λ : ℝ,
    ¬ ∀ L x y : ℝ, |steepF ε γ L x - steepF ε γ L y| ≤ Λ * |x - y| := by
  intro ε γ Λ h
  have h1 := h (|Λ| + 1) 1 0
  have e1 : steepF ε γ (|Λ| + 1) 1 - steepF ε γ (|Λ| + 1) 0 = |Λ| + 1 := by
    simp only [steepF]
    ring
  have h2 : |steepF ε γ (|Λ| + 1) 1 - steepF ε γ (|Λ| + 1) 0| = |Λ| + 1 := by
    rw [e1]
    exact abs_of_pos (by positivity)
  have h3 : Λ * |(1 : ℝ) - 0| = Λ := by norm_num
  linarith [le_abs_self Λ]

/-- **G88.** Hence the G83 witness `steep_selMin` admits no global Lipschitz row `lip`. -/
theorem steep_selMin_not_lip (Λ : ℝ → ℝ → ℝ) :
    ¬ ∀ ε γ L x y : ℝ,
      |steep_selMin.F ε γ L x - steep_selMin.F ε γ L y| ≤ Λ ε γ * |x - y| :=
  fun h => steepF_not_lip 0 0 (Λ 0 0) (fun L x y => h 0 0 L x y)

end SteklovAudit.H5GlobalLipStrict
