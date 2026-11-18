import Mathlib
import SteklovAudit.H5SelMin

/-!
# G84: the G83 inputs are strictly weaker than the G80 inputs on the data level

Roadmap item G84. `bigD L : Data (Fin 1) (Fin 1)` has `a = b = 0` and overlap
`J = (1 + |L|) ^ 2`, so its defect `K` vanishes (`bigD_K`). With `E = Emod = 0`, cutoff data
`D _ _ L := bigD L`, `F = 0`, `disc = 0`, `Λ0 = lam = 0`, every row of `H5bSelMinInputs` holds
(`bigD_selMin`), yet at every constant `Cm` the overlap mass violates the mass row (2.2) of
`PDEInputs` (`bigD_not_pde`). So an instance of the G83 rows need not satisfy the PDE rows of G80
(`selMin_without_pde`).

F table text: an instance of the G83 rows whose overlap mass violates (2.2) at every constant.

What this file does NOT prove: nothing about the Steklov operator of the tetrahedron; no DtN
operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional. The example has
`E = Emod = 0`, so it says nothing about whether the actual comparison holds; it only shows that
the PDE rows are not implied by the remaining G83 rows.
-/

namespace SteklovAudit.H5SelMinStrict

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin

/-- One-mode data with zero eigenvalues and overlap `(1 + |L|) ^ 2`. -/
noncomputable def bigD (L : ℝ) : Data (Fin 1) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => (1 + |L|) ^ 2

theorem bigD_K (L : ℝ) (i j : Fin 1) : (bigD L).K i j = 0 := by
  simp [Data.K, bigD]

/-- **G84.** The G83 rows hold for `bigD` with `E = Emod = 0`. -/
noncomputable def bigD_selMin : H5bSelMinInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0) where
  nA := fun _ _ _ => 1
  nB := fun _ _ _ => 1
  D := fun _ _ L => bigD L
  F := fun _ _ _ _ => 0
  disc := fun _ _ _ => 0
  cutoff := by
    intro ε γ L
    simp
  discVanish := by
    intro ε γ _ _ η hη
    exact ⟨0, fun L hL => by
      show (0 : ℝ) ≤ η * L
      exact mul_nonneg hη.le hL⟩
  Λ0 := fun _ _ => 0
  hΛ0 := fun _ _ => le_rfl
  lam := fun _ _ _ _ => 0
  hlam := fun _ _ _ _ => le_rfl
  lipHi := by
    intros
    simp
  lipLo := by
    intros
    simp
  directVanish := by
    intro ε γ _ _ η hη
    refine ⟨fun _ => 0, 0, fun L hL => ?_⟩
    have h0 : 0 ≤ η * L := mul_nonneg hη.le hL
    first
      | (show (0 : ℝ) * Real.sqrt _ + 0 * Real.sqrt _ ≤ η * L
         rw [zero_mul, zero_mul, add_zero]
         exact h0)
      | simpa using h0

theorem bigD_selMin_target : H5bTarget (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0) :=
  h5b_of_selMinInputs bigD_selMin

theorem hs2_bigD_J (L : ℝ) : hs2 (bigD L).J = (1 + |L|) ^ 4 := by
  first
    | (show ∑ i : Fin 1, ∑ j : Fin 1, ((1 + |L|) ^ 2) ^ 2 = _
       rw [Fin.sum_univ_one, Fin.sum_univ_one]
       ring)
    | (simp [hs2, bigD]; ring)
    | simp [hs2, bigD]

/-- **G84.** The mass row (2.2) fails for `bigD |Cm|` at every constant. -/
theorem bigD_not_pde : ∀ Cm Ck : ℝ, ¬ PDEInputs (bigD |Cm|) |Cm| Cm Ck := by
  intro Cm Ck h
  have hm := h.mass
  rw [hs2_bigD_J, abs_abs] at hm
  have hle := le_abs_self Cm
  have ha := abs_nonneg Cm
  have hp : 0 < (1 + |Cm|) ^ 2 := by positivity
  have h1 : Cm * (1 + |Cm|) ^ 2 ≤ |Cm| * (1 + |Cm|) ^ 2 :=
    mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  have hlt : |Cm| < (1 + |Cm|) ^ 2 := by nlinarith [sq_nonneg |Cm|]
  have h2 : |Cm| * (1 + |Cm|) ^ 2 < (1 + |Cm|) ^ 2 * (1 + |Cm|) ^ 2 :=
    mul_lt_mul_of_pos_right hlt hp
  have h3 : (1 + |Cm|) ^ 2 * (1 + |Cm|) ^ 2 = (1 + |Cm|) ^ 4 := by ring
  linarith

/-- **G84.** Some G83 instance has cutoff data violating the PDE rows at every constant. -/
theorem selMin_without_pde :
    ∃ H : H5bSelMinInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0),
      ∀ Cm Ck : ℝ, ¬ PDEInputs (H.D 0 0 |Cm|) |Cm| Cm Ck :=
  ⟨bigD_selMin, fun Cm Ck => bigD_not_pde Cm Ck⟩

end SteklovAudit.H5SelMinStrict
