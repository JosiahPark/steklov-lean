import Mathlib
import SteklovAudit.H5Compare

/-!
# G4: the tail and low-energy rows of H5b are genuine inputs

Roadmap item G4.

* `hs2_mask_split`: `hs2 K = hs2 (mask p K) + hs2 (mask (¬p) K)`. So the rows `tail` and
  `lowDefect` of `H5bInputs` together bound exactly the full defect
  (`defect_le_tail_add_low`): they are a split of the HS defect, not extra information about it.
* `counterData`: an explicit one-by-one family (`a = L + 1`, `b = L`, `J = 1 + L`) that satisfies
  `PDEInputs (counterData L) L 1 1` for every real `L` (`counterData_pde`), but whose
  high-energy masked defect is `(1 + L)²` as soon as `M < L + 1` (`counterData_hi_mask`).
* `defect_not_imp_tail`: for this family the high-energy masked defect does not tend to `0`
  uniformly in `L`; `tail_row_fails`: no `τ` bounding it uniformly in `L` can satisfy
  `tailVanish`. Hence `tailVanish` does not follow from `PDEInputs.defect`; the row stays a
  separate named input.

What this file does NOT prove: it proves no row of the F table for the Steklov operator of the
tetrahedron; the counterexample is a toy finite array, not spectral data; (7.29) and
Theorem 1.3 / 11.1 stay conditional.
-/

namespace SteklovAudit.H5TailAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- **G4.** The HS norm splits along any mask and its complement. -/
theorem hs2_mask_split {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → κ → Prop)
    [∀ i j, Decidable (p i j)] (K : ι → κ → ℝ) :
    hs2 K = hs2 (mask p K) + hs2 (mask (fun i j => ¬ p i j) K) := by
  dsimp only [hs2, mask]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : p i j
  · rw [if_pos h, if_neg (not_not.mpr h)]
    ring
  · rw [if_neg h, if_pos h]
    ring

/-- **G4.** `tail` and `lowDefect` together bound exactly the full defect. -/
theorem defect_le_tail_add_low {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod)
    (ε γ M L : ℝ) : hs2 (H.D ε γ L).K ≤ H.τ ε γ M + H.κ2 ε γ M := by
  have s := hs2_mask_split (hiE (H.D ε γ L) M) (H.D ε γ L).K
  have t := H.tail ε γ M L
  have l := H.lowDefect ε γ M L
  linarith

/-- On `Fin 1 × Fin 1` the HS norm is the square of the single entry. -/
theorem hs2_fin_one (M : Fin 1 → Fin 1 → ℝ) : hs2 M = M 0 0 ^ 2 := by
  first
  | simp only [hs2, Fin.sum_univ_one]
  | simp [hs2]

/-- The toy family: energies `L + 1` and `L`, coupling `1 + L`. -/
noncomputable def counterData (L : ℝ) : Data (Fin 1) (Fin 1) where
  a := fun _ => L + 1
  b := fun _ => L
  J := fun _ _ => 1 + L

/-- The toy family satisfies the PDE inputs (mass and defect) with `Cm = Ck = 1`, every `L`. -/
theorem counterData_pde (L : ℝ) : PDEInputs (counterData L) L 1 1 := by
  constructor
  · rw [hs2_fin_one]
    show (1 + L) ^ 2 ≤ 1 * (1 + L) ^ 2
    apply le_of_eq
    ring
  · rw [hs2_fin_one]
    show ((L + 1 - L) * (1 + L)) ^ 2 ≤ 1 ^ 2 * (1 + L) ^ 2
    apply le_of_eq
    ring

/-- Above the split energy the masked defect of the toy family is `(1 + L)²`. -/
theorem counterData_hi_mask (M L : ℝ) (h : M < L + 1) :
    hs2 (mask (hiE (counterData L) M) (counterData L).K) = (1 + L) ^ 2 := by
  rw [hs2_fin_one]
  have hh : hiE (counterData L) M 0 0 := by
    show M < max (L + 1) L
    exact lt_of_lt_of_le h (le_max_left _ _)
  dsimp only [mask]
  rw [if_pos hh]
  show ((L + 1 - L) * (1 + L)) ^ 2 = (1 + L) ^ 2
  ring

/-- **G4.** `PDEInputs` for every `L` does not force the high-energy masked defect to vanish
uniformly in `L`. -/
theorem defect_not_imp_tail :
    (∀ L : ℝ, PDEInputs (counterData L) L 1 1) ∧
    ¬ (∀ δ : ℝ, 0 < δ → ∃ M : ℝ, ∀ L : ℝ,
        hs2 (mask (hiE (counterData L) M) (counterData L).K) ≤ δ) := by
  refine ⟨counterData_pde, fun h => ?_⟩
  obtain ⟨M, hM⟩ := h 1 one_pos
  have h0 := abs_nonneg M
  have hL : M < (|M| + 1) + 1 := by
    have := le_abs_self M
    linarith
  have e := counterData_hi_mask M (|M| + 1) hL
  have b := hM (|M| + 1)
  rw [e] at b
  nlinarith [sq_nonneg (|M|)]

/-- **G4.** For the toy family, no `τ` bounding the tail uniformly in `L` satisfies
`tailVanish`: the `tail`/`tailVanish` row is not implied by the `pde` row. -/
theorem tail_row_fails (τ : ℝ → ℝ)
    (htail : ∀ M L : ℝ, hs2 (mask (hiE (counterData L) M) (counterData L).K) ≤ τ M) :
    ¬ (∀ δ : ℝ, 0 < δ → ∃ M, τ M ≤ δ) := by
  intro hv
  apply defect_not_imp_tail.2
  intro δ hδ
  obtain ⟨M, hM⟩ := hv δ hδ
  exact ⟨M, fun L => le_trans (htail M L) hM⟩

end SteklovAudit.H5TailAudit
