import Mathlib
import SteklovAudit.H5GlobalLip
import SteklovAudit.H5TailAudit

/-!
# G89: the rows (2.2) and Lemma 7.1′ do not give `globalVanish`

Roadmap item G89. `pdeD L : Data (Fin 1) (Fin 1)` is one-mode cutoff data with eigenvalues
`a = 1`, `b = 0` and overlap `J = 1 + L`, so its defect is `K = 1 + L`. `pdeD_pde` shows that it
satisfies both fields of `PDEInputs` (the mass row (2.2) and the defect row of Lemma 7.1′) with
`Cm = Ck = 1`, for every `L`. `pdeD_prod` computes the unsplit defect/overlap product
`√(hs2 K * hs2 J) = (1 + L) ^ 2`, and `pdeD_not_vanish` shows that it is not eventually `≤ L`:
the row `globalVanish` of `H5bGlobalLipInputs` (G86, `H5GlobalLip.lean`) fails for this data with
`Λ = 1` and `η = 1`.

F table text: with `Cm = Ck = 1` in `PDEInputs` the unsplit product can be `(1 + L)²`;
`globalVanish` is a separate input, as the docstring of `trace_transfer_naive` says of the
`O(L²)` bound.

What this file does NOT prove: `pdeD` is a one-mode toy family, not the cutoff data of any
operator, so nothing here says whether `globalVanish` holds for the Steklov operator of the
tetrahedron. No field is proved for that operator; no DtN operator is constructed; (7.29) and
Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5GlobalVanishNeeded

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip

/-- One-mode data with eigenvalues `1` and `0` and overlap `1 + L`, so that `K = 1 + L`. -/
noncomputable def pdeD (L : ℝ) : Data (Fin 1) (Fin 1) where
  a := fun _ => 1
  b := fun _ => 0
  J := fun _ _ => 1 + L

/-- **G89.** `pdeD` satisfies the PDE rows (mass and defect) with `Cm = Ck = 1`, for every `L`. -/
theorem pdeD_pde (L : ℝ) : PDEInputs (pdeD L) L 1 1 := by
  constructor
  · rw [SteklovAudit.H5TailAudit.hs2_fin_one]
    show (1 + L) ^ 2 ≤ 1 * (1 + L) ^ 2
    apply le_of_eq
    ring
  · rw [SteklovAudit.H5TailAudit.hs2_fin_one]
    show ((1 - 0) * (1 + L)) ^ 2 ≤ 1 ^ 2 * (1 + L) ^ 2
    apply le_of_eq
    ring

/-- **G89.** The unsplit defect/overlap product of `pdeD` is `(1 + L) ^ 2`. -/
theorem pdeD_prod (L : ℝ) :
    Real.sqrt (hs2 (pdeD L).K * hs2 (pdeD L).J) = (1 + L) ^ 2 := by
  have e : hs2 (pdeD L).K * hs2 (pdeD L).J = ((1 + L) ^ 2) ^ 2 := by
    rw [SteklovAudit.H5TailAudit.hs2_fin_one, SteklovAudit.H5TailAudit.hs2_fin_one]
    show ((1 - 0) * (1 + L)) ^ 2 * (1 + L) ^ 2 = ((1 + L) ^ 2) ^ 2
    ring
  rw [e]
  exact Real.sqrt_sq (sq_nonneg _)

/-- **G89.** The product is not eventually `≤ L`: the row `globalVanish` fails for `pdeD` with
`Λ = 1` and `η = 1`, although the PDE rows hold (`pdeD_pde`). -/
theorem pdeD_not_vanish : ¬ ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    1 * Real.sqrt (hs2 (pdeD L).K * hs2 (pdeD L).J) ≤ 1 * L := by
  intro h
  obtain ⟨L₀, hL⟩ := h
  have h1 := hL (max L₀ 0) (le_max_left _ _)
  rw [pdeD_prod] at h1
  have h0 : (0 : ℝ) ≤ max L₀ 0 := le_max_right _ _
  nlinarith [sq_nonneg (max L₀ 0)]

end SteklovAudit.H5GlobalVanishNeeded
