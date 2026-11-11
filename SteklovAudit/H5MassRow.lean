import Mathlib
import SteklovAudit.H5Compare

/-!
# G12: the mass row (2.2) from a Bessel bound plus a Weyl count

Roadmap item G12. The `mass` field of `PDEInputs` (`hs2 D.J ≤ Cm * (1 + L) ^ 2`) follows from two
statements that each mention only one ingredient:

* a Bessel bound: every row of `J` has squared norm at most `1` (`∀ i, ∑ j, J i j ^ 2 ≤ 1`), which
  holds when `J` is the matrix of a contraction between orthonormal families;
* a Weyl count: the number of eigenvalues below the cutoff is `O(L²)`
  (`(Fintype.card ι : ℝ) ≤ Cw * (1 + L) ^ 2`).

Declarations: `sum_one_eq_card`, `mass_of_bessel_count`, `pde_of_bessel_count`, the witness `idJ`
(identity matrix on `Fin 2`) with `idJ_row`, `idJ_hs2`, and `bessel_count_nonjunk` (both
hypotheses hold for a witness with nonzero mass, so they are not vacuous).

What this file does NOT prove: it proves neither the Bessel bound nor the Weyl count for the
Steklov operator of the tetrahedron, constructs no Dirichlet-to-Neumann operator, does not touch
the defect row of `PDEInputs`, and leaves (7.29) and Theorem 1.3 / 11.1 conditional on the
named inputs.
-/

namespace SteklovAudit.H5MassRow

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Summing `1` over a finite type gives its cardinality. -/
theorem sum_one_eq_card : ∑ _i : ι, (1 : ℝ) = (Fintype.card ι : ℝ) := by
  first
  | simp
  | rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **G12.** Bessel bound on the rows plus a Weyl count gives the mass bound. -/
theorem mass_of_bessel_count (J : ι → κ → ℝ) (L Cw : ℝ)
    (hrow : ∀ i, ∑ j, J i j ^ 2 ≤ 1) (hcount : (Fintype.card ι : ℝ) ≤ Cw * (1 + L) ^ 2) :
    hs2 J ≤ Cw * (1 + L) ^ 2 := by
  have h1 : hs2 J ≤ ∑ _i : ι, (1 : ℝ) := by
    unfold hs2
    exact Finset.sum_le_sum (fun i _ => hrow i)
  have h2 := (sum_one_eq_card (ι := ι))
  linarith

/-- **G12.** The same, together with a defect bound, gives the full `PDEInputs`. -/
theorem pde_of_bessel_count (D : Data ι κ) (L Cw Ck : ℝ)
    (hrow : ∀ i, ∑ j, D.J i j ^ 2 ≤ 1) (hcount : (Fintype.card ι : ℝ) ≤ Cw * (1 + L) ^ 2)
    (hdef : hs2 D.K ≤ Ck ^ 2 * (1 + L) ^ 2) : PDEInputs D L Cw Ck :=
  ⟨mass_of_bessel_count D.J L Cw hrow hcount, hdef⟩

/-- The witness: the identity matrix on `Fin 2`. -/
noncomputable def idJ : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1 else 0

/-- Each row of `idJ` has squared norm `1`. -/
theorem idJ_row (i : Fin 2) : ∑ j, idJ i j ^ 2 = 1 := by
  first
  | (fin_cases i <;> simp [idJ, Fin.sum_univ_two])
  | (fin_cases i <;> norm_num [idJ, Fin.sum_univ_two])

/-- The mass of `idJ` is `2` (nonzero). -/
theorem idJ_hs2 : hs2 idJ = 2 := by
  first
  | norm_num [hs2, idJ, Fin.sum_univ_two]
  | (simp [hs2, idJ, Fin.sum_univ_two]; norm_num)

/-- **G12.** Non-vacuity: for every `L ≥ 0` the witness satisfies the Bessel bound and the Weyl
count with `Cw = 2`, and its mass is nonzero, so the hypotheses are not met only by `J = 0`. -/
theorem bessel_count_nonjunk (L : ℝ) (hL : 0 ≤ L) :
    (∀ i, ∑ j, idJ i j ^ 2 ≤ 1) ∧ ((Fintype.card (Fin 2) : ℝ) ≤ 2 * (1 + L) ^ 2) ∧
      hs2 idJ = 2 ∧ hs2 idJ ≤ 2 * (1 + L) ^ 2 := by
  have hc : ((Fintype.card (Fin 2) : ℕ) : ℝ) = 2 := by
    first
    | simp
    | (rw [Fintype.card_fin]; norm_num)
  refine ⟨fun i => le_of_eq (idJ_row i), ?_, idJ_hs2, ?_⟩
  · rw [hc]
    nlinarith [sq_nonneg L]
  · rw [idJ_hs2]
    nlinarith [sq_nonneg L]

end SteklovAudit.H5MassRow
