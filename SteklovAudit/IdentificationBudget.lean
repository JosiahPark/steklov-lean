import Mathlib
import SteklovAudit.SpectralCounting

/-!
# E7: identification budget in coordinates (continuation 29)

Roadmap item E7. Let `A`, `B` have spectral data `a : ι → ℝ`, `b : κ → ℝ` (finite cutoff), let
`J : Matrix κ ι ℝ` be the identification written in the two eigenbases, and let
`P_A = 1_{A ≤ L}`, `P_B = 1_{B ≤ L}` be the diagonal spectral projections (`proj`). Proved:

* `trace_proj`: `Tr P_A = N_A(L)` (`AbstractTransfer.count`);
* `trace_JPJt`: `Tr(J P_A Jᵀ) = Σ_{a_i ≤ L} ‖J e_i‖²`;
* `identification_identity` (exact): `N_B − N_A = Tr(P_B − J P_A Jᵀ) − Σ_{a_i ≤ L} (1 − ‖J e_i‖²)`;
* `identification_budget_coords`:
  `|N_B − N_A| ≤ |Tr(P_B − J P_A Jᵀ)| + Σ_{a_i ≤ L} |1 − ‖J e_i‖²|`;
* `identification_budget_contraction`: if every column has `‖J e_i‖ ≤ 1`, the last sum is the
  diagonal defect `Σ_{a_i ≤ L} (1 − ‖J e_i‖²) ≥ 0`, with no absolute values.

Note: the signed trace `Tr P_A(I − JᵀJ)` equals `Σ_{a_i ≤ L} (1 − ‖J e_i‖²)`, whose terms can
cancel when some columns have norm `> 1`; the budget therefore uses the termwise absolute values,
or the column-contraction hypothesis. The trace-norm form `‖P_B − J P_A Jᵀ‖₁` of continuation 29
is not formalized; `|Tr X| ≤ ‖X‖₁` would give it.

What this file does NOT prove: anything about the Steklov operator, the identification for the
tetrahedron, or the main theorem.
-/

namespace SteklovAudit.IdentificationBudget

open Finset SteklovAudit.AbstractTransfer

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Diagonal spectral projection `1_{e ≤ L}`. -/
noncomputable def proj {τ : Type*} [Fintype τ] [DecidableEq τ] (e : τ → ℝ) (L : ℝ) :
    Matrix τ τ ℝ :=
  Matrix.diagonal (fun t => if e t ≤ L then (1 : ℝ) else 0)

theorem trace_proj {τ : Type*} [Fintype τ] [DecidableEq τ] (e : τ → ℝ) (L : ℝ) :
    Matrix.trace (proj e L) = (count e L : ℝ) := by
  unfold proj count
  rw [Matrix.trace_diagonal]
  first | simp [Finset.sum_boole] | rw [Finset.sum_boole]

theorem trace_JPJt (J : Matrix κ ι ℝ) (a : ι → ℝ) (L : ℝ) :
    Matrix.trace (J * proj a L * J.transpose) =
      ∑ i ∈ univ.filter (fun i => a i ≤ L), ∑ j, J j i ^ 2 := by
  have h1 : Matrix.trace (J * proj a L * J.transpose) =
      ∑ j, ∑ i, (if a i ≤ L then (1 : ℝ) else 0) * J j i ^ 2 := by
    unfold Matrix.trace
    refine sum_congr rfl (fun j _ => ?_)
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine sum_congr rfl (fun i _ => ?_)
    unfold proj
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    ring
  rw [h1]
  conv_lhs => rw [Finset.sum_comm]
  rw [sum_filter]
  refine sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

/-- Exact identification identity. -/
theorem identification_identity (J : Matrix κ ι ℝ) (a : ι → ℝ) (b : κ → ℝ) (L : ℝ) :
    (count b L : ℝ) - count a L =
      Matrix.trace (proj b L - J * proj a L * J.transpose)
        - ∑ i ∈ univ.filter (fun i => a i ≤ L), (1 - ∑ j, J j i ^ 2) := by
  rw [Matrix.trace_sub, trace_proj, trace_JPJt, sum_sub_distrib, sum_const, nsmul_eq_mul,
    mul_one]
  unfold count
  ring

/-- Identification budget with termwise defects. -/
theorem identification_budget_coords (J : Matrix κ ι ℝ) (a : ι → ℝ) (b : κ → ℝ) (L : ℝ) :
    |(count b L : ℝ) - count a L| ≤
      |Matrix.trace (proj b L - J * proj a L * J.transpose)|
        + ∑ i ∈ univ.filter (fun i => a i ≤ L), |1 - ∑ j, J j i ^ 2| := by
  have hS : |∑ i ∈ univ.filter (fun i => a i ≤ L), (1 - ∑ j, J j i ^ 2)| ≤
      ∑ i ∈ univ.filter (fun i => a i ≤ L), |1 - ∑ j, J j i ^ 2| :=
    Finset.abs_sum_le_sum_abs _ _
  rw [identification_identity]
  have hT1 := le_abs_self (Matrix.trace (proj b L - J * proj a L * J.transpose))
  have hT2 := neg_abs_le (Matrix.trace (proj b L - J * proj a L * J.transpose))
  have hS1 := le_abs_self (∑ i ∈ univ.filter (fun i => a i ≤ L), (1 - ∑ j, J j i ^ 2))
  have hS2 := neg_abs_le (∑ i ∈ univ.filter (fun i => a i ≤ L), (1 - ∑ j, J j i ^ 2))
  rw [abs_le]
  constructor <;> linarith

/-- With column contractions `‖J e_i‖ ≤ 1` the defect is the nonnegative diagonal sum. -/
theorem identification_budget_contraction (J : Matrix κ ι ℝ) (a : ι → ℝ) (b : κ → ℝ) (L : ℝ)
    (hcol : ∀ i, ∑ j, J j i ^ 2 ≤ 1) :
    |(count b L : ℝ) - count a L| ≤
      |Matrix.trace (proj b L - J * proj a L * J.transpose)|
        + ∑ i ∈ univ.filter (fun i => a i ≤ L), (1 - ∑ j, J j i ^ 2) ∧
    0 ≤ ∑ i ∈ univ.filter (fun i => a i ≤ L), (1 - ∑ j, J j i ^ 2) := by
  have he : ∑ i ∈ univ.filter (fun i => a i ≤ L), |1 - ∑ j, J j i ^ 2| =
      ∑ i ∈ univ.filter (fun i => a i ≤ L), (1 - ∑ j, J j i ^ 2) :=
    sum_congr rfl (fun i _ => abs_of_nonneg (sub_nonneg.mpr (hcol i)))
  refine ⟨?_, sum_nonneg (fun i _ => sub_nonneg.mpr (hcol i))⟩
  rw [← he]
  exact identification_budget_coords J a b L

end SteklovAudit.IdentificationBudget
