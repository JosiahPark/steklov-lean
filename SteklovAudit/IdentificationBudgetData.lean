import Mathlib
import SteklovAudit.SpectralCounting

/-!
# E13: identification budget in `AbstractTransfer.Data` coordinates (continuation 29)

Roadmap item E13, a companion to E7 (`IdentificationBudget.lean`, stated for matrices): the same
budget for `AbstractTransfer.Data`, plus an explicit example where the signed trace cancels. In the spectral coordinates of `AbstractTransfer` (`J : B-space → A-space` with
coefficients `J i j`, `P_A = 1_{A ≤ L}`, `P_B = 1_{B ≤ L}`), continuation 29 bounds
`|N_B − N_A| ≤ ‖P_B − J* P_A J‖₁ + |Tr P_A (I − J J*)|`. Proved here, without trace norms:

* `budget_identity` (exact): `N_B(L) − N_A(L) = Σ_j (1_{b_j ≤ L} − (J* P_A J)_{jj})
  − Σ_{a_i ≤ L} (1 − ‖J* e_i‖²)`, where `(J* P_A J)_{jj} = Σ_{a_i ≤ L} J_{ij}²` and
  `‖J* e_i‖² = Σ_j J_{ij}²`;
* `budget_bound`: `|N_B − N_A| ≤ Σ_j |1_{b_j ≤ L} − (J* P_A J)_{jj}| + Σ_{a_i ≤ L} |1 − ‖J* e_i‖²|`.
  The first sum is the diagonal part of `‖P_B − J* P_A J‖₁` and is at most it;
* `defect_terms_nonneg`: if every row of `J` has norm `≤ 1` (a contraction), each diagonal defect
  `1 − ‖J* e_i‖²` is `≥ 0`, so the signed sum equals the absolute sum and nothing cancels;
* `signed_trace_cancels`: without that, the signed trace can vanish while the diagonal defect is
  `2` (rows of squared norm `2` and `0`). So the budget must use the diagonal form
  `Σ_{a_i ≤ L} |1 − ‖J* e_i‖²|`, not `|Tr P_A (I − J J*)|`.

What this file does NOT prove: anything about the Steklov operator or a bound on these terms for
the tetrahedron; trace norms are not used. It does not prove the main theorem.
-/

namespace SteklovAudit.AbstractTransfer

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- E13. Exact identification identity at threshold `L`. -/
theorem budget_identity (D : Data ι κ) (L : ℝ) :
    (count D.b L : ℝ) - count D.a L =
      ∑ j, ((if D.b j ≤ L then (1 : ℝ) else 0)
          - ∑ i ∈ univ.filter (fun i => D.a i ≤ L), D.J i j ^ 2)
        - ∑ i ∈ univ.filter (fun i => D.a i ≤ L), (1 - ∑ j, D.J i j ^ 2) := by
  have hB : (count D.b L : ℝ) = ∑ j, (if D.b j ≤ L then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
    rfl
  have hA : (count D.a L : ℝ) = ∑ i ∈ univ.filter (fun i => D.a i ≤ L), (1 : ℝ) := by
    unfold count
    rw [sum_const, nsmul_eq_mul, mul_one]
  have hc : ∑ j, ∑ i ∈ univ.filter (fun i => D.a i ≤ L), D.J i j ^ 2 =
      ∑ i ∈ univ.filter (fun i => D.a i ≤ L), ∑ j, D.J i j ^ 2 := Finset.sum_comm
  rw [sum_sub_distrib, sum_sub_distrib, hc, hA, hB]
  ring

/-- E13. The identification budget in diagonal form. -/
theorem budget_bound (D : Data ι κ) (L : ℝ) :
    |(count D.b L : ℝ) - count D.a L| ≤
      ∑ j, |(if D.b j ≤ L then (1 : ℝ) else 0)
          - ∑ i ∈ univ.filter (fun i => D.a i ≤ L), D.J i j ^ 2|
        + ∑ i ∈ univ.filter (fun i => D.a i ≤ L), |1 - ∑ j, D.J i j ^ 2| := by
  have key : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    have h := abs_add_le x (-y)
    rwa [abs_neg, ← sub_eq_add_neg] at h
  rw [budget_identity]
  refine le_trans (key _ _) (add_le_add ?_ ?_)
  · exact Finset.abs_sum_le_sum_abs _ _
  · exact Finset.abs_sum_le_sum_abs _ _

/-- For a contraction (rows of norm `≤ 1`) the diagonal defects are nonnegative, so the signed
defect sum equals the absolute one. -/
theorem defect_terms_nonneg (D : Data ι κ) (L : ℝ) (hrow : ∀ i, ∑ j, D.J i j ^ 2 ≤ 1) :
    ∑ i ∈ univ.filter (fun i => D.a i ≤ L), |1 - ∑ j, D.J i j ^ 2| =
      ∑ i ∈ univ.filter (fun i => D.a i ≤ L), (1 - ∑ j, D.J i j ^ 2) := by
  apply sum_congr rfl
  intro i _
  exact abs_of_nonneg (by linarith [hrow i])

/-- Without the contraction property the signed trace can cancel: rows `(1, 1)` and `(0, 0)` (squared
norms `2` and `0`) give signed defect `0` but absolute defect `2`. -/
theorem signed_trace_cancels :
    ∃ D : Data (Fin 2) (Fin 2),
      ∑ i, (1 - ∑ j, D.J i j ^ 2) = 0 ∧ ∑ i, |1 - ∑ j, D.J i j ^ 2| = 2 := by
  refine ⟨⟨fun _ => 0, fun _ => 0, fun i _ => if i = 0 then 1 else 0⟩, ?_, ?_⟩
  · norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]

end SteklovAudit.AbstractTransfer
