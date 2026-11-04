import Mathlib
import SteklovAudit.IdentificationBudget

/-!
# E10: trace-norm form of the identification budget (continuation 29)

Roadmap item E10. With `X = P_B − J P_A Jᵀ` (notation of `IdentificationBudget`), proved:

* `abs_trace_le_sum_abs_diag`: `|Tr X| ≤ Σ_j |X j j|`;
* `trace_diagonal_mul`: `Tr(diag s · X) = Σ_j s j · X j j`;
* `sum_abs_diag_le_of_dual`: if `t` bounds `|Tr(D X)|` for every diagonal contraction `D`
  (`|s j| ≤ 1`), then `Σ_j |X j j| ≤ t` (test against the sign matrix of the diagonal);
* `dual_at_diag`: that hypothesis holds with `t = Σ_j |X j j|`, so it is never vacuous;
* `identification_budget_traceNorm`:
  `|N_B − N_A| ≤ t + Σ_{a_i ≤ L} |1 − ‖J e_i‖²|` for any such `t`.

The intended `t` is the trace norm `‖X‖₁`: by the duality `‖X‖₁ = sup_{‖U‖ ≤ 1} |Tr(U X)|`
it bounds `|Tr(D X)|` for diagonal contractions `D`. That duality, and the trace norm itself
(singular values), are NOT formalized here; the hypothesis `hdual` is stated explicitly instead.

What this file does NOT prove: the trace-norm duality, anything about the Steklov operator or the
identification for the tetrahedron, any of `[H1]`–`[H6]`, or the main theorem.
-/

namespace SteklovAudit.TraceNormBudget

open Finset SteklovAudit.AbstractTransfer SteklovAudit.IdentificationBudget

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem abs_trace_le_sum_abs_diag (X : Matrix κ κ ℝ) :
    |Matrix.trace X| ≤ ∑ j, |X j j| := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  exact Finset.abs_sum_le_sum_abs _ _

theorem trace_diagonal_mul (s : κ → ℝ) (X : Matrix κ κ ℝ) :
    Matrix.trace (Matrix.diagonal s * X) = ∑ j, s j * X j j := by
  unfold Matrix.trace
  refine sum_congr rfl (fun j _ => ?_)
  rw [Matrix.diag_apply, Matrix.diagonal_mul]

/-- Sign vector of the diagonal of `X`. -/
noncomputable def signDiag (X : Matrix κ κ ℝ) : κ → ℝ :=
  fun j => if 0 ≤ X j j then 1 else -1

theorem abs_signDiag_le (X : Matrix κ κ ℝ) (j : κ) : |signDiag X j| ≤ 1 := by
  unfold signDiag
  split_ifs <;> simp

theorem signDiag_mul (X : Matrix κ κ ℝ) (j : κ) : signDiag X j * X j j = |X j j| := by
  unfold signDiag
  split_ifs with hj
  · rw [abs_of_nonneg hj]; ring
  · rw [abs_of_neg (not_le.mp hj)]; ring

/-- A dual (trace-norm type) bound against diagonal contractions dominates the diagonal sum. -/
theorem sum_abs_diag_le_of_dual (X : Matrix κ κ ℝ) (t : ℝ)
    (hdual : ∀ s : κ → ℝ, (∀ j, |s j| ≤ 1) →
      |Matrix.trace (Matrix.diagonal s * X)| ≤ t) :
    ∑ j, |X j j| ≤ t := by
  have h := hdual (signDiag X) (abs_signDiag_le X)
  rw [trace_diagonal_mul] at h
  have he : ∑ j, signDiag X j * X j j = ∑ j, |X j j| :=
    sum_congr rfl (fun j _ => signDiag_mul X j)
  rw [he, abs_of_nonneg (sum_nonneg (fun j _ => abs_nonneg _))] at h
  exact h

/-- The dual hypothesis holds at `t = Σ_j |X j j|` (non-vacuity). -/
theorem dual_at_diag (X : Matrix κ κ ℝ) (s : κ → ℝ) (hs : ∀ j, |s j| ≤ 1) :
    |Matrix.trace (Matrix.diagonal s * X)| ≤ ∑ j, |X j j| := by
  rw [trace_diagonal_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => ?_))
  rw [abs_mul]
  have h1 := hs j
  have h2 := abs_nonneg (X j j)
  have h3 := abs_nonneg (s j)
  nlinarith

/-- Identification budget in trace-norm form, with the dual bound `t` as a named hypothesis. -/
theorem identification_budget_traceNorm (J : Matrix κ ι ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (L t : ℝ)
    (hdual : ∀ s : κ → ℝ, (∀ j, |s j| ≤ 1) →
      |Matrix.trace (Matrix.diagonal s * (proj b L - J * proj a L * J.transpose))| ≤ t) :
    |(count b L : ℝ) - count a L| ≤
      t + ∑ i ∈ univ.filter (fun i => a i ≤ L), |1 - ∑ j, J j i ^ 2| := by
  have h1 := identification_budget_coords J a b L
  have h2 := abs_trace_le_sum_abs_diag (proj b L - J * proj a L * J.transpose)
  have h3 := sum_abs_diag_le_of_dual (proj b L - J * proj a L * J.transpose) t hdual
  linarith

/-- The same budget with the diagonal sum in place of `t`. -/
theorem identification_budget_diag (J : Matrix κ ι ℝ) (a : ι → ℝ) (b : κ → ℝ) (L : ℝ) :
    |(count b L : ℝ) - count a L| ≤
      ∑ j, |(proj b L - J * proj a L * J.transpose) j j|
        + ∑ i ∈ univ.filter (fun i => a i ≤ L), |1 - ∑ j, J j i ^ 2| :=
  identification_budget_traceNorm J a b L _
    (fun s hs => dual_at_diag (proj b L - J * proj a L * J.transpose) s hs)

end SteklovAudit.TraceNormBudget
