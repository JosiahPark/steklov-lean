import Mathlib
import SteklovAudit.AbstractTransfer

/-!
# Hilbert–Schmidt smallness does not control the trace (roadmap R1, paper proof R43.2(ii))

On `Fin n` (`n ≥ 1`) the scalar matrix `T = n⁻¹ I` has `‖T‖²_HS = 1/n` and `Tr T = 1`. So along
`n → ∞` the Hilbert–Schmidt norm tends to `0` while the trace stays `1`, and `T` attains equality in
`|Tr T|² ≤ rank · ‖T‖²_HS` (compare `SteklovAudit.AbstractTransfer.trace_rank_amplification`).
This is why a uniform HS bound costs a factor `√rank` when it is converted to a trace bound.

What this module does NOT prove: anything about the tetrahedral Steklov operator, any of the
ledger hypotheses `[H1]`–`[H6]`, or the main theorem (Theorem 1.3 / 11.1). It is a
finite-dimensional sharpness example only.
-/

namespace SteklovAudit.HSNoTrace

open Finset Filter Topology SteklovAudit.AbstractTransfer

/-- The scalar matrix `n⁻¹ I` on `Fin n`. -/
noncomputable def scalarDiag (n : ℕ) (i j : Fin n) : ℝ := if i = j then (n : ℝ)⁻¹ else 0

theorem scalarDiag_diag (n : ℕ) (i : Fin n) : scalarDiag n i i = (n : ℝ)⁻¹ := if_pos rfl

theorem scalarDiag_off (n : ℕ) {i j : Fin n} (h : i ≠ j) : scalarDiag n i j = 0 := if_neg h

/-- `‖n⁻¹ I‖²_HS = 1/n`. -/
theorem hs2_scalarDiag (n : ℕ) (hn : 0 < n) : hs2 (scalarDiag n) = 1 / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hrow : ∀ i : Fin n, ∑ j : Fin n, scalarDiag n i j ^ 2 = ((n : ℝ)⁻¹) ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [scalarDiag_diag]
    · intro j _ hj
      rw [scalarDiag_off n (Ne.symm hj)]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  unfold SteklovAudit.AbstractTransfer.hs2
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sq, ← mul_assoc, mul_inv_cancel₀ hn', one_mul, one_div]

/-- `Tr(n⁻¹ I) = 1`. -/
theorem trace_scalarDiag (n : ℕ) (hn : 0 < n) : ∑ i : Fin n, scalarDiag n i i = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [scalarDiag_diag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ hn'

/-- The HS norms tend to `0` along `n → ∞` ... -/
theorem hs2_tendsto_zero :
    Tendsto (fun n : ℕ => hs2 (scalarDiag (n + 1))) atTop (𝓝 0) := by
  have h := tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  refine Tendsto.congr (fun n => ?_) h
  exact (hs2_scalarDiag (n + 1) n.succ_pos).symm

/-- ... while every trace equals `1`. -/
theorem trace_const (n : ℕ) : ∑ i : Fin (n + 1), scalarDiag (n + 1) i i = 1 :=
  trace_scalarDiag (n + 1) n.succ_pos

/-- HS smallness does not force trace smallness: no bound `|Tr T| ≤ C ‖T‖²_HS` with a constant
independent of the dimension. -/
theorem no_dimension_free_trace_bound (C : ℝ) :
    ∃ n : ℕ, ∃ hn : 0 < n, C * hs2 (scalarDiag n) < |∑ i : Fin n, scalarDiag n i i| := by
  obtain ⟨m, hm⟩ := exists_nat_gt C
  refine ⟨m + 1, m.succ_pos, ?_⟩
  rw [trace_scalarDiag (m + 1) m.succ_pos, hs2_scalarDiag (m + 1) m.succ_pos, abs_one]
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [mul_one_div, div_lt_one hpos]
  push_cast
  linarith

/-- Equality in `trace_rank_amplification` with `s = univ` (rank `n`). -/
theorem rank_amplification_equality (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ (univ : Finset (Fin n)), scalarDiag n j j) ^ 2 =
      (univ : Finset (Fin n)).card * ∑ j ∈ (univ : Finset (Fin n)), ∑ i, scalarDiag n i j ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Finset.sum_comm]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, scalarDiag n i j ^ 2 = 1 / n := hs2_scalarDiag n hn
  rw [h2, trace_scalarDiag n hn, Finset.card_univ, Fintype.card_fin, one_pow,
    mul_one_div_cancel hn']

/-- Square-root form: `|Tr T| = √rank · ‖T‖_HS = 1`. -/
theorem sqrt_rank_equality (n : ℕ) (hn : 0 < n) :
    |∑ i : Fin n, scalarDiag n i i| = Real.sqrt n * Real.sqrt (hs2 (scalarDiag n)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [trace_scalarDiag n hn, hs2_scalarDiag n hn, abs_one, ← Real.sqrt_mul (Nat.cast_nonneg n),
    mul_one_div_cancel hn', Real.sqrt_one]

end SteklovAudit.HSNoTrace
