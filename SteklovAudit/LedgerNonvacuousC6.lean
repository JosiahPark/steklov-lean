import Mathlib
import SteklovAudit.EdgeLength

/-!
# C8: the C6 ledger is satisfiable

Roadmap item C8. `Thm111InputsC6` (C5 + C6: `[H1]`–`[H3]` derived from a finite squared
partition and edge cutoffs) adds structure to the original ledger, so its consistency must be
re-checked. Here an explicit instance (one spectral coordinate, the whole count put in the edge
piece, trivial edge cutoffs with `K = 0`) meets every field for the exact two-term count, and
`nonvacuous_C6` applies `theorem_11_1_of_C6` to it.

What this file does NOT prove: anything about the Steklov operator. The instance is a consistency
witness only; it shows the ledger is not contradictory, not that the paper's partition meets it.
It does not prove the main theorem.
-/

namespace SteklovAudit.LedgerNonvacuousC6

open SteklovAudit SteklovAudit.MainConditional SteklovAudit.PartitionTrace
  SteklovAudit.EdgeLength

/-- Trivial edge cutoffs: `q_e² ≡ 1`, `K = 0`. -/
noncomputable def cutTriv (a : ℝ) : EdgeCutoffs a where
  K := 0
  hK := le_refl 0
  q2 := fun _ _ _ => 1
  cont := fun _ _ => continuous_const
  nonneg := fun _ _ _ _ => zero_le_one
  le_one := fun _ _ _ _ => le_refl 1
  one_mid := fun _ _ _ _ => rfl

theorem cutTriv_len (a ε : ℝ) : (cutTriv a).len ε = 6 * a := by
  show ∑ _e : Fin 6, ∫ _x in (0:ℝ)..a, (1:ℝ) = 6 * a
  first | simp | (simp; ring) | norm_num

/-- Localized trace on one coordinate with a constant cutoff. -/
theorem loc_unit (P : ℝ → Matrix Unit Unit ℝ) (k L : ℝ) :
    loc P (fun _ => k) L = k ^ 2 * P L () () := by
  unfold loc
  first
    | (simp [Matrix.trace, diag_conj_entry]; done)
    | (simp [Matrix.trace, diag_conj_entry]; ring)
    | (simp [Matrix.trace]; ring)

theorem areaOf_unit (a k : ℝ) :
    areaOf (fun _ : Unit => Real.sqrt 3 * a ^ 2) (fun _ => k) = k ^ 2 * areaCoeff a := by
  unfold areaOf areaCoeff
  first | (simp; ring) | simp | (simp; field_simp) | (simp; field_simp; ring)

/-- The one-coordinate count matrix. -/
noncomputable def P1 (a c : ℝ) (L : ℝ) : Matrix Unit Unit ℝ :=
  Matrix.diagonal (fun _ => realWeylPolynomial (areaCoeff a) (6 * a * c) L)

/-- A piece with cutoff `0` contributes nothing. -/
theorem zero_piece (a c L t : ℝ) (ht : 0 ≤ t) :
    |loc (P1 a c) (fun _ => 0) L - areaOf (fun _ : Unit => Real.sqrt 3 * a ^ 2) (fun _ => 0) * L ^ 2|
      ≤ t := by
  rw [loc_unit, areaOf_unit]
  simpa using ht

/-- The piece with cutoff `1` carries the whole two-term count. -/
theorem one_piece (a c L ε t : ℝ) (ht : 0 ≤ t) :
    |loc (P1 a c) (fun _ => 1) L - areaOf (fun _ : Unit => Real.sqrt 3 * a ^ 2) (fun _ => 1) * L ^ 2
      - c * (cutTriv a).len ε * L| ≤ t := by
  rw [loc_unit, areaOf_unit, cutTriv_len]
  simp only [P1, Matrix.diagonal_apply_eq, realWeylPolynomial, one_pow, one_mul]
  first
    | (ring_nf; simpa using ht)
    | (rw [show areaCoeff a * L ^ 2 + 6 * a * c * L - areaCoeff a * L ^ 2 - c * (6 * a) * L = 0
          by ring, abs_zero]; exact ht)

/-- An explicit instance of the C6 ledger for the exact two-term count. -/
noncomputable def exactInputsC6 (a c : ℝ) (ha : 0 ≤ a) :
    Thm111InputsC6 Unit (fun L => realWeylPolynomial (areaCoeff a) (6 * a * c) L) a c where
  P := P1 a c
  w := fun _ => Real.sqrt 3 * a ^ 2
  qV := fun _ _ => 0
  qE := fun _ _ _ => 1
  qF := fun _ _ _ => 0
  cut := cutTriv a
  ha := ha
  CV := 0
  DE := fun _ => 0
  hCV := le_refl 0
  hDE := fun _ => le_refl 0
  count := by
    intro L
    unfold P1
    first | simp [Matrix.trace_diagonal] | rw [Matrix.trace_diagonal, Fintype.sum_unique]
  sq_sum := by intros; norm_num
  wsum := by simp
  vertex := by
    intro ε _ η hη
    exact ⟨0, fun L hL => zero_piece a c L ((0 * ε + η) * L) (mul_nonneg (by linarith) hL)⟩
  edge := by
    intro ε γ _ _ η hη
    exact ⟨0, fun L hL => one_piece a c L ε ((0 * γ + η) * L) (mul_nonneg (by linarith) hL)⟩
  face := by
    intro ε γ _ _ η hη
    exact ⟨0, fun L hL => zero_piece a c L (η * L) (mul_nonneg hη.le hL)⟩

/-- Non-vacuity of the C6 ledger: `theorem_11_1_of_C6` applies to an actual instance. -/
theorem nonvacuous_C6 (a c : ℝ) (ha : 0 ≤ a) :
    HasSharpRealLaw (fun L => realWeylPolynomial (areaCoeff a) (6 * a * c) L)
      (areaCoeff a) (6 * a * c) :=
  theorem_11_1_of_C6 _ a c (exactInputsC6 a c ha)

end SteklovAudit.LedgerNonvacuousC6
