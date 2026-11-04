import Mathlib
import SteklovAudit.VertexLog
import SteklovAudit.LedgerNonvacuousC6

/-!
# D6: the D5 ledger is satisfiable

Roadmap item D6. `Thm111InputsD5` (D5) replaces `[H4 vertex]` by the explicit (7.49) form, so its
consistency must be re-checked, as C8 did for the C6 ledger. The C8 witness (one spectral
coordinate, the whole count in the edge piece, trivial edge cutoffs) also meets the (7.49) form
with `C_V = 0`, `K_V = 0`, and `nonvacuous_D5` applies `theorem_11_1_of_D5` to it.

What this file does NOT prove: anything about the Steklov operator. The instance is a consistency
witness only; it shows the ledger is not contradictory, not that the paper's partition meets it.
It does not prove the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.LedgerNonvacuousD5

open SteklovAudit SteklovAudit.MainConditional SteklovAudit.PartitionTrace
  SteklovAudit.EdgeLength SteklovAudit.VertexLog SteklovAudit.LedgerNonvacuousC6

/-- An explicit instance of the D5 ledger for the exact two-term count. -/
noncomputable def exactInputsD5 (a c : ℝ) (ha : 0 ≤ a) :
    Thm111InputsD5 Unit (fun L => realWeylPolynomial (areaCoeff a) (6 * a * c) L) a c where
  P := P1 a c
  w := fun _ => Real.sqrt 3 * a ^ 2
  qV := fun _ _ => 0
  qE := fun _ _ _ => 1
  qF := fun _ _ _ => 0
  cut := cutTriv a
  ha := ha
  CV := 0
  KV := fun _ => 0
  DE := fun _ => 0
  hCV := le_refl 0
  hKV := fun _ => le_refl 0
  hDE := fun _ => le_refl 0
  count := (exactInputsC6 a c ha).count
  sq_sum := (exactInputsC6 a c ha).sq_sum
  wsum := (exactInputsC6 a c ha).wsum
  vertex := by
    intro ε _ L _
    exact zero_piece a c L (0 * ε * L + 0 * (Real.log L + 1)) (by simp)
  edge := (exactInputsC6 a c ha).edge
  face := (exactInputsC6 a c ha).face

/-- D6. Non-vacuity of the D5 ledger: `theorem_11_1_of_D5` applies to an actual instance. -/
theorem nonvacuous_D5 (a c : ℝ) (ha : 0 ≤ a) :
    HasSharpRealLaw (fun L => realWeylPolynomial (areaCoeff a) (6 * a * c) L)
      (areaCoeff a) (6 * a * c) :=
  theorem_11_1_of_D5 _ a c (exactInputsD5 a c ha)

end SteklovAudit.LedgerNonvacuousD5
