import Mathlib
import SteklovAudit.PartitionKeptLength

/-!
# Kept edge length of the tetrahedral partition: assembly (roadmap item K7b)

Third step of the explicit partition of `∂T_a` (Josiah's construction, 2026-11-26), toward ledger
input H3 (edge length) of `MainConditional.lean`. Item K7a (`PartitionKeptLength.lean`) computed the
three pieces of `∫₀ᵃ q_ε²` for the edge cutoff `q_ε z = sin(β(z/ε)) sin(β((a − z)/ε))`. Here, for a
continuous profile `β`, `0 < ε` and `4ε ≤ a`:

* `edge_kept_length`: `∫₀ᵃ q_ε(z)² dz = a − 3ε` (adjacent intervals at `2ε` and `a − 2ε`);
* `six_edges_kept_length`, `kept_length`: summed over the six edges of the tetrahedron, `6a − 18ε`;
* `ledger_length`, `ledger_length_integral`: `|(6a − 18ε) − 6a| ≤ 18ε`, the H3 bound with `CL = 18`.

What this file does NOT prove: that `edgeCut` is the edge cutoff of the paper for the adapted radius
`R_v` of (7.48) (item K11b), the H3 field of `Thm111Inputs` for the actual partition (it is only the
explicit one-variable integral), any statement about the Dirichlet-to-Neumann operator, H4–H6, or
Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.PartitionKeptLengthTotal

open Real SteklovAudit.PartitionProfile SteklovAudit.PartitionKeptLength

/-- **K7b.** The kept length of one edge: `∫₀ᵃ q_ε² = a − 3ε`. -/
theorem edge_kept_length (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {ε a : ℝ}
    (hε : 0 < ε) (ha : 4 * ε ≤ a) :
    ∫ z in (0 : ℝ)..a, edgeCut β ε a z ^ 2 = a - 3 * ε := by
  have hc := edgeCut_continuous β hβ ε a
  have hi : ∀ x y : ℝ,
      IntervalIntegrable (fun z => edgeCut β ε a z ^ 2) MeasureTheory.volume x y :=
    fun x y => hc.intervalIntegrable x y
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (2 * ε)) (hi (2 * ε) a)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi (2 * ε) (a - 2 * ε))
    (hi (a - 2 * ε) a)
  have hl := left_integral β hβ h hε ha
  have hm := mid_integral β h hε ha
  have hr := right_integral β hβ h hε ha
  linarith

/-- **K7b.** The six edges of the tetrahedron together keep length `6a − 18ε`. -/
theorem six_edges_kept_length (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {ε a : ℝ}
    (hε : 0 < ε) (ha : 4 * ε ≤ a) :
    ∑ _e : Fin 6, (∫ z in (0 : ℝ)..a, edgeCut β ε a z ^ 2) = 6 * a - 18 * ε := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    edge_kept_length β hβ h hε ha]
  first
    | (push_cast; ring)
    | (norm_num; ring)
    | norm_num

/-- **K7b.** `6 (a − 3ε) = 6a − 18ε`. -/
theorem kept_length (a ε : ℝ) : 6 * (a - 3 * ε) = 6 * a - 18 * ε := by ring

/-- **K7b.** The H3 bound with `CL = 18`: `|(6a − 18ε) − 6a| ≤ 18ε`. -/
theorem ledger_length {a ε : ℝ} (hε : 0 ≤ ε) : |(6 * a - 18 * ε) - 6 * a| ≤ 18 * ε :=
  abs_le.mpr ⟨by linarith, by linarith⟩

/-- **K7b.** The H3 bound stated for the explicit partition's kept-length integral. -/
theorem ledger_length_integral (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {ε a : ℝ}
    (hε : 0 < ε) (ha : 4 * ε ≤ a) :
    |6 * (∫ z in (0 : ℝ)..a, edgeCut β ε a z ^ 2) - 6 * a| ≤ 18 * ε := by
  rw [edge_kept_length β hβ h hε ha]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SteklovAudit.PartitionKeptLengthTotal
