import Mathlib
import SteklovAudit.TetraEdgeLawOverlap

/-!
# Non-vacuity of the tetrahedron overlap reduction (roadmap item G153)

Definition check for G151 (`TetraEdgeLawOverlap.tetra_edge_law_of_overlap`): its hypotheses hold
for an explicit scalar witness whose six per-edge remainders and whose collar overlap are all
NONZERO (each equal to `√(max L 0)`), so the theorem is not vacuous and does not secretly force the
remainders to vanish.

* `sqrt_littleO`: `√(max L 0)` is `o(L)` in `η`-form (take `L ≥ 1 / η ^ 2`).
* `wNe`, `wN`: the witness per-edge counts `A L² + c L + √(max L 0)` and total count
  `∑ wNe + √(max L 0)`.
* `witness_edge_laws`, `witness_overlap`: the two hypotheses of `tetra_edge_law_of_overlap`
  (with `face = 0`, `C = 1`).
* `witness_nonvacuous`: the hypotheses hold and both the overlap and every per-edge remainder are
  nonzero for `L > 0`; `witness_conclusion`: G151 then applies to the witness.

What this file does NOT prove: anything about the actual Steklov / Dirichlet-to-Neumann counting
function, the overlap bound near the vertices (H3/H4 geometry), the per-edge law (7.38), (7.45),
(7.29), (9.1), (11.3), H1–H6, or Theorem 1.3 / 11.1. The witness is an artificial scalar function.
-/

namespace SteklovAudit.TetraEdgeLawNonvacuous

open Filter

/-- **G153.** `√(max L 0)` is `o(L)` in `η`-form. -/
theorem sqrt_littleO : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |Real.sqrt (max L 0)| ≤ η * L := by
  intro η hη
  filter_upwards [eventually_ge_atTop (1 / η ^ 2), eventually_ge_atTop (0 : ℝ)] with L hL hL0
  rw [max_eq_left hL0, abs_of_nonneg (Real.sqrt_nonneg L)]
  have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0
  have hη2 : 0 < η ^ 2 := by positivity
  have e : η ^ 2 * (1 / η ^ 2) = 1 := by
    first
      | field_simp
      | exact mul_one_div_cancel (pow_ne_zero 2 hη.ne')
  have h1 : 1 ≤ η ^ 2 * L := by
    have hm := mul_le_mul_of_nonneg_left hL hη2.le
    linarith
  have h2 : (η * Real.sqrt L) ^ 2 = η ^ 2 * L := by
    first
      | rw [mul_pow, pow_two (Real.sqrt L), hss]
      | nlinarith [hss]
  have hηs0 : 0 ≤ η * Real.sqrt L := mul_nonneg hη.le hs0
  have hηs : 1 ≤ η * Real.sqrt L := by nlinarith [h2, h1, hηs0]
  calc Real.sqrt L = 1 * Real.sqrt L := by ring
    _ ≤ (η * Real.sqrt L) * Real.sqrt L := mul_le_mul_of_nonneg_right hηs hs0
    _ = η * L := by rw [mul_assoc, hss]

/-- The witness remainder `√(max L 0)`. -/
noncomputable def wsq (L : ℝ) : ℝ := Real.sqrt (max L 0)

/-- Witness per-edge counts: `A L² + c L + √(max L 0)` on every edge. -/
noncomputable def wNe (A c : ℝ) : Fin 6 → ℝ → ℝ := fun _ L => A * L ^ 2 + c * L + wsq L

/-- Witness total count: the six edge counts plus a nonzero overlap `√(max L 0)`. -/
noncomputable def wN (A c : ℝ) : ℝ → ℝ := fun L => ∑ e, wNe A c e L + wsq L

theorem wsq_pos (L : ℝ) (hL : 0 < L) : 0 < wsq L := by
  unfold wsq
  exact Real.sqrt_pos.mpr (lt_max_of_lt_left hL)

/-- **G153.** The witness satisfies the per-edge laws with nonzero remainder `√(max L 0)`. -/
theorem witness_edge_laws (A c : ℝ) : ∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
    |wNe A c e L - (A * L ^ 2 + c * L)| ≤ η * L := by
  intro e η hη
  filter_upwards [sqrt_littleO η hη] with L hL
  show |A * L ^ 2 + c * L + wsq L - (A * L ^ 2 + c * L)| ≤ η * L
  rw [show A * L ^ 2 + c * L + wsq L - (A * L ^ 2 + c * L) = wsq L by ring]
  exact hL

/-- **G153.** The witness overlap `√(max L 0)` is at most `1 * ε * L` eventually, for every `ε > 0`. -/
theorem witness_overlap (A c : ℝ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ L in atTop,
    |wN A c L - 0 - ∑ e, wNe A c e L| ≤ 1 * ε * L := by
  intro ε hε
  filter_upwards [sqrt_littleO ε hε] with L hL
  show |(∑ e, wNe A c e L + wsq L) - 0 - ∑ e, wNe A c e L| ≤ 1 * ε * L
  rw [show (∑ e, wNe A c e L + wsq L) - 0 - ∑ e, wNe A c e L = wsq L by ring, one_mul]
  exact hL

/-- **G153.** All hypotheses of `tetra_edge_law_of_overlap` hold for the witness (with
`face = 0`, `C = 1`), while the overlap and every per-edge remainder are nonzero for `L > 0`. -/
theorem witness_nonvacuous (A c : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ Ne' : Fin 6 → ℝ → ℝ,
      (∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
        |Ne' e L - (A * L ^ 2 + c * L)| ≤ η * L) ∧
      ∀ᶠ L in atTop, |wN A c L - 0 - ∑ e, Ne' e L| ≤ 1 * ε * L) ∧
    (∀ L : ℝ, 0 < L → wN A c L - ∑ e, wNe A c e L ≠ 0) ∧
    (∀ L : ℝ, 0 < L → ∀ e : Fin 6, wNe A c e L - (A * L ^ 2 + c * L) ≠ 0) := by
  refine ⟨fun ε hε => ⟨wNe A c, witness_edge_laws A c, witness_overlap A c ε hε⟩, ?_, ?_⟩
  · intro L hL
    show (∑ e, wNe A c e L + wsq L) - ∑ e, wNe A c e L ≠ 0
    rw [show (∑ e, wNe A c e L + wsq L) - ∑ e, wNe A c e L = wsq L by ring]
    exact ne_of_gt (wsq_pos L hL)
  · intro L hL e
    show A * L ^ 2 + c * L + wsq L - (A * L ^ 2 + c * L) ≠ 0
    rw [show A * L ^ 2 + c * L + wsq L - (A * L ^ 2 + c * L) = wsq L by ring]
    exact ne_of_gt (wsq_pos L hL)

/-- **G153.** G151 applies to the witness: its edge part obeys the tetrahedron edge law. -/
theorem witness_conclusion (A c : ℝ) : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
    |wN A c L - 0 - ((∑ _e : Fin 6, A) * L ^ 2 + (∑ _e : Fin 6, c) * L)| ≤ η * L :=
  SteklovAudit.TetraEdgeLawOverlap.tetra_edge_law_of_overlap (wN A c) (fun _ => 0)
    (fun _ => A) (fun _ => c) 1 zero_le_one
    (fun ε hε => ⟨wNe A c, witness_edge_laws A c, witness_overlap A c ε hε⟩)

end SteklovAudit.TetraEdgeLawNonvacuous
