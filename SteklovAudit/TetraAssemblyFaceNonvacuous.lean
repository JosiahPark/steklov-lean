import Mathlib
import SteklovAudit.TetraAssemblyFace
import SteklovAudit.TetraEdgeLawNonvacuous

/-!
# Non-vacuity of the face-plus-edges tetrahedron assembly (roadmap item G161)

Definition check for G155 (`TetraAssemblyFace.tetra_law_of_overlap_and_face`): its hypotheses
hold for an explicit scalar witness whose face remainder, six per-edge remainders and collar
overlap are all NONZERO (each equal to `√(max L 0)`), so the theorem is not vacuous and does not
secretly force any remainder to vanish.

Model: `fwFace L = L ^ 2 + L + √(max L 0)` (so `Af = Bf = 1`), per-edge counts
`fwNe e L = √(max L 0)` (so `A = c = 0`), total `fwN = fwFace + ∑ fwNe + √(max L 0)`, `C = 1`.

* `face_witness_law`: the named face input of G155 holds for `fwFace`.
* `face_witness_remainder_ne`: the face remainder `fwFace L - (L ^ 2 + L)` is nonzero for `L > 0`.
* `face_witness_edge_laws`, `face_witness_overlap`: the per-edge laws and the `O(ε L)` overlap.
* `face_witness_hyps`: all hypotheses of `tetra_law_of_overlap_and_face` for the witness.
* `face_witness_nonzero`: every per-edge remainder and the overlap are nonzero for `L > 0`.
* `face_witness_conclusion`: G155 applied to the witness.

What this file does NOT prove: anything about the actual Steklov / Dirichlet-to-Neumann counting
function, the face law (Lemma 7.4 / §10.2, H6), the vertex term (7.49) / H4, the overlap bound
near the vertices (H3/H4 geometry), the per-edge law (7.38), (7.45), (7.29), (9.1), (11.3),
H1–H6, or Theorem 1.3 / 11.1. The witness is an artificial scalar function.
-/

namespace SteklovAudit.TetraAssemblyFaceNonvacuous

open Filter

/-- Witness face count `L ^ 2 + L + √(max L 0)`. -/
noncomputable def fwFace (L : ℝ) : ℝ := L ^ 2 + L + SteklovAudit.TetraEdgeLawNonvacuous.wsq L

/-- Witness per-edge counts: pure remainder `√(max L 0)` on every edge. -/
noncomputable def fwNe : Fin 6 → ℝ → ℝ := fun _ L => SteklovAudit.TetraEdgeLawNonvacuous.wsq L

/-- Witness total count: face, six edges and a nonzero overlap `√(max L 0)`. -/
noncomputable def fwN (L : ℝ) : ℝ :=
  fwFace L + ∑ e, fwNe e L + SteklovAudit.TetraEdgeLawNonvacuous.wsq L

/-- **G161.** The face input of G155 holds for `fwFace` with `Af = Bf = 1`. -/
theorem face_witness_law : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
    |fwFace L - (1 * L ^ 2 + 1 * L)| ≤ η * L := by
  intro η hη
  filter_upwards [SteklovAudit.TetraEdgeLawNonvacuous.sqrt_littleO η hη] with L hL
  have e : fwFace L - (1 * L ^ 2 + 1 * L) = SteklovAudit.TetraEdgeLawNonvacuous.wsq L := by
    first
      | (unfold fwFace; ring)
      | (simp only [fwFace]; ring)
  rw [e]
  exact hL

/-- **G161.** The face remainder is nonzero for `L > 0`. -/
theorem face_witness_remainder_ne (L : ℝ) (hL : 0 < L) : fwFace L - (L ^ 2 + L) ≠ 0 := by
  have e : fwFace L - (L ^ 2 + L) = SteklovAudit.TetraEdgeLawNonvacuous.wsq L := by
    first
      | (unfold fwFace; ring)
      | (simp only [fwFace]; ring)
  rw [e]
  exact ne_of_gt (SteklovAudit.TetraEdgeLawNonvacuous.wsq_pos L hL)

/-- **G161.** The per-edge laws hold with `A = c = 0` and nonzero remainder `√(max L 0)`. -/
theorem face_witness_edge_laws : ∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
    |fwNe e L - (0 * L ^ 2 + 0 * L)| ≤ η * L := by
  intro e η hη
  filter_upwards [SteklovAudit.TetraEdgeLawNonvacuous.sqrt_littleO η hη] with L hL
  show |SteklovAudit.TetraEdgeLawNonvacuous.wsq L - (0 * L ^ 2 + 0 * L)| ≤ η * L
  rw [show SteklovAudit.TetraEdgeLawNonvacuous.wsq L - (0 * L ^ 2 + 0 * L)
      = SteklovAudit.TetraEdgeLawNonvacuous.wsq L by ring]
  exact hL

/-- **G161.** The overlap `√(max L 0)` is at most `1 * ε * L` eventually, for every `ε > 0`. -/
theorem face_witness_overlap : ∀ ε : ℝ, 0 < ε → ∀ᶠ L in atTop,
    |fwN L - fwFace L - ∑ e, fwNe e L| ≤ 1 * ε * L := by
  intro ε hε
  filter_upwards [SteklovAudit.TetraEdgeLawNonvacuous.sqrt_littleO ε hε] with L hL
  have heq : fwN L - fwFace L - ∑ e, fwNe e L = SteklovAudit.TetraEdgeLawNonvacuous.wsq L := by
    first
      | (unfold fwN; ring)
      | (simp only [fwN]; ring)
  rw [heq, one_mul]
  exact hL

/-- **G161.** All hypotheses of `tetra_law_of_overlap_and_face` hold for the witness
(`N = fwN`, `face = fwFace`, `Af = Bf = 1`, `A = c = 0`, `C = 1`). -/
theorem face_witness_hyps :
    (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |fwFace L - (1 * L ^ 2 + 1 * L)| ≤ η * L) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Ne : Fin 6 → ℝ → ℝ,
      (∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
        |Ne e L - (0 * L ^ 2 + 0 * L)| ≤ η * L) ∧
      ∀ᶠ L in atTop, |fwN L - fwFace L - ∑ e, Ne e L| ≤ 1 * ε * L) :=
  ⟨face_witness_law, fun ε hε => ⟨fwNe, face_witness_edge_laws, face_witness_overlap ε hε⟩⟩

/-- **G161.** Every per-edge remainder and the overlap are nonzero for `L > 0`. -/
theorem face_witness_nonzero (L : ℝ) (hL : 0 < L) :
    (∀ e : Fin 6, fwNe e L - (0 * L ^ 2 + 0 * L) ≠ 0) ∧
    fwN L - fwFace L - ∑ e, fwNe e L ≠ 0 := by
  have hp := SteklovAudit.TetraEdgeLawNonvacuous.wsq_pos L hL
  refine ⟨fun e => ?_, ?_⟩
  · show SteklovAudit.TetraEdgeLawNonvacuous.wsq L - (0 * L ^ 2 + 0 * L) ≠ 0
    rw [show SteklovAudit.TetraEdgeLawNonvacuous.wsq L - (0 * L ^ 2 + 0 * L)
        = SteklovAudit.TetraEdgeLawNonvacuous.wsq L by ring]
    exact ne_of_gt hp
  · have e : fwN L - fwFace L - ∑ e, fwNe e L = SteklovAudit.TetraEdgeLawNonvacuous.wsq L := by
      first
        | (unfold fwN; ring)
        | (simp only [fwN]; ring)
    rw [e]
    exact ne_of_gt hp

/-- **G161.** G155 applies to the witness: the total count obeys the two-term law with
coefficients `1 + ∑ 0` and `1 + ∑ 0`. -/
theorem face_witness_conclusion : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
    |fwN L - ((1 + ∑ _i : Fin 6, (0 : ℝ)) * L ^ 2 + (1 + ∑ _i : Fin 6, (0 : ℝ)) * L)|
      ≤ η * L :=
  SteklovAudit.TetraAssemblyFace.tetra_law_of_overlap_and_face fwN fwFace 1 1
    (fun _ => 0) (fun _ => 0) 1 zero_le_one face_witness_law
    (fun ε hε => ⟨fwNe, face_witness_edge_laws, face_witness_overlap ε hε⟩)

end SteklovAudit.TetraAssemblyFaceNonvacuous
