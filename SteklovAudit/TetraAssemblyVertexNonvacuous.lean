import Mathlib
import SteklovAudit.TetraAssemblyVertex
import SteklovAudit.TetraAssemblyFaceNonvacuous

/-!
# Non-vacuity of the vertex-face-edges assembly (roadmap item G164)

Definition check for G160 (`TetraAssemblyVertex.tetra_law_of_overlap_face_vertex`): its hypotheses
hold in a scalar model with a NONZERO vertex term `√(max L 0)` on top of G161's nonzero face
remainder, nonzero per-edge remainders and nonzero overlap.

Model: `vert := TetraEdgeLawNonvacuous.wsq` (`= √(max L 0)`), total count `fvN L := fwN L + wsq L`,
`face := fwFace`, per-edge counts `fwNe` (all from `TetraAssemblyFaceNonvacuous`), `Af = Bf = 1`,
`A = c = 0`, `C = 1`.

* `vertex_witness_vert`: the `o(L)` vertex input.
* `vertex_witness_ne`: the vertex term is nonzero for `L > 0`.
* `vertex_witness_overlap`: the `O(ε L)` overlap bound for `fvN − vert`.
* `vertex_witness_conclusion`: G160 applies.

What this file does NOT prove: (7.49), H4, the face law H6, the overlap bound or any per-edge law for
the actual tetrahedron Dirichlet-to-Neumann operator, (11.3), H5, or Theorem 1.3 / 11.1. The model
functions are explicit scalar functions chosen only to show that the hypotheses of G160 are
satisfiable with a nonzero vertex term.
-/

namespace SteklovAudit.TetraAssemblyVertexNonvacuous

open Filter

/-- **G164.** Witness total count: G161's total plus a nonzero vertex term `√(max L 0)`. -/
noncomputable def fvN (L : ℝ) : ℝ :=
  SteklovAudit.TetraAssemblyFaceNonvacuous.fwN L + SteklovAudit.TetraEdgeLawNonvacuous.wsq L

/-- **G164.** The vertex input `vert = o(L)` holds for `vert = √(max L 0)`. -/
theorem vertex_witness_vert : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
    |SteklovAudit.TetraEdgeLawNonvacuous.wsq L| ≤ η * L := by
  intro η hη
  filter_upwards [SteklovAudit.TetraEdgeLawNonvacuous.sqrt_littleO η hη] with L hL
  exact hL

/-- **G164.** The vertex term is nonzero for `L > 0`. -/
theorem vertex_witness_ne (L : ℝ) (hL : 0 < L) : SteklovAudit.TetraEdgeLawNonvacuous.wsq L ≠ 0 :=
  ne_of_gt (SteklovAudit.TetraEdgeLawNonvacuous.wsq_pos L hL)

/-- **G164.** The overlap bound of G160 for the witness: `fvN − vert − face − ∑ edges` is at most
`1 * ε * L` eventually, for every `ε > 0`. -/
theorem vertex_witness_overlap : ∀ ε : ℝ, 0 < ε → ∀ᶠ L in atTop,
    |fvN L - SteklovAudit.TetraEdgeLawNonvacuous.wsq L - SteklovAudit.TetraAssemblyFaceNonvacuous.fwFace L -
      ∑ e, SteklovAudit.TetraAssemblyFaceNonvacuous.fwNe e L| ≤ 1 * ε * L := by
  intro ε hε
  filter_upwards [SteklovAudit.TetraAssemblyFaceNonvacuous.face_witness_overlap ε hε] with L hL
  have heq : fvN L - SteklovAudit.TetraEdgeLawNonvacuous.wsq L -
      SteklovAudit.TetraAssemblyFaceNonvacuous.fwFace L -
      ∑ e, SteklovAudit.TetraAssemblyFaceNonvacuous.fwNe e L =
      SteklovAudit.TetraAssemblyFaceNonvacuous.fwN L -
      SteklovAudit.TetraAssemblyFaceNonvacuous.fwFace L -
      ∑ e, SteklovAudit.TetraAssemblyFaceNonvacuous.fwNe e L := by
    first
      | (unfold fvN; ring)
      | (simp only [fvN]; ring)
  rw [heq]
  exact hL

/-- **G164.** G160 applies to the witness: the total count `fvN` obeys the two-term law with
coefficients `1 + ∑ 0` and `1 + ∑ 0`, although the vertex term, face remainder, per-edge remainders
and overlap are all nonzero. -/
theorem vertex_witness_conclusion : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
    |fvN L - ((1 + ∑ _i : Fin 6, (0 : ℝ)) * L ^ 2 + (1 + ∑ _i : Fin 6, (0 : ℝ)) * L)| ≤ η * L :=
  SteklovAudit.TetraAssemblyVertex.tetra_law_of_overlap_face_vertex fvN
    SteklovAudit.TetraAssemblyFaceNonvacuous.fwFace SteklovAudit.TetraEdgeLawNonvacuous.wsq 1 1
    (fun _ => 0) (fun _ => 0) 1 zero_le_one vertex_witness_vert
    SteklovAudit.TetraAssemblyFaceNonvacuous.face_witness_law
    (fun ε hε => ⟨SteklovAudit.TetraAssemblyFaceNonvacuous.fwNe,
      SteklovAudit.TetraAssemblyFaceNonvacuous.face_witness_edge_laws, vertex_witness_overlap ε hε⟩)

end SteklovAudit.TetraAssemblyVertexNonvacuous
