import Mathlib
import SteklovAudit.TetraEdgeLawOverlap

/-!
# Face term added to the tetrahedron edge assembly (roadmap item G155)

Scalar form of the last assembly step in (7.45): if the face count obeys a two-term law
`face L = Af * L ^ 2 + Bf * L + o(L)` (a named input with the H6 shape) and the edge part
`N L - face L` obeys the conclusion of G151 `tetra_edge_law_of_overlap`, then the total count obeys
`N L = (Af + ∑ A e) * L ^ 2 + (Bf + ∑ c e) * L + o(L)`. "`o(L)`" is the `η`-form
`∀ η > 0, ∀ᶠ L in atTop, |r L| ≤ η * L` used throughout.

* `tetra_law_of_face_and_edges`: face law plus edge-part law give the total law (split `η / 2`).
* `tetra_law_of_overlap_and_face`: the same conclusion directly from the hypotheses of
  `tetra_edge_law_of_overlap` plus the face input.
* `tetra_law_equal_edges`: equal edges, coefficients `Af + 6 * A` and `Bf + 6 * c`.

What this file does NOT prove: the face law (Lemma 7.4 / §10.2, H6), the vertex term H4, the
overlap bound near the vertices (H3/H4 geometry), any per-edge law for an actual operator,
(7.29), (7.38)/(7.45), (9.1), (11.3), H1–H6, or Theorem 1.3 / 11.1. Everything here is real
analysis of scalar functions; every input is an explicit hypothesis.
-/

namespace SteklovAudit.TetraAssemblyFace

open Filter

/-- **G155.** A two-term face law plus the edge-part law give the tetrahedron two-term law. -/
theorem tetra_law_of_face_and_edges (N face : ℝ → ℝ) (Af Bf : ℝ) (A c : Fin 6 → ℝ)
    (hface : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |face L - (Af * L ^ 2 + Bf * L)| ≤ η * L)
    (hedge : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N L - face L - ((∑ i, A i) * L ^ 2 + (∑ i, c i) * L)| ≤ η * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N L - ((Af + ∑ i, A i) * L ^ 2 + (Bf + ∑ i, c i) * L)| ≤ η * L := by
  intro η hη
  filter_upwards [hface (η / 2) (by linarith), hedge (η / 2) (by linarith)] with L h1 h2
  have e : N L - ((Af + ∑ i, A i) * L ^ 2 + (Bf + ∑ i, c i) * L)
      = (face L - (Af * L ^ 2 + Bf * L))
        + (N L - face L - ((∑ i, A i) * L ^ 2 + (∑ i, c i) * L)) := by ring
  rw [e]
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-- **G155.** The tetrahedron two-term law from the hypotheses of G151
`tetra_edge_law_of_overlap` (six per-edge laws and an `O(ε L)` overlap, uniform in `ε`) plus the
named face input. -/
theorem tetra_law_of_overlap_and_face (N face : ℝ → ℝ) (Af Bf : ℝ) (A c : Fin 6 → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hface : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |face L - (Af * L ^ 2 + Bf * L)| ≤ η * L)
    (h : ∀ ε : ℝ, 0 < ε → ∃ Ne : Fin 6 → ℝ → ℝ,
      (∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
        |Ne e L - (A e * L ^ 2 + c e * L)| ≤ η * L) ∧
      ∀ᶠ L in atTop, |N L - face L - ∑ e, Ne e L| ≤ C * ε * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N L - ((Af + ∑ i, A i) * L ^ 2 + (Bf + ∑ i, c i) * L)| ≤ η * L :=
  tetra_law_of_face_and_edges N face Af Bf A c hface
    (SteklovAudit.TetraEdgeLawOverlap.tetra_edge_law_of_overlap N face A c C hC h)

/-- **G155.** Equal edges: the coefficients become `Af + 6 * A` and `Bf + 6 * c`. -/
theorem tetra_law_equal_edges (N face : ℝ → ℝ) (Af Bf A c C : ℝ) (hC : 0 ≤ C)
    (hface : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |face L - (Af * L ^ 2 + Bf * L)| ≤ η * L)
    (h : ∀ ε : ℝ, 0 < ε → ∃ Ne : Fin 6 → ℝ → ℝ,
      (∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
        |Ne e L - (A * L ^ 2 + c * L)| ≤ η * L) ∧
      ∀ᶠ L in atTop, |N L - face L - ∑ e, Ne e L| ≤ C * ε * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N L - ((Af + 6 * A) * L ^ 2 + (Bf + 6 * c) * L)| ≤ η * L := by
  have H := tetra_law_of_overlap_and_face N face Af Bf (fun _ => A) (fun _ => c) C hC hface h
  intro η hη
  filter_upwards [H η hη] with L hL
  have hA : (∑ _i : Fin 6, A) = 6 * A := by
    first
      | (rw [Fin.sum_univ_six]; ring)
      | simp
  have hc : (∑ _i : Fin 6, c) = 6 * c := by
    first
      | (rw [Fin.sum_univ_six]; ring)
      | simp
  first
    | (rw [hA, hc] at hL; exact hL)
    | simpa only [hA, hc] using hL
    | (simp only [hA, hc] at hL; exact hL)

end SteklovAudit.TetraAssemblyFace
