import Mathlib
import SteklovAudit.TetraAssemblyFace

/-!
# Vertex term added to the tetrahedron assembly (roadmap item G160)

Scalar form of the vertex step in (7.45): if the vertex contribution `vert` is `o(L)` (a named
input with the H4 / (7.49) shape) and the remaining count `N - vert` obeys the two-term law of
G155 (`TetraAssemblyFace`), then `N` obeys the same law. "`o(L)`" is the `η`-form
`∀ η > 0, ∀ᶠ L in atTop, |r L| ≤ η * L` used throughout.

* `tetra_law_of_vertex_face_edges`: an `o(L)` vertex term does not change the two-term law.
* `tetra_law_of_overlap_face_vertex`: the law for `N` from the face input, six per-edge laws,
  an `O(ε L)` overlap (all applied to `N - vert`) and the vertex input.
* `vertex_must_be_littleO`: with `N = vert = (fun L => L)`, face and all coefficients `0`, the
  law holds for `N - vert` but fails for `N`; so the `o(L)` vertex input cannot be dropped.

What this file does NOT prove: (7.49), H4, the face law (Lemma 7.4 / §10.2, H6), the overlap
bound near the vertices, any per-edge law for an actual operator, (7.29), (7.38)/(7.45), (9.1),
(11.3), H1–H6, or Theorem 1.3 / 11.1. Everything here is real analysis of scalar functions;
every input is an explicit hypothesis.
-/

namespace SteklovAudit.TetraAssemblyVertex

open Filter

/-- **G160.** An `o(L)` vertex term added to a count obeying the two-term law keeps the law. -/
theorem tetra_law_of_vertex_face_edges (N vert : ℝ → ℝ) (Af Bf : ℝ) (A c : Fin 6 → ℝ)
    (hvert : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |vert L| ≤ η * L)
    (hrest : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N L - vert L - ((Af + ∑ i, A i) * L ^ 2 + (Bf + ∑ i, c i) * L)| ≤ η * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N L - ((Af + ∑ i, A i) * L ^ 2 + (Bf + ∑ i, c i) * L)| ≤ η * L := by
  intro η hη
  filter_upwards [hvert (η / 2) (by linarith), hrest (η / 2) (by linarith)] with L h1 h2
  have e : N L - ((Af + ∑ i, A i) * L ^ 2 + (Bf + ∑ i, c i) * L)
      = vert L + (N L - vert L - ((Af + ∑ i, A i) * L ^ 2 + (Bf + ∑ i, c i) * L)) := by ring
  rw [e]
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-- **G160.** The tetrahedron two-term law from the named vertex input, the named face input and
the hypotheses of G151 (six per-edge laws, `O(ε L)` overlap) applied to `N - vert`. -/
theorem tetra_law_of_overlap_face_vertex (N face vert : ℝ → ℝ) (Af Bf : ℝ) (A c : Fin 6 → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hvert : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |vert L| ≤ η * L)
    (hface : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |face L - (Af * L ^ 2 + Bf * L)| ≤ η * L)
    (h : ∀ ε : ℝ, 0 < ε → ∃ Ne : Fin 6 → ℝ → ℝ,
      (∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
        |Ne e L - (A e * L ^ 2 + c e * L)| ≤ η * L) ∧
      ∀ᶠ L in atTop, |N L - vert L - face L - ∑ e, Ne e L| ≤ C * ε * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N L - ((Af + ∑ i, A i) * L ^ 2 + (Bf + ∑ i, c i) * L)| ≤ η * L :=
  tetra_law_of_vertex_face_edges N vert Af Bf A c hvert
    (SteklovAudit.TetraAssemblyFace.tetra_law_of_overlap_and_face
      (fun L => N L - vert L) face Af Bf A c C hC hface h)

/-- **G160.** The vertex input cannot be dropped: for `N = vert = (fun L => L)`, face `0` and all
coefficients `0`, the law holds for `N - vert` (first conjunct, the `hrest` hypothesis above) but
fails for `N` (second conjunct). -/
theorem vertex_must_be_littleO :
    (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |L - L - ((0 + ∑ _i : Fin 6, (0 : ℝ)) * L ^ 2 + (0 + ∑ _i : Fin 6, (0 : ℝ)) * L)| ≤ η * L) ∧
    ¬ (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |L - ((0 + ∑ _i : Fin 6, (0 : ℝ)) * L ^ 2 + (0 + ∑ _i : Fin 6, (0 : ℝ)) * L)| ≤ η * L) := by
  have hs : (∑ _i : Fin 6, (0 : ℝ)) = 0 := by simp
  constructor
  · intro η hη
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    rw [hs]
    have e : L - L - ((0 + 0) * L ^ 2 + (0 + 0) * L) = 0 := by ring
    rw [e, abs_zero]
    exact mul_nonneg hη.le hL
  · intro H
    obtain ⟨L, hL, hpos⟩ :=
      ((H (1 / 2) (by norm_num)).and (eventually_gt_atTop (0 : ℝ))).exists
    rw [hs] at hL
    have e : L - ((0 + 0) * L ^ 2 + (0 + 0) * L) = L := by ring
    rw [e, abs_of_pos hpos] at hL
    linarith

end SteklovAudit.TetraAssemblyVertex
