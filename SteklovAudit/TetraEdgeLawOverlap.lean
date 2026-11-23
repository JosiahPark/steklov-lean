import Mathlib
import SteklovAudit.ModelEdgeLawSixEdges
import SteklovAudit.ModelEdgeLawGammaFamily

/-!
# Tetrahedron edge law from six edge laws and a shrinking collar overlap (roadmap item G151)

Scalar form of the assembly step in (7.45): the edge part of the tetrahedron count, `N L - face L`,
differs from the sum of six localized edge counts `Ne e L` by a vertex-collar overlap error. If, for
every collar parameter `ε > 0`, the six localized counts obey the per-edge laws
`Ne e L = A e * L ^ 2 + c e * L + o(L)` and the overlap error is at most `C * ε * L` eventually (with
`C ≥ 0` uniform in `ε`), then `N L - face L = (∑ A e) * L ^ 2 + (∑ c e) * L + o(L)`. "`o(L)`" is the
`η`-form `∀ η > 0, ∀ᶠ L in atTop, |r L| ≤ η * L` of `CumulativeBudgetQuantifiers`.

* `tetra_edge_law_of_overlap`: the reduction (G149 `six_edge_law` per `ε`, then G148
  `edge_law_of_gamma_family` with `γ := ε`).
* `overlap_must_shrink`: an `ε`-independent overlap `1 · L` fits the hypothesis shape (with `N L = L`,
  `face = 0`, `Ne = 0`, `A = c = 0`) while the conclusion fails, so the shrinking of the overlap with
  `ε` is a genuine input.

What this file does NOT prove: the overlap bound near the vertices (the H3/H4 geometry), the per-edge
law for any operator, the face term H6, the vertex term H4, the splitting H1, (7.29), (7.38)/(7.45),
(9.1), (11.3), H5, or Theorem 1.3 / 11.1. Everything here is real analysis of scalar functions; every
input is an explicit hypothesis.
-/

namespace SteklovAudit.TetraEdgeLawOverlap

open Filter

/-- **G151.** Six per-edge laws plus an `O(ε L)` vertex-collar overlap, with constant uniform in the
collar parameter `ε`, give the tetrahedron edge law. -/
theorem tetra_edge_law_of_overlap (N face : ℝ → ℝ) (A c : Fin 6 → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ∃ Ne : Fin 6 → ℝ → ℝ,
      (∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
        |Ne e L - (A e * L ^ 2 + c e * L)| ≤ η * L) ∧
      ∀ᶠ L in atTop, |N L - face L - ∑ e, Ne e L| ≤ C * ε * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N L - face L - ((∑ e, A e) * L ^ 2 + (∑ e, c e) * L)| ≤ η * L := by
  apply SteklovAudit.ModelEdgeLawGammaFamily.edge_law_of_gamma_family
    (fun L => N L - face L) (fun L => (∑ e, A e) * L ^ 2 + (∑ e, c e) * L) C hC
  intro γ hγ
  obtain ⟨Ne, hNe, hov⟩ := h γ hγ
  refine ⟨fun L => ∑ e, Ne e L - ((∑ e, A e) * L ^ 2 + (∑ e, c e) * L),
    SteklovAudit.ModelEdgeLawSixEdges.six_edge_law Ne A c hNe, ?_⟩
  filter_upwards [hov] with L hL
  have e1 : N L - face L - ((∑ e, A e) * L ^ 2 + (∑ e, c e) * L)
      - (∑ e, Ne e L - ((∑ e, A e) * L ^ 2 + (∑ e, c e) * L))
      = N L - face L - ∑ e, Ne e L := by ring
  show |N L - face L - ((∑ e, A e) * L ^ 2 + (∑ e, c e) * L)
      - (∑ e, Ne e L - ((∑ e, A e) * L ^ 2 + (∑ e, c e) * L))| ≤ C * γ * L
  rw [e1]
  exact hL

/-- **G151.** The overlap must shrink with `ε`: an `ε`-independent overlap `1 · L` fits the hypothesis
shape of `tetra_edge_law_of_overlap` (with `N L = L`, `face = 0`, `Ne = 0`, `A = c = 0`), but the
conclusion fails. -/
theorem overlap_must_shrink :
    (∀ ε : ℝ, 0 < ε → ∃ Ne : Fin 6 → ℝ → ℝ,
      (∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
        |Ne e L - ((0 : ℝ) * L ^ 2 + (0 : ℝ) * L)| ≤ η * L) ∧
      ∀ᶠ L in atTop, |L - 0 - ∑ e, Ne e L| ≤ 1 * L) ∧
    ¬ (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |L - 0 - ((∑ _e : Fin 6, (0 : ℝ)) * L ^ 2 + (∑ _e : Fin 6, (0 : ℝ)) * L)| ≤ η * L) := by
  refine ⟨fun ε _ => ⟨fun _ _ => 0, fun e η hη => ?_, ?_⟩, ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |(0 : ℝ) - ((0 : ℝ) * L ^ 2 + (0 : ℝ) * L)| ≤ η * L
    have e0 : (0 : ℝ) - ((0 : ℝ) * L ^ 2 + (0 : ℝ) * L) = 0 := by ring
    rw [e0, abs_zero]
    exact mul_nonneg hη.le hL
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |L - 0 - ∑ _e : Fin 6, (0 : ℝ)| ≤ 1 * L
    have e3 : L - 0 - ∑ _e : Fin 6, (0 : ℝ) = L := by
      first
        | simp
        | (rw [Finset.sum_const_zero]; ring)
    rw [e3, one_mul, abs_of_nonneg hL]
  · intro hcon
    obtain ⟨L, hL, hL0⟩ :=
      ((hcon (1 / 2) (by norm_num)).and (eventually_gt_atTop (0 : ℝ))).exists
    have e2 : L - 0 - ((∑ _e : Fin 6, (0 : ℝ)) * L ^ 2 + (∑ _e : Fin 6, (0 : ℝ)) * L) = L := by
      first
        | simp
        | (rw [Finset.sum_const_zero]; ring)
    rw [e2, abs_of_pos hL0] at hL
    linarith

end SteklovAudit.TetraEdgeLawOverlap
