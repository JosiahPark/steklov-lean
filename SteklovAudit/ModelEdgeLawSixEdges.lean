import Mathlib

/-!
# Six edge laws sum to the tetrahedron edge count (roadmap item G149)

Scalar form of the passage from the per-edge law (11.3)/(7.38) to the tetrahedron count in (7.45):
if each of the six edges `e : Fin 6` contributes `N e L = A e * L ^ 2 + c e * L + o(L)`, then the sum
over the six edges equals `(∑ A e) * L ^ 2 + (∑ c e) * L + o(L)`. "`o(L)`" is the `η`-form
`∀ η > 0, ∀ᶠ L in atTop, |r L| ≤ η * L` used in `CumulativeBudgetQuantifiers`.

* `finset_sum_littleO`: a `Finset` sum of `η`-form `o(L)` functions is `o(L)` (split `η` as
  `η / (s.card + 1)` and use `Filter.eventually_all_finset`).
* `six_edge_law`: the six per-edge laws sum to the tetrahedron law with summed coefficients.
* `six_equal_edges`: for congruent edges the coefficients become `6 * A` and `6 * c`.

What this file does NOT prove: the per-edge law itself for any operator, the overlap of the edge
collars near the vertices (the geometric input for passing from localized counts to the global
count), the vertex term H4, the face term H6, the splitting H1, (7.29), (7.38)/(7.45), (9.1), (11.3),
H5, or Theorem 1.3 / 11.1. Everything here is real analysis of scalar functions; all inputs are
explicit hypotheses.
-/

namespace SteklovAudit.ModelEdgeLawSixEdges

open Filter

/-- **G149.** A finite sum of `η`-form `o(L)` functions is `o(L)`. -/
theorem finset_sum_littleO {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |f i L| ≤ η * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |∑ i ∈ s, f i L| ≤ η * L := by
  intro η hη
  have hn : (0 : ℝ) < (s.card : ℝ) + 1 := by positivity
  have hne : (s.card : ℝ) + 1 ≠ 0 := hn.ne'
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = η / ((s.card : ℝ) + 1) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact div_pos hη hn
  have hq : ((s.card : ℝ) + 1) * δ = η := by
    rw [hδdef]
    first
      | exact mul_div_cancel₀ η hne
      | field_simp
      | exact mul_div_cancel' η hne
  have hcδ : (s.card : ℝ) * δ = η - δ := by linear_combination hq
  have h4 : (s.card : ℝ) * δ ≤ η := by linarith
  have hall : ∀ᶠ L in atTop, ∀ i ∈ s, |f i L| ≤ δ * L := by
    first
      | exact (Filter.eventually_all_finset s).2 (fun i hi => hf i hi δ hδ)
      | exact Filter.eventually_all_finset.2 (fun i hi => hf i hi δ hδ)
      | exact (Finset.eventually_all s).2 (fun i hi => hf i hi δ hδ)
  filter_upwards [hall, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  have h1 : |∑ i ∈ s, f i L| ≤ ∑ i ∈ s, |f i L| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ i ∈ s, |f i L| ≤ ∑ i ∈ s, δ * L := Finset.sum_le_sum hL
  have h3 : ∑ i ∈ s, δ * L = (s.card : ℝ) * (δ * L) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  calc |∑ i ∈ s, f i L| ≤ (s.card : ℝ) * (δ * L) := by linarith
    _ = ((s.card : ℝ) * δ) * L := by ring
    _ ≤ η * L := mul_le_mul_of_nonneg_right h4 hL0

/-- **G149.** Six per-edge laws `N e L = A e L² + c e L + o(L)` sum to the tetrahedron law with the
summed coefficients. -/
theorem six_edge_law (N : Fin 6 → ℝ → ℝ) (A c : Fin 6 → ℝ)
    (h : ∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N e L - (A e * L ^ 2 + c e * L)| ≤ η * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |∑ e, N e L - ((∑ e, A e) * L ^ 2 + (∑ e, c e) * L)| ≤ η * L := by
  intro η hη
  have hs : ∀ᶠ L in atTop, |∑ e, (N e L - (A e * L ^ 2 + c e * L))| ≤ η * L :=
    finset_sum_littleO Finset.univ (fun e L => N e L - (A e * L ^ 2 + c e * L))
      (fun e _ => h e) η hη
  filter_upwards [hs] with L hL
  have e1 : ∑ e, N e L - ((∑ e, A e) * L ^ 2 + (∑ e, c e) * L)
      = ∑ e, (N e L - (A e * L ^ 2 + c e * L)) := by
    first
      | simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
      | rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  rw [e1]
  exact hL

/-- **G149.** Congruent edges: with common coefficients `A`, `c` the tetrahedron law has
coefficients `6 * A` and `6 * c`. -/
theorem six_equal_edges (N : Fin 6 → ℝ → ℝ) (A c : ℝ)
    (h : ∀ e : Fin 6, ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |N e L - (A * L ^ 2 + c * L)| ≤ η * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |∑ e, N e L - ((6 * A) * L ^ 2 + (6 * c) * L)| ≤ η * L := by
  intro η hη
  have hs : ∀ᶠ L in atTop,
      |∑ e, N e L - ((∑ _e : Fin 6, A) * L ^ 2 + (∑ _e : Fin 6, c) * L)| ≤ η * L :=
    six_edge_law N (fun _ => A) (fun _ => c) h η hη
  have hA : (∑ _e : Fin 6, A) = 6 * A := by
    first
      | simp
      | (rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num)
  have hc : (∑ _e : Fin 6, c) = 6 * c := by
    first
      | simp
      | (rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num)
  rw [hA, hc] at hs
  exact hs

end SteklovAudit.ModelEdgeLawSixEdges
