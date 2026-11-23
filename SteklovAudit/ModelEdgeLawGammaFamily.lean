import Mathlib
import SteklovAudit.CumulativeBudgetQuantifiers

/-!
# The `γ`-order of limits behind (11.3)/(7.38) (roadmap item G148)

The edge law (11.3)/(7.38) is obtained with an angular cutoff `γ > 0`: for each fixed `γ` the localized
edge count equals the main term up to an `o_γ(L)` remainder plus a cutoff error `O(γ L)` whose constant
does not depend on `γ`. Sending `L → ∞` first and then `γ → 0` gives `o(L)`. This file proves that
order-of-limits step for scalar functions `N main : ℝ → ℝ`, with "`o(L)`" in the `η`-form
`∀ η > 0, ∀ᶠ L in atTop, |r L| ≤ η * L` of `CumulativeBudgetQuantifiers`.

* `edge_law_of_gamma_family`: `γ`-independent main term; `o_γ(L) + C γ L` with `C` uniform in `γ`
  gives `N − main = o(L)`.
* `edge_law_of_gamma_main`: the paper's main term depends on `γ` (through `θ_γ`); if the `γ`-main term
  differs from the limit main term by at most `C' γ L`, the same conclusion holds.
* `edge_law_of_gamma_family'`: `Asymptotics.IsLittleO` form of the first theorem.
* `gamma_term_must_shrink`: if the cutoff error does not shrink with `γ` (a `γ`-independent `1 · L`),
  the hypothesis shape holds for `N L = L`, `main = 0`, but `N − main` is not `o(L)`.

What this file does NOT prove: the per-`γ` bound itself for the actual tetrahedron or wedge
Dirichlet-to-Neumann operator, the uniformity of the cutoff constant `C` in `γ`, the identification of
the main term with `θ_γ`-integrals, (7.29), (7.38)/(7.45), (9.1), (11.3), H5, or Theorem 1.3 / 11.1.
Everything here is real analysis of scalar functions; all inputs are explicit hypotheses.
-/

namespace SteklovAudit.ModelEdgeLawGammaFamily

open Filter

/-- **G148.** `γ`-family to edge law: if for every cutoff `γ > 0` there is an `o(L)` remainder `r` with
eventually `|N L − main L − r L| ≤ C γ L` (`C ≥ 0` uniform in `γ`), then `N − main = o(L)`. -/
theorem edge_law_of_gamma_family (N main : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ γ : ℝ, 0 < γ → ∃ r : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |N L - main L - r L| ≤ C * γ * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |N L - main L| ≤ η * L := by
  apply SteklovAudit.CumulativeBudgetQuantifiers.littleO_of_approx (fun L => N L - main L)
  intro δ hδ
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hq0 : 0 < δ / (C + 1) := div_pos hδ hC1
  obtain ⟨r, hr, hNr⟩ := h (δ / (C + 1)) hq0
  refine ⟨r, hr, ?_⟩
  have hq : (C + 1) * (δ / (C + 1)) = δ := by
    first
      | exact mul_div_cancel₀ δ hC1.ne'
      | field_simp
      | exact mul_div_cancel' δ hC1.ne'
  have hCq : C * (δ / (C + 1)) = δ - δ / (C + 1) := by linear_combination hq
  have hle : C * (δ / (C + 1)) ≤ δ := by linarith
  filter_upwards [hNr, eventually_ge_atTop (0 : ℝ)] with L h1 hL
  show |N L - main L - r L| ≤ δ * L
  exact h1.trans (mul_le_mul_of_nonneg_right hle hL)

/-- `edge_law_of_gamma_family` in `Asymptotics.IsLittleO` form. -/
theorem edge_law_of_gamma_family' (N main : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ γ : ℝ, 0 < γ → ∃ r : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |N L - main L - r L| ≤ C * γ * L) :
    (fun L => N L - main L) =o[atTop] (fun L : ℝ => L) := by
  refine Asymptotics.IsLittleO.of_bound fun η hη => ?_
  filter_upwards [edge_law_of_gamma_family N main C hC h η hη,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  show ‖N L - main L‖ ≤ η * ‖L‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0]
  exact hL

/-- **G148.** `γ`-dependent main term: if for every `γ > 0` there are a main term `mγ` and an `o(L)`
remainder `r` with eventually `|N − mγ − r| ≤ C γ L` and `|mγ − main| ≤ C' γ L` (`C, C' ≥ 0` uniform in
`γ`), then `N − main = o(L)`. -/
theorem edge_law_of_gamma_main (N main : ℝ → ℝ) (C C' : ℝ) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (h : ∀ γ : ℝ, 0 < γ → ∃ mγ r : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L) ∧
        (∀ᶠ L in atTop, |N L - mγ L - r L| ≤ C * γ * L) ∧
          ∀ᶠ L in atTop, |mγ L - main L| ≤ C' * γ * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |N L - main L| ≤ η * L := by
  apply edge_law_of_gamma_family N main (C + C') (by linarith)
  intro γ hγ
  obtain ⟨mγ, r, hr, h1, h2⟩ := h γ hγ
  refine ⟨r, hr, ?_⟩
  filter_upwards [h1, h2] with L hL1 hL2
  have e : N L - main L - r L = (N L - mγ L - r L) + (mγ L - main L) := by ring
  rw [e]
  calc |(N L - mγ L - r L) + (mγ L - main L)|
      ≤ |N L - mγ L - r L| + |mγ L - main L| := by
        first
          | exact abs_add _ _
          | exact abs_add_le _ _
    _ ≤ C * γ * L + C' * γ * L := add_le_add hL1 hL2
    _ = (C + C') * γ * L := by ring

/-- **G148.** The cutoff error must shrink with `γ`: with a `γ`-independent error `1 · L`, the hypothesis
shape holds for `N L = L`, `main = 0` (remainder `r = 0`), but `N − main` is not `o(L)`. -/
theorem gamma_term_must_shrink :
    (∀ γ : ℝ, 0 < γ → ∃ r : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |L - 0 - r L| ≤ 1 * L) ∧
      ¬ (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |L - 0| ≤ η * L) := by
  refine ⟨fun γ _ => ⟨fun _ => 0, fun η hη => ?_, ?_⟩, ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |(0 : ℝ)| ≤ η * L
    rw [abs_zero]
    exact mul_nonneg hη.le hL
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |L - 0 - 0| ≤ 1 * L
    rw [sub_zero, sub_zero, one_mul, abs_of_nonneg hL]
  · intro hcon
    obtain ⟨L, hL, hL0⟩ := ((hcon (1 / 2) (by norm_num)).and (eventually_gt_atTop (0 : ℝ))).exists
    rw [sub_zero, abs_of_pos hL0] at hL
    linarith

end SteklovAudit.ModelEdgeLawGammaFamily
