import Mathlib

/-!
# Abstract fixed-time cumulative error budget (supporting (7.29))

Elementary real-analysis pieces for the order of limits in the cumulative argument behind (7.29).

Main result (`tail_littleO_of_cutoff_bound`, roadmap item G120): if an error `r L` satisfies, for every
fixed cutoff `M > 0`, the eventual bound `|r L| ≤ C * L / M` with ONE constant `C` independent of `M`
(the threshold in `L` may depend on `M`), then `r L = o(L)`. Proof: given `η > 0`, take `M = (C + 1) / η`.
`order_of_limits_matters` shows that the uniformity of `C` in `M` cannot be dropped.

What this file does NOT prove: the uniform bound `|r L| ≤ C * L / M` for the actual localized
tetrahedron–wedge error, Proposition 7.3, (7.29) itself, or anything about the Dirichlet-to-Neumann
operator. Applying these lemmas to (7.29) requires that operator estimate, which is open.
-/

namespace SteklovAudit.CumulativeBudget

/-- Literally an associativity identity: `C * S * δ * L = (C * S * δ) * L`. (It is used only to
display the product as a constant times `L`; it proves no asymptotic statement.) -/
theorem uniform_defect_is_O (C S δ L : ℝ) :
    C * S * δ * L = (C * S * δ) * L := by
  ring

/-- `η`-form of G120: if for every fixed `M > 0` eventually `|r L| ≤ C * L / M`, with `C ≥ 0`
independent of `M`, then for every `η > 0` eventually `|r L| ≤ η * L`. -/
theorem tail_eta_form (r : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ M : ℝ, 0 < M → ∀ᶠ L in Filter.atTop, |r L| ≤ C * L / M) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in Filter.atTop, |r L| ≤ η * L := by
  intro η hη
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hM : 0 < (C + 1) / η := div_pos hC1 hη
  filter_upwards [h _ hM, Filter.eventually_ge_atTop (0 : ℝ)] with L hL hL0
  have key : C * L / ((C + 1) / η) = C / (C + 1) * (η * L) := by
    rw [div_div_eq_mul_div]
    ring
  have hfrac : C / (C + 1) ≤ 1 := by
    first
      | exact (div_le_one hC1).2 (by linarith)
      | exact (div_le_one₀ hC1).2 (by linarith)
      | exact div_le_one_of_le₀ (by linarith) hC1.le
  have hηL : 0 ≤ η * L := mul_nonneg hη.le hL0
  calc |r L| ≤ C * L / ((C + 1) / η) := hL
    _ = C / (C + 1) * (η * L) := key
    _ ≤ 1 * (η * L) := mul_le_mul_of_nonneg_right hfrac hηL
    _ = η * L := one_mul _

/-- **G120.** An error bounded by `C * L / M` eventually, for every fixed `M > 0`, with `C`
independent of `M`, is `o(L)`. -/
theorem tail_littleO_of_cutoff_bound (r : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ M : ℝ, 0 < M → ∀ᶠ L in Filter.atTop, |r L| ≤ C * L / M) :
    r =o[Filter.atTop] (fun L : ℝ => L) := by
  refine Asymptotics.IsLittleO.of_bound fun η hη => ?_
  filter_upwards [tail_eta_form r C hC h η hη, Filter.eventually_ge_atTop (0 : ℝ)] with L hL hL0
  show ‖r L‖ ≤ η * ‖L‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0]
  exact hL

/-- Strengthened form of the earlier statement (which proved only `(C / L) * L → C`): under the
G120 hypothesis, `r L / L → 0`. -/
theorem tail_over_M_is_o (C : ℝ) (hC : 0 ≤ C) (r : ℝ → ℝ)
    (h : ∀ M : ℝ, 0 < M → ∀ᶠ L in Filter.atTop, |r L| ≤ C * L / M) :
    Filter.Tendsto (fun L => r L / L) Filter.atTop (nhds 0) :=
  (tail_littleO_of_cutoff_bound r C hC h).tendsto_div_nhds_zero

/-- The constant must be uniform in `M`. With `r L = L` and the `M`-dependent constant `C_M = M`,
the bound `|r L| ≤ C_M * L / M` holds eventually for every `M > 0`, but `r` is not `o(L)`. -/
theorem order_of_limits_matters :
    (∀ M : ℝ, 0 < M → ∀ᶠ L in Filter.atTop, |(fun L : ℝ => L) L| ≤ M * L / M) ∧
      ¬ ((fun L : ℝ => L) =o[Filter.atTop] (fun L : ℝ => L)) := by
  constructor
  · intro M hM
    have hM' : M ≠ 0 := hM.ne'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with L hL
    show |L| ≤ M * L / M
    have e : M * L / M = L := by field_simp
    rw [e, abs_of_nonneg hL]
  · intro hlo
    have h2 := hlo.def (by norm_num : (0 : ℝ) < 1 / 2)
    obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 h2
    have hx := hL₀ (max L₀ 1) (le_max_left _ _)
    have h1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
    have hpos : (0 : ℝ) < max L₀ 1 := lt_of_lt_of_le one_pos h1
    simp only [Real.norm_eq_abs] at hx
    rw [abs_of_pos hpos] at hx
    linarith

/-- Literally `|S * ε| ≤ S * |ε|` for `S ≥ 0` (the Duhamel time factor pulled out of an absolute
value); no asymptotic claim. -/
theorem time_factor_preserves_o (S ε : ℝ) (hS : 0 ≤ S) :
    |S * ε| ≤ S * |ε| := by
  exact le_of_eq (by rw [abs_mul, abs_of_nonneg hS])

end SteklovAudit.CumulativeBudget
