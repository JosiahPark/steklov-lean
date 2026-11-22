import Mathlib
import SteklovAudit.CumulativeBudget

/-!
# Order of limits for (7.29): fixed-cutoff part plus uniform tail

The (7.29) argument splits the localized error at a fixed cutoff `M` into a part `m_M` that is `o(L)`
for that fixed `M` (with an `M`-dependent threshold in `L`), and a tail bounded by `C L / M` with ONE
constant `C` independent of `M`. `littleO_of_split` proves that this gives `r = o(L)` (choose `M` with
`C / M ≤ η / 2`, then let `L → ∞`). `littleO_of_split'` states it with `Asymptotics.IsLittleO`.
`G120` (`CumulativeBudget.tail_littleO_of_cutoff_bound`) is the special case `m_M = 0`.
`split_needs_uniform_C` records, via `CumulativeBudget.order_of_limits_matters`, that an `M`-dependent
constant would not suffice.

What this file does NOT prove: the split itself for the actual localized tetrahedron–wedge error, the
uniform tail bound `C L / M`, the fixed-`M` estimate, (7.29), H5, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.CumulativeBudgetSplit

open Filter

/-- Fixed-cutoff part `o(L)` for each `M`, plus a tail `≤ C L / M` with `C` uniform in `M`,
gives `r = o(L)` in `η`-form. -/
theorem littleO_of_split (r : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ M : ℝ, 0 < M → ∃ m : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |m L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |r L - m L| ≤ C * L / M) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L := by
  intro η hη
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hM : 0 < 2 * (C + 1) / η := by positivity
  obtain ⟨m, hm, hrm⟩ := h _ hM
  filter_upwards [hm (η / 2) (by linarith), hrm, eventually_ge_atTop (0 : ℝ)] with L h1 h2 hL
  have hηL : 0 ≤ η * L := mul_nonneg hη.le hL
  have key : C * L / (2 * (C + 1) / η) ≤ η / 2 * L := by
    rw [div_div_eq_mul_div]
    have hden : (0 : ℝ) < 2 * (C + 1) := by linarith
    first
      | (rw [div_le_iff₀ hden]; nlinarith)
      | (rw [div_le_iff hden]; nlinarith)
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

/-- `littleO_of_split` in `Asymptotics.IsLittleO` form. -/
theorem littleO_of_split' (r : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ M : ℝ, 0 < M → ∃ m : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |m L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |r L - m L| ≤ C * L / M) :
    r =o[atTop] (fun L : ℝ => L) := by
  refine Asymptotics.IsLittleO.of_bound fun η hη => ?_
  filter_upwards [littleO_of_split r C hC h η hη, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  show ‖r L‖ ≤ η * ‖L‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0]
  exact hL

/-- G120 is the case `m_M = 0` of the split. -/
theorem split_of_cutoff_bound (r : ℝ → ℝ) (C : ℝ)
    (h : ∀ M : ℝ, 0 < M → ∀ᶠ L in atTop, |r L| ≤ C * L / M) :
    ∀ M : ℝ, 0 < M → ∃ m : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |m L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |r L - m L| ≤ C * L / M := by
  intro M hM
  refine ⟨fun _ => 0, fun η hη => ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    simpa using mul_nonneg hη.le hL
  · filter_upwards [h M hM] with L hL
    simpa using hL

/-- The uniformity of `C` in `M` cannot be dropped: with `r L = L` and `C_M = M` every fixed-`M`
tail bound holds, yet `r` is not `o(L)` (from `CumulativeBudget.order_of_limits_matters`). -/
theorem split_needs_uniform_C :
    (∀ M : ℝ, 0 < M → ∀ᶠ L in atTop, |(fun L : ℝ => L) L - 0| ≤ M * L / M) ∧
      ¬ ((fun L : ℝ => L) =o[atTop] (fun L : ℝ => L)) := by
  obtain ⟨h1, h2⟩ := SteklovAudit.CumulativeBudget.order_of_limits_matters
  refine ⟨fun M hM => ?_, h2⟩
  filter_upwards [h1 M hM] with L hL
  simpa using hL

end SteklovAudit.CumulativeBudgetSplit
