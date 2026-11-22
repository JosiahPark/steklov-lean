import Mathlib
import SteklovAudit.CumulativeBudget
import SteklovAudit.CumulativeBudgetSplit

/-!
# Quantifier and order-of-limits closure for the (7.29) budget (roadmap item G133)

`CumulativeBudget` (G120) and `CumulativeBudgetSplit` prove that a fixed-cutoff part `o(L)` plus a tail
`≤ C L / M`, with `C` uniform in `M`, gives `o(L)`. This file closes the remaining quantifier forms that
the (7.29) argument uses, all for scalar functions `r : ℝ → ℝ` and "`o(L)`" in the `η`-form
`∀ η > 0, ∀ᶠ L in atTop, |r L| ≤ η * L`.

* `littleO_of_approx`, `approx_of_littleO`, `approx_iff`: `r = o(L)` iff for every `δ > 0` there is an
  `o(L)` function `m` with eventually `|r L − m L| ≤ δ L`. This is the most general split; the cutoff
  forms below are special cases.
* `littleO_of_split_rate`: the tail constant may depend on the cutoff, `|r − m_M| ≤ c(M) L`, as long as
  `c(M) → 0` as `M → ∞`. (`C/M` with `C` uniform is the case `c(M) = C/M`; `C_M = M`, i.e. `c ≡ 1`, fails
  by `CumulativeBudget.order_of_limits_matters`.)
* `littleO_of_split_nat`: it suffices to have the split for integer cutoffs `M = 1, 2, 3, …`.
* `littleO_of_window_defect`, `littleO_of_window_defect'`: the two-parameter shape behind (7.29) after
  G129/G130. If for every Fourier window `T > 0`, eventually
  `|r L| ≤ C L / T + K T L ε(1/L)` with `C, K ≥ 0` independent of `T` and `ε(h) → 0` as `h ↓ 0`
  (only `ε h ≤ δ` is used), then `r = o(L)`: fix `T` first, then let `L → ∞`.
* `window_needs_vanishing`: the condition `ε → 0` cannot be dropped (`ε ≡ 1`, `r L = L`).

What this file does NOT prove: any of these bounds for the actual localized tetrahedron–wedge error, the
uniform tail `C L / M` or `C L / T`, the HS defect bound `ε(h) → 0` (Lemma 7.1′ / (7.2)), the Duhamel or
Tauberian steps for the Dirichlet-to-Neumann operator, Proposition 7.3, (7.29), H5, or Theorem 1.3 / 11.1.
Everything here is real analysis of scalar functions.
-/

namespace SteklovAudit.CumulativeBudgetQuantifiers

open Filter

/-- **G133.** If every `δ > 0` has an `o(L)` approximant `m` with eventually `|r L − m L| ≤ δ L`,
then `r = o(L)` (`η`-form). -/
theorem littleO_of_approx (r : ℝ → ℝ)
    (h : ∀ δ : ℝ, 0 < δ → ∃ m : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |m L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |r L - m L| ≤ δ * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L := by
  intro η hη
  obtain ⟨m, hm, hrm⟩ := h (η / 2) (by linarith)
  filter_upwards [hm (η / 2) (by linarith), hrm] with L h1 h2
  have h3 := abs_sub_abs_le_abs_sub (r L) (m L)
  linarith

/-- Converse of `littleO_of_approx`: an `o(L)` function is its own approximant. -/
theorem approx_of_littleO (r : ℝ → ℝ)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L) :
    ∀ δ : ℝ, 0 < δ → ∃ m : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |m L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |r L - m L| ≤ δ * L := by
  intro δ hδ
  refine ⟨r, h, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  rw [sub_self, abs_zero]
  exact mul_nonneg hδ.le hL

/-- **G133.** The approximation form is equivalent to `r = o(L)`. -/
theorem approx_iff (r : ℝ → ℝ) :
    (∀ δ : ℝ, 0 < δ → ∃ m : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |m L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |r L - m L| ≤ δ * L) ↔
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L) :=
  ⟨littleO_of_approx r, approx_of_littleO r⟩

/-- **G133.** Split with a cutoff-dependent tail rate: for every `M > 0` a fixed-`M` part `o(L)` and a tail
`|r − m_M| ≤ c(M) L`, where `c(M) → 0` as `M → ∞`. Then `r = o(L)`. -/
theorem littleO_of_split_rate (r : ℝ → ℝ) (c : ℝ → ℝ)
    (hc : Tendsto c atTop (nhds 0))
    (h : ∀ M : ℝ, 0 < M → ∃ m : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |m L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |r L - m L| ≤ c M * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L := by
  apply littleO_of_approx r
  intro δ hδ
  have hnear : ∀ᶠ x in nhds (0 : ℝ), x < δ := by
    first
      | exact gt_mem_nhds hδ
      | exact Iio_mem_nhds hδ
  have hev : ∀ᶠ M in atTop, c M < δ ∧ 0 < M :=
    (hc.eventually hnear).and (eventually_gt_atTop 0)
  obtain ⟨M, hcM, hM⟩ := hev.exists
  obtain ⟨m, hm, hrm⟩ := h M hM
  refine ⟨m, hm, ?_⟩
  filter_upwards [hrm, eventually_ge_atTop (0 : ℝ)] with L h1 hL
  exact h1.trans (mul_le_mul_of_nonneg_right hcM.le hL)

/-- **G133.** Integer cutoffs suffice: the split of `CumulativeBudgetSplit.littleO_of_split` for
`M = 1, 2, 3, …` only (tail `C L / M`, `C` uniform in `M`) gives `r = o(L)`. -/
theorem littleO_of_split_nat (r : ℝ → ℝ) (C : ℝ)
    (h : ∀ M : ℕ, 1 ≤ M → ∃ m : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |m L| ≤ η * L) ∧
        ∀ᶠ L in atTop, |r L - m L| ≤ C * L / (M : ℝ)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L := by
  apply littleO_of_approx r
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (C / δ)
  obtain ⟨m, hm, hrm⟩ := h (N + 1) (Nat.le_add_left 1 N)
  refine ⟨m, hm, ?_⟩
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    first
      | positivity
      | exact_mod_cast Nat.succ_pos N
  have hlt : C / δ < ((N + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hCd : C < ((N + 1 : ℕ) : ℝ) * δ := by
    first
      | exact (div_lt_iff₀ hδ).1 hlt
      | exact (div_lt_iff hδ).1 hlt
  filter_upwards [hrm, eventually_ge_atTop (0 : ℝ)] with L h1 hL
  have h2 : C * L / ((N + 1 : ℕ) : ℝ) ≤ δ * L := by
    first
      | (rw [div_le_iff₀ hpos]; nlinarith [mul_le_mul_of_nonneg_right hCd.le hL])
      | (rw [div_le_iff hpos]; nlinarith [mul_le_mul_of_nonneg_right hCd.le hL])
  exact h1.trans h2

/-- **G133.** Two-parameter window bound behind (7.29): if for every window `T > 0`, eventually
`|r L| ≤ C L / T + K T L ε(1/L)`, with `C, K ≥ 0` independent of `T` and `ε(h) → 0` as `h ↓ 0`
(only the upper bound `ε h ≤ δ` is used), then `r = o(L)` (`η`-form). The window `T` is fixed before
`L → ∞`. -/
theorem littleO_of_window_defect (r : ℝ → ℝ) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (ε : ℝ → ℝ)
    (hε : ∀ δ : ℝ, 0 < δ → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ε h ≤ δ)
    (hr : ∀ T : ℝ, 0 < T → ∀ᶠ L in atTop, |r L| ≤ C * L / T + K * T * L * ε (1 / L)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L := by
  intro η hη
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 2 * (C + 1) / η := ⟨_, rfl⟩
  have hC2 : (0 : ℝ) < 2 * (C + 1) := by linarith
  have hT : 0 < T := by
    rw [hTdef]
    exact div_pos hC2 hη
  have hKT : 0 < 2 * (K + 1) * T := by
    have hK1 : (0 : ℝ) < 2 * (K + 1) := by linarith
    exact mul_pos hK1 hT
  have hq0 : 0 < η / (2 * (K + 1) * T) := div_pos hη hKT
  have hq : η / (2 * (K + 1) * T) * (2 * (K + 1) * T) = η := by
    first
      | exact div_mul_cancel₀ η hKT.ne'
      | exact div_mul_cancel η hKT.ne'
      | (field_simp [hKT.ne'])
  obtain ⟨h₀, hh₀, hεh⟩ := hε (η / (2 * (K + 1) * T)) hq0
  filter_upwards [hr T hT, eventually_ge_atTop (max 1 (1 / h₀))] with L hL hLge
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hLge
  have hL0 : 0 < L := by linarith
  have hinv : 1 / L ≤ h₀ := by
    have h1 : 1 / h₀ ≤ L := le_trans (le_max_right _ _) hLge
    first
      | exact (one_div_le hL0 hh₀).2 h1
      | (rw [div_le_iff₀ hL0]; rw [div_le_iff₀ hh₀] at h1; linarith)
  have hinvpos : 0 < 1 / L := one_div_pos.mpr hL0
  have hεL : ε (1 / L) ≤ η / (2 * (K + 1) * T) := hεh (1 / L) hinvpos hinv
  -- the window term
  have t1 : C * L / T ≤ η / 2 * L := by
    have e : C * L / T = C * L * η / (2 * (C + 1)) := by
      rw [hTdef, div_div_eq_mul_div]
    rw [e]
    have hηL : 0 < η * L := mul_pos hη hL0
    first
      | (rw [div_le_iff₀ hC2]; nlinarith [hηL])
      | (rw [div_le_iff hC2]; nlinarith [hηL])
  -- the defect term
  have t2 : K * T * L * ε (1 / L) ≤ η / 2 * L := by
    have hKTL : 0 ≤ K * T * L := mul_nonneg (mul_nonneg hK hT.le) hL0.le
    have key : η / 2 * L =
        K * T * L * (η / (2 * (K + 1) * T)) + η / (2 * (K + 1) * T) * T * L := by
      linear_combination (-(L / 2)) * hq
    have hextra : 0 ≤ η / (2 * (K + 1) * T) * T * L :=
      mul_nonneg (mul_nonneg hq0.le hT.le) hL0.le
    calc K * T * L * ε (1 / L) ≤ K * T * L * (η / (2 * (K + 1) * T)) :=
          mul_le_mul_of_nonneg_left hεL hKTL
      _ ≤ K * T * L * (η / (2 * (K + 1) * T)) + η / (2 * (K + 1) * T) * T * L :=
          le_add_of_nonneg_right hextra
      _ = η / 2 * L := key.symm
  linarith

/-- `littleO_of_window_defect` in `Asymptotics.IsLittleO` form. -/
theorem littleO_of_window_defect' (r : ℝ → ℝ) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (ε : ℝ → ℝ)
    (hε : ∀ δ : ℝ, 0 < δ → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ε h ≤ δ)
    (hr : ∀ T : ℝ, 0 < T → ∀ᶠ L in atTop, |r L| ≤ C * L / T + K * T * L * ε (1 / L)) :
    r =o[atTop] (fun L : ℝ => L) := by
  refine Asymptotics.IsLittleO.of_bound fun η hη => ?_
  filter_upwards [littleO_of_window_defect r C K hC hK ε hε hr η hη,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  show ‖r L‖ ≤ η * ‖L‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0]
  exact hL

/-- The vanishing of `ε` cannot be dropped: with `C = K = 1`, `ε ≡ 1` and `r L = L`, the window bound
`|L| ≤ 1 · L / T + 1 · T · L · 1` holds eventually for every `T > 0` (since `1/T + T ≥ 1`), yet `r` is
not `o(L)`. -/
theorem window_needs_vanishing :
    (∀ T : ℝ, 0 < T → ∀ᶠ L in atTop, |L| ≤ 1 * L / T + 1 * T * L * 1) ∧
      ¬ ((fun L : ℝ => L) =o[atTop] (fun L : ℝ => L)) := by
  refine ⟨fun T hT => ?_, SteklovAudit.CumulativeBudget.order_of_limits_matters.2⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  simp only [one_mul, mul_one]
  rw [abs_of_nonneg hL]
  have hdiv : 0 ≤ L / T := div_nonneg hL hT.le
  have hTL : 0 ≤ T * L := mul_nonneg hT.le hL
  by_cases hT1 : 1 ≤ T
  · have h1 : L ≤ T * L := by nlinarith [mul_le_mul_of_nonneg_right hT1 hL]
    linarith
  · push_neg at hT1
    have h1 : L ≤ L / T := by
      first
        | (rw [le_div_iff₀ hT]; nlinarith [mul_le_mul_of_nonneg_left hT1.le hL])
        | (rw [le_div_iff hT]; nlinarith [mul_le_mul_of_nonneg_left hT1.le hL])
    linarith

end SteklovAudit.CumulativeBudgetQuantifiers
