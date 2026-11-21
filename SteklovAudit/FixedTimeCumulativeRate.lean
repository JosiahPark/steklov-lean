import Mathlib
import SteklovAudit.VertexLog

/-!
# Power-saving rate for the scalar model of (7.29)

The scalar model of the fixed-time cumulative error is `C (1 + log L) + C L ε(1/L)`
(see `Cumulative729Support.log_plus_vanishing_is_o_L`, which shows it is `o(L)`).

This file proves a power-saving version: if `ε(h) ≤ K h^β` with `K ≥ 0` and `0 < β ≤ 1`,
then for `L ≥ 1` the model is at most `(3 C + C K) L^(1 - β/2)`.

Weakening relative to the first draft: the hypothesis `β ≤ 1` is added. Without it the
claim is false for `β ≥ 2` (the right side tends to `0` while `C log L → ∞`), and the
`log L ≤ 2 √L` route only gives the exponent `1 - β/2` when `β ≤ 1`.

What this file does NOT prove:
* any Hilbert–Schmidt estimate for an actual differential operator;
* the uniform localized gluing bound (7.2) / Lemma 7.1′;
* the cumulative transfer (7.29) itself, propagation (9.1), or (7.38)/(7.45);
* any of `[H1]`–`[H6]`, or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.FixedTimeCumulativeRate

open Real

theorem log_plus_power_vanishing_is_power_saving
    (C K β : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ M L₀ : ℝ, 0 ≤ M ∧ 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      C * (1 + log L) + C * L * (K * (1 / L) ^ β) ≤ M * L ^ (1 - β / 2) := by
  refine ⟨3 * C + C * K, 1, by positivity, by norm_num, fun L hL => ?_⟩
  have hLpos : 0 < L := by linarith
  set P : ℝ := L ^ (1 - β / 2) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hL (by linarith)
  -- log term
  have hsqrt : Real.sqrt L ≤ P := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hlog := SteklovAudit.VertexLog.log_le_two_sqrt L hLpos
  have h1 : C * (1 + log L) ≤ C * (3 * P) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  -- vanishing term
  have hpow : L * (1 / L) ^ β = L ^ (1 - β) := by
    rw [Real.rpow_sub hLpos, Real.rpow_one, one_div, Real.inv_rpow hLpos.le]
    ring
  have hcomp : L ^ (1 - β) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h2 : C * L * (K * (1 / L) ^ β) ≤ C * K * P := by
    have : C * L * (K * (1 / L) ^ β) = C * K * (L * (1 / L) ^ β) := by ring
    rw [this, hpow]
    exact mul_le_mul_of_nonneg_left hcomp (mul_nonneg hC hK)
  have h3 : (3 * C + C * K) * P = C * (3 * P) + C * K * P := by ring
  linarith

end SteklovAudit.FixedTimeCumulativeRate
