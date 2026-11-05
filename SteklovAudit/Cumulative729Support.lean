import Mathlib
import SteklovAudit.VertexLog

/-!
# The `C (1 + log L) + C L ε(1/L) = o(L)` step of the cumulative transfer (7.29)

Model of the scalar bound that appears in the proof of (7.29) once the time factor of Duhamel's
formula is kept and the observation time is fixed: a logarithmic term `C (1 + log L)` plus a term
`C L ε(1/L)` with `ε(h) → 0` as `h ↓ 0`. This file proves that the sum is `o(L)`:

* `log_plus_vanishing_is_o_L`: for every `η > 0`, eventually
  `C (1 + log L) + C L ε(1/L) ≤ η L`.

The log term is handled by `VertexLog.log_le_two_sqrt`. The energy-split step
(vanishing high-energy tail plus `o(L)` low-energy remainder) is already
`little_o_of_vanishing_tail` in `AbstractTransferB.lean` and is not repeated here.

What this file does NOT prove:
* any Hilbert–Schmidt estimate for an actual differential operator;
* the uniform localized gluing bound (7.2);
* the cumulative transfer (7.29) itself;
* propagation (9.1) or the wedge coefficient identities (7.38)/(7.45);
* any of `[H1]`–`[H6]`, or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.Cumulative729Support

/-- Model of the bound in the proof of (7.29): `C (1 + log L) + C L ε(1/L)` is `o(L)` when
`C ≥ 0` and `ε(h) → 0` as `h ↓ 0`. No sign condition on `ε` is needed. -/
theorem log_plus_vanishing_is_o_L (C : ℝ) (hC : 0 ≤ C) (ε : ℝ → ℝ)
    (hε : ∀ δ : ℝ, 0 < δ → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ε h ≤ δ) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      C * (1 + Real.log L) + C * L * ε (1 / L) ≤ η * L := by
  intro η hη
  have hC1 : 0 < C + 1 := by linarith
  have h2C1 : (0 : ℝ) < 2 * (C + 1) := by linarith
  obtain ⟨h₀, hh₀, hεh⟩ := hε (η / (2 * (C + 1))) (div_pos hη h2C1)
  have hK : 0 < 6 * (C + 1) / η := div_pos (by linarith) hη
  refine ⟨max (max 1 ((6 * (C + 1) / η) ^ 2)) (1 / h₀), fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLK : (6 * (C + 1) / η) ^ 2 ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLh : 1 / h₀ ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := by linarith
  -- Logarithmic term: `C (1 + log L) ≤ (η / 2) L`, via `log L ≤ 2 √L` and `√L ≥ 6 (C + 1) / η`.
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hs1 : 1 ≤ Real.sqrt L := by
    have h1 := Real.sqrt_le_sqrt hL1
    rwa [Real.sqrt_one] at h1
  have hsK : 6 * (C + 1) / η ≤ Real.sqrt L := by
    have h1 := Real.sqrt_le_sqrt hLK
    rwa [Real.sqrt_sq hK.le] at h1
  have hηs : 6 * (C + 1) ≤ Real.sqrt L * η := by
    first
      | exact (div_le_iff₀ hη).mp hsK
      | exact (div_le_iff hη).mp hsK
  have hlog := SteklovAudit.VertexLog.log_le_two_sqrt L hLpos
  have hA : C * (1 + Real.log L) ≤ C * (1 + 2 * Real.sqrt L) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have hB : 0 ≤ C * (Real.sqrt L - 1) := mul_nonneg hC (by linarith)
  have hD : 6 * (C + 1) * Real.sqrt L ≤ Real.sqrt L * η * Real.sqrt L :=
    mul_le_mul_of_nonneg_right hηs hs
  have hE : Real.sqrt L * η * Real.sqrt L = η * L := by
    linear_combination η * hss
  have hlogpart : C * (1 + Real.log L) ≤ η / 2 * L := by
    nlinarith [hA, hB, hD, hE, hs]
  -- Vanishing term: `1 / L ≤ h₀`, so `ε (1 / L) ≤ η / (2 (C + 1))`, so `C L ε(1/L) ≤ (η / 2) L`.
  have hinv : 1 / L ≤ h₀ := by
    first
      | exact (one_div_le hh₀ hLpos).mp hLh
      | (rw [div_le_iff₀ hLpos]; rw [div_le_iff₀ hh₀] at hLh; nlinarith)
  have hεL := hεh (1 / L) (one_div_pos.mpr hLpos) hinv
  have hεL' : ε (1 / L) * (2 * (C + 1)) ≤ η := by
    first
      | exact (le_div_iff₀ h2C1).mp hεL
      | exact (le_div_iff h2C1).mp hεL
  have hCe : C * ε (1 / L) ≤ η / 2 := by
    rcases le_or_lt 0 (ε (1 / L)) with he | he
    · nlinarith [mul_nonneg hC he]
    · nlinarith [mul_nonneg hC (neg_nonneg.mpr he.le)]
  have hεpart : C * L * ε (1 / L) ≤ η / 2 * L := by
    have h1 := mul_le_mul_of_nonneg_right hCe hLpos.le
    have h2 : C * L * ε (1 / L) = C * ε (1 / L) * L := by ring
    linarith
  linarith

end SteklovAudit.Cumulative729Support
