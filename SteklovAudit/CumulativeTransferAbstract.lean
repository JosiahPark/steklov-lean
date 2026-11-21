import Mathlib
import SteklovAudit.VertexLog

/-!
# Abstract fixed-time cumulative transfer (towards (7.29))

Finite-dimensional scalar steps behind the passage from a uniform localized Hilbert–Schmidt bound
of size `O(1 + L)` to an `o(L)` cumulative error, once the time factor of Duhamel's formula is
kept. Everything is stated in finite spectral coordinates, as in `AbstractTransfer`; no
Dirichlet-to-Neumann operator is constructed and the analytic inputs remain named hypotheses.

* `time_factor_cancellation`: `|t| * C / |t| = C` when `|t| > 0`.
* `duhamel_time_controlled`: if `hs2 K ≤ Lip ^ 2` with `Lip ≥ 0`, then `|t| √(hs2 K) ≤ |t| Lip`.
* `vanishing_tail_gives_oL`: if for every `ε > 0` one has `|τ M| ≤ ε` for all large `M`, then for
  every `η > 0`, eventually `C (1 + log L) + C L τ(log L) ≤ η L`.

Changes relative to the first draft of this file:
* `Data` takes its index types as explicit parameters and `locCount` has an explicit finite index
  type; the draft left them unbound.
* The last statement is the eventual upper bound `≤ η L`. The draft claimed that
  `C (1 + log L) + C L τ(log L)` tends to `0`, which is false for `C > 0` because `C log L → ∞`.
  No lower bound is proved here.

`Cumulative729Support.log_plus_vanishing_is_o_L` is the same bound with `ε(1/L)` in place of
`τ(log L)`; the proof below follows it.

What this file does NOT prove:
* any Hilbert–Schmidt estimate for an actual differential operator;
* the uniform localized gluing bound (7.2);
* the cumulative transfer (7.29) itself, propagation (9.1), or (7.38)/(7.45);
* any of `[H1]`–`[H6]`, or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.CumulativeTransferAbstract

/-- Abstract spectral data at a finite cutoff (simplified from `AbstractTransfer.Data`):
eigenvalues of `A` and `B`, intertwiner coefficients `J` and defect coefficients `K`. -/
structure Data (ι κ : Type*) where
  a : ι → ℝ
  b : κ → ℝ
  J : ι → κ → ℝ
  K : ι → κ → ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Squared Hilbert–Schmidt norm of a coefficient array. -/
def hs2 (M : ι → κ → ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

/-- Weighted count of the indices whose value lies in `[0, L]`. -/
noncomputable def locCount {α : Type*} [Fintype α] (vals : α → ℝ) (L : ℝ) (w : α → ℝ) : ℝ :=
  ∑ x, (if 0 ≤ vals x ∧ vals x ≤ L then w x else 0)

/-- The time factor `|t|` cancels against the `1 / |t|` of the cumulative kernel. -/
theorem time_factor_cancellation (t : ℝ) (h : 0 < |t|) (C : ℝ) : |t| * C / |t| = C := by
  have hne : |t| ≠ 0 := h.ne'
  first
    | exact mul_div_cancel_left₀ C hne
    | (field_simp; done)
    | (field_simp; ring)
    | (rw [mul_comm, mul_div_assoc, div_self hne, mul_one])

/-- A Hilbert–Schmidt defect bound `hs2 K ≤ Lip ^ 2` gives `|t| √(hs2 K) ≤ |t| Lip`. -/
theorem duhamel_time_controlled (D : Data ι κ) (t Lip : ℝ) (hLip : 0 ≤ Lip)
    (hdef : hs2 D.K ≤ Lip ^ 2) :
    |t| * Real.sqrt (hs2 D.K) ≤ |t| * Lip := by
  have h1 := Real.sqrt_le_sqrt hdef
  rw [Real.sqrt_sq hLip] at h1
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg t)

/-- A vanishing tail gives an eventual `≤ η L` bound: if for every `ε > 0` one has `|τ M| ≤ ε` for
all large `M`, then `C (1 + log L) + C L τ(log L)` is eventually at most `η L`, for every `η > 0`. -/
theorem vanishing_tail_gives_oL (τ : ℝ → ℝ)
    (hτ : ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → |τ M| ≤ ε)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      C * (1 + Real.log L) + C * L * τ (Real.log L) ≤ η * L := by
  intro η hη
  have hC1 : 0 < C + 1 := by linarith
  have h2C1 : (0 : ℝ) < 2 * (C + 1) := by linarith
  obtain ⟨M₀, hM₀⟩ := hτ (η / (2 * (C + 1))) (div_pos hη h2C1)
  have hK : 0 < 6 * (C + 1) / η := div_pos (by linarith) hη
  refine ⟨max (max 1 ((6 * (C + 1) / η) ^ 2)) (Real.exp M₀), fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLK : (6 * (C + 1) / η) ^ 2 ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLexp : Real.exp M₀ ≤ L := le_trans (le_max_right _ _) hL
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
  -- Vanishing term: `exp M₀ ≤ L` gives `M₀ ≤ log L`, so `τ (log L) ≤ η / (2 (C + 1))`.
  have hM : M₀ ≤ Real.log L := by
    first
      | exact Real.exp_le_exp.mp (le_of_le_of_eq hLexp (Real.exp_log hLpos).symm)
      | exact (Real.le_log_iff_exp_le hLpos).mpr hLexp
      | exact Real.exp_le_exp.mp (by rw [Real.exp_log hLpos]; exact hLexp)
  have hτL : τ (Real.log L) ≤ η / (2 * (C + 1)) :=
    le_trans (le_abs_self _) (hM₀ (Real.log L) hM)
  have hτL' : τ (Real.log L) * (2 * (C + 1)) ≤ η := by
    first
      | exact (le_div_iff₀ h2C1).mp hτL
      | exact (le_div_iff h2C1).mp hτL
  have hCe : C * τ (Real.log L) ≤ η / 2 := by
    rcases le_total 0 (τ (Real.log L)) with he | he
    · nlinarith [mul_nonneg hC he]
    · nlinarith [mul_nonneg hC (neg_nonneg.mpr he)]
  have hτpart : C * L * τ (Real.log L) ≤ η / 2 * L := by
    have h1 := mul_le_mul_of_nonneg_right hCe hLpos.le
    have h2 : C * L * τ (Real.log L) = C * τ (Real.log L) * L := by ring
    linarith
  linarith

end SteklovAudit.CumulativeTransferAbstract
