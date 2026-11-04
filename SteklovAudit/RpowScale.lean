import Mathlib
import SteklovAudit.SharpLawTransfer

/-!
# Roadmap item E8: the `L ^ (-β)` scale for the sharp-law transfer

This file instantiates the abstract `sharp_law_transfer` with the concrete window
`δ L = L ^ (-β)` (real power, `β > 0`) and a Hilbert–Schmidt-type error term
`G L = H L / (L ^ (-β)) ^ 2` with `0 ≤ H L ≤ C * L ^ α`, `α + 2β < 1`.

What this file does NOT prove: it constructs no Steklov operator, proves no
Hilbert–Schmidt or commutator estimate (the bound on `H` is a hypothesis), and does
not prove the main theorem. It is purely the real-analysis bookkeeping that the
scale `L ^ (-β)` satisfies the hypotheses of `sharp_law_transfer`.
-/

namespace SteklovAudit.RpowScale

open SteklovAudit SteklovAudit.SharpLawTransfer
open Filter Topology

/-- For `L ≥ 1`, the window `L ^ (-β)` is positive. -/
theorem rpow_neg_pos (β : ℝ) {L : ℝ} (hL : 1 ≤ L) : 0 < L ^ (-β) :=
  Real.rpow_pos_of_pos (by linarith) _

/-- For `L ≥ 1` and `β > 0`, the window `L ^ (-β)` is at most `1`. -/
theorem rpow_neg_le_one {β : ℝ} (hβ : 0 < β) {L : ℝ} (hL : 1 ≤ L) : L ^ (-β) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)

/-- `L ^ (-γ)` is eventually below any positive threshold. -/
theorem eventually_rpow_neg_le {γ : ℝ} (hγ : 0 < γ) {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → L ^ (-γ) ≤ η := by
  have ht := tendsto_rpow_neg_atTop hγ
  have hev : ∀ᶠ x in Filter.atTop, x ^ (-γ) < η := (tendsto_order.1 ht).2 η hη
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 hev
  exact ⟨L₀, fun L hL => (hL₀ L hL).le⟩

/-- The Hilbert–Schmidt-type term `H L / (L ^ (-β)) ^ 2` is `o(L)`. -/
theorem hs_term_littleO (H : ℝ → ℝ) (C α β : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hβ : 0 < β) (hαβ : α + 2 * β < 1)
    (hH : ∀ L, 1 ≤ L → 0 ≤ H L ∧ H L ≤ C * L ^ α) :
    ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |H L / (L ^ (-β)) ^ 2| ≤ η * L := by
  intro η hη
  have hγ : 0 < 1 - α - 2 * β := by linarith
  have hC1 : 0 < C + 1 := by linarith
  have hq : 0 < η / (C + 1) := div_pos hη hC1
  obtain ⟨L₁, hL₁⟩ := eventually_rpow_neg_le hγ hq
  refine ⟨max 1 L₁, fun L hL => ?_⟩
  have h1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := by linarith
  have hsmall : L ^ (-(1 - α - 2 * β)) ≤ η / (C + 1) := hL₁ L (le_trans (le_max_right _ _) hL)
  obtain ⟨hH0, hHC⟩ := hH L h1
  have hp : 0 < L ^ (-β + -β) := Real.rpow_pos_of_pos hLpos _
  have hsq : (L ^ (-β)) ^ 2 = L ^ (-β + -β) := by
    rw [Real.rpow_add hLpos, sq]
  have hexp : L ^ (-(1 - α - 2 * β)) * L * L ^ (-β + -β) = L ^ α := by
    have e1 : L ^ (-(1 - α - 2 * β) + 1 + (-β + -β))
        = L ^ (-(1 - α - 2 * β) + 1) * L ^ (-β + -β) := Real.rpow_add hLpos _ _
    have e2 : L ^ (-(1 - α - 2 * β) + 1) = L ^ (-(1 - α - 2 * β)) * L := by
      rw [Real.rpow_add hLpos, Real.rpow_one]
    have e3 : -(1 - α - 2 * β) + 1 + (-β + -β) = α := by ring
    rw [← e2, ← e1, e3]
  have hLp : 0 ≤ L * L ^ (-β + -β) := (mul_pos hLpos hp).le
  have hCq : C * (η / (C + 1)) ≤ η := by
    have hne : C + 1 ≠ 0 := hC1.ne'
    have hcancel : (C + 1) * (η / (C + 1)) = η := by
      first
        | (field_simp; done)
        | (field_simp; ring)
        | (rw [mul_comm]; exact div_mul_cancel₀ η hne)
    nlinarith [hcancel, hq]
  have key : H L ≤ (η * L) * L ^ (-β + -β) := by
    calc H L ≤ C * L ^ α := hHC
      _ = C * L ^ (-(1 - α - 2 * β)) * (L * L ^ (-β + -β)) := by rw [← hexp]; ring
      _ ≤ C * (η / (C + 1)) * (L * L ^ (-β + -β)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hC) hLp
      _ ≤ η * (L * L ^ (-β + -β)) := mul_le_mul_of_nonneg_right hCq hLp
      _ = (η * L) * L ^ (-β + -β) := by ring
  have hG0 : 0 ≤ H L / (L ^ (-β)) ^ 2 := div_nonneg hH0 (by positivity)
  rw [abs_of_nonneg hG0, hsq]
  first
    | exact (div_le_iff₀ hp).2 key
    | exact (div_le_iff hp).2 key

/-- Sharp-law transfer at the concrete scale `δ L = L ^ (-β)`. -/
theorem sharp_law_transfer_rpow (NA NB E H : ℝ → ℝ) (A B C α β : ℝ)
    (hA : HasSharpRealLaw NA A B) (hC : 0 ≤ C) (hα : 0 ≤ α) (hβ : 0 < β)
    (hαβ : α + 2 * β < 1)
    (hH : ∀ L, 1 ≤ L → 0 ≤ H L ∧ H L ≤ C * L ^ α)
    (hE : ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |E L| ≤ η * L)
    (hup : ∀ L, 1 ≤ L → NB L ≤ NA (L + L ^ (-β)) + E L + H L / (L ^ (-β)) ^ 2)
    (hdown : ∀ L, 1 ≤ L → NA (L - L ^ (-β)) ≤ NB L + E L + H L / (L ^ (-β)) ^ 2) :
    HasSharpRealLaw NB A B :=
  sharp_law_transfer NA NB E (fun L => H L / (L ^ (-β)) ^ 2) (fun L => L ^ (-β)) A B hA
    (fun _ hL => rpow_neg_pos β hL)
    (fun _ hL => rpow_neg_le_one hβ hL)
    (fun _ hη => eventually_rpow_neg_le hβ hη)
    hE
    (hs_term_littleO H C α β hC hα hβ hαβ hH)
    hup hdown

end SteklovAudit.RpowScale
