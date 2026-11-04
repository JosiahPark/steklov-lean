import Mathlib
import SteklovAudit.SharpLawTransfer

/-!
# E8: the power shift `δ(L) = L^(−β)` in the sharp-law transfer

Roadmap item E8. `SharpLawTransfer.sharp_law_transfer` (E6) works at an abstract shift
`δ(L) → 0` with HS term `G(L) = o(L)`. Here the shift is `δ(L) = L^(−β)` and the HS term is
`G(L) = δ(L)⁻² · H(L)` with `|H(L)| ≤ C L^α` (the bound `‖K P‖²_HS = O(L^α)`). We prove:

* `inv_sq_rpow_neg`: `(L^(−β))⁻² = L^(2β)` for `L > 0`;
* `hs_term_bound`: `|δ⁻² H| ≤ C L^(α+2β)`;
* `power_little_o`: `C L^(α+2β) = o(L)` when `α + 2β < 1`;
* `sharp_law_transfer_power`: with `β > 0`, `α + 2β < 1` (i.e. `0 < β < (1 − α)/2`), the sharp
  law for `N_A`, defects `E = o(L)` and the two-sided comparisons at shift `L^(−β)` give the
  sharp law for `N_B`.

What this file does NOT prove: the bound `‖K P‖²_HS = O(L^α)` with `α < 1` for the tetrahedral
data (it is the hypothesis `hH`), the comparisons `hup`/`hdown` for the actual operators, any
PDE estimate, or the main theorem.
-/

namespace SteklovAudit.PowerShiftTransfer

open SteklovAudit Filter

theorem rpow_pos' {L : ℝ} (hL : 0 < L) (y : ℝ) : 0 < L ^ y := by
  first
    | exact Real.rpow_pos_of_pos hL y
    | positivity

/-- `L^(−β) ≤ 1` for `L ≥ 1`, `β ≥ 0`. -/
theorem rpow_neg_le_one {L β : ℝ} (hL : 1 ≤ L) (hβ : 0 ≤ β) : L ^ (-β) ≤ 1 := by
  first
    | exact Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
    | (rw [Real.rpow_neg (by linarith)]
       exact inv_le_one_of_one_le₀ (Real.one_le_rpow hL hβ))

/-- `L^(−γ)` is eventually below any `η > 0`. -/
theorem eventually_rpow_neg_le {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → L ^ (-γ) ≤ η := by
  have h := (tendsto_rpow_neg_atTop hγ).eventually (ge_mem_nhds hη)
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨L₀, fun L hL => hL₀ L hL⟩

/-- `(L^(−β))⁻² = L^(2β)`. -/
theorem inv_sq_rpow_neg {L β : ℝ} (hL : 0 < L) : ((L ^ (-β))⁻¹) ^ 2 = L ^ (2 * β) := by
  rw [Real.rpow_neg hL.le, inv_inv, sq, ← Real.rpow_add hL]
  congr 1
  ring

/-- The HS term at shift `L^(−β)`: `|(L^(−β))⁻² h| ≤ C L^(α+2β)` when `|h| ≤ C L^α`. -/
theorem hs_term_bound {L α β C h : ℝ} (hL : 0 < L) (hh : |h| ≤ C * L ^ α) :
    |((L ^ (-β))⁻¹) ^ 2 * h| ≤ C * L ^ (α + 2 * β) := by
  rw [abs_mul, inv_sq_rpow_neg hL, abs_of_pos (rpow_pos' hL (2 * β)), Real.rpow_add hL]
  calc L ^ (2 * β) * |h| ≤ L ^ (2 * β) * (C * L ^ α) :=
        mul_le_mul_of_nonneg_left hh (rpow_pos' hL _).le
    _ = C * (L ^ α * L ^ (2 * β)) := by ring

/-- `C L^(α+2β) = o(L)` when `α + 2β < 1`. -/
theorem power_little_o {α β C : ℝ} (hC : 0 ≤ C) (hαβ : α + 2 * β < 1) :
    ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → C * L ^ (α + 2 * β) ≤ η * L := by
  intro η hη
  have hγ : 0 < 1 - (α + 2 * β) := by linarith
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨L₀, h⟩ := eventually_rpow_neg_le hγ (div_pos hη hC1)
  refine ⟨max L₀ 1, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hx := h L (le_trans (le_max_left _ _) hL)
  have e : L ^ (α + 2 * β) = L ^ (1 : ℝ) * L ^ (-(1 - (α + 2 * β))) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  rw [Real.rpow_one] at e
  rw [e]
  have hq : C / (C + 1) ≤ 1 := by
    first
      | exact (div_le_one hC1).mpr (by linarith)
      | exact (div_le_one₀ hC1).mpr (by linarith)
      | (rw [div_le_iff₀ hC1]; linarith)
  calc C * (L * L ^ (-(1 - (α + 2 * β)))) ≤ C * (L * (η / (C + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hL0.le) hC
    _ = η * L * (C / (C + 1)) := by ring
    _ ≤ η * L * 1 := mul_le_mul_of_nonneg_left hq (mul_nonneg hη.le hL0.le)
    _ = η * L := mul_one _

/-- E8. Sharp-law transfer at the power shift `δ(L) = L^(−β)`, `0 < β`, `α + 2β < 1`.
`hH` is the named input `‖K P‖²_HS ≤ C L^α` at each cutoff; `E` is the isometry defect. -/
theorem sharp_law_transfer_power (NA NB E H : ℝ → ℝ) (A B α β C : ℝ)
    (hA : HasSharpRealLaw NA A B) (hβ : 0 < β) (hC : 0 ≤ C) (hαβ : α + 2 * β < 1)
    (hE : ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |E L| ≤ η * L)
    (hH : ∀ L, 1 ≤ L → |H L| ≤ C * L ^ α)
    (hup : ∀ L, 1 ≤ L →
      NB L ≤ NA (L + L ^ (-β)) + E L + ((L ^ (-β))⁻¹) ^ 2 * H L)
    (hdown : ∀ L, 1 ≤ L →
      NA (L - L ^ (-β)) ≤ NB L + E L + ((L ^ (-β))⁻¹) ^ 2 * H L) :
    HasSharpRealLaw NB A B := by
  refine SharpLawTransfer.sharp_law_transfer NA NB E
    (fun L => ((L ^ (-β))⁻¹) ^ 2 * H L) (fun L => L ^ (-β)) A B hA
    (fun L hL => rpow_pos' (by linarith) _)
    (fun L hL => rpow_neg_le_one hL hβ.le)
    (fun η hη => eventually_rpow_neg_le hβ hη)
    hE ?_ hup hdown
  intro η hη
  obtain ⟨L₀, h⟩ := power_little_o hC hαβ η hη
  refine ⟨max L₀ 1, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  exact le_trans (hs_term_bound (by linarith) (hH L hL1)) (h L (le_trans (le_max_left _ _) hL))

end SteklovAudit.PowerShiftTransfer
