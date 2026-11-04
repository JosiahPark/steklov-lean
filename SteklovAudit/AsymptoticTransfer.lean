import Mathlib
import SteklovAudit

/-!
# E12: asymptotic counting transfer from the raw two-sided inequalities (continuations 33/34)

Roadmap item E12, a variant of E6/E8 (`SharpLawTransfer`, `RpowScale`). There the lower inequality is
assumed already shifted, `N_A(L − δ) ≤ N_B(L) + E(L) + G(L)`; here it is taken exactly as
`counting_two_sided` gives it, at threshold `L − δ`, with its error terms evaluated at `L − δ`.
`SpectralCounting.counting_two_sided` (E1) gives, at every finite cutoff and every
shift `δ > 0`, the two transfer inequalities
`N_B(L) ≤ N_A(L + δ) + E₁(L) + δ⁻² H₁(L)` and `N_A(L) ≤ N_B(L + δ) + E₂(L) + δ⁻² H₂(L)`,
where `E` is the isometry defect `Σ (1 − ‖J e‖²)` and `H` the localized `‖K P‖²_HS`. Proved here,
for a family indexed by `L` (the count functions and error terms are arbitrary real functions):

* `law_of_shifted_bounds`: if `N_A = aL² + bL + o(L)`, the shift `δ(L) → 0`, the remainders are
  `o(L)`, `N_B(L) ≤ N_A(L + δ(L)) + R₁(L)` and `N_A(L − δ(L)) ≤ N_B(L) + R₂(L)`, then
  `N_B = aL² + bL + o(L)` (same `a`, `b`);
* `rpow_little_o`: `L^γ = o(L)` for `γ < 1`; `rpow_neg_small`: `L^{−β} → 0` for `β > 0`;
* `asymptotic_transfer`: with `δ = L^{−β}`, `0 < β`, `α + 2β < 1`, isometry defects `o(L)` and
  `0 ≤ H(L) ≤ C L^α` for `L ≥ 1` (`α ≥ 0`), the two transfer inequalities give the same sharp law
  for `N_B`.

What this file does NOT prove: the defect bound `‖K P‖²_HS = O(L^α)` with `α < 1`, the isometry
defect `o(L)`, or the model law for the tetrahedral Steklov operator; these are inputs. It does not
prove the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.AsymptoticTransfer

open SteklovAudit Filter

/-- `o(L)` in the explicit form used throughout the project. -/
def LittleO (R : ℝ → ℝ) : Prop := ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |R L| ≤ η * L

/-- Shifted two-sided bounds transfer the sharp law. -/
theorem law_of_shifted_bounds (NA NB δ R₁ R₂ : ℝ → ℝ) (a b : ℝ)
    (hA : HasSharpRealLaw NA a b)
    (hδ : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → 0 ≤ δ L ∧ δ L ≤ η)
    (hR₁ : LittleO R₁) (hR₂ : LittleO R₂)
    (hup : ∀ L, NB L ≤ NA (L + δ L) + R₁ L)
    (hlow : ∀ L, NA (L - δ L) ≤ NB L + R₂ L) :
    HasSharpRealLaw NB a b := by
  intro ε hε
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 3 * |a| + |b| + 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by linarith [abs_nonneg a, abs_nonneg b]
  have hM0 : M ≠ 0 := by linarith
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ, η' = min 1 (ε / (2 * M)) := ⟨_, rfl⟩
  have hη'pos : 0 < η' := by rw [hη']; exact lt_min one_pos (div_pos hε (by linarith))
  have hη'1 : η' ≤ 1 := by rw [hη']; exact min_le_left _ _
  have hη'M : η' * M ≤ ε / 2 := by
    have h1 : η' ≤ ε / (2 * M) := by rw [hη']; exact min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ M)
    have h3 : ε / (2 * M) * M = ε / 2 := by
      first
        | (field_simp; done)
        | (field_simp; ring)
        | (rw [div_mul_eq_mul_div, mul_comm 2 M, ← div_div, mul_div_assoc, div_self hM0, mul_one])
    linarith
  have hη : (0 : ℝ) < ε / 6 := by linarith
  obtain ⟨LA, hLA0, hLA⟩ := hA (ε / 6) hη
  obtain ⟨Lδ, hLδ⟩ := hδ η' hη'pos
  obtain ⟨L1, hL1⟩ := hR₁ (ε / 6) hη
  obtain ⟨L2, hL2⟩ := hR₂ (ε / 6) hη
  have hmax0 : (0 : ℝ) ≤ max (max (LA + 1) Lδ) (max (max L1 L2) 1) :=
    le_trans zero_le_one (le_trans (le_max_right (max L1 L2) 1) (le_max_right _ _))
  refine ⟨max (max (LA + 1) Lδ) (max (max L1 L2) 1), hmax0, ?_⟩
  intro L hL
  have hLA1 : LA + 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLδL : Lδ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL1L : L1 ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hL
  have hL2L : L2 ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hL
  have hL1' : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hd0, hdη⟩ := hLδ L hLδL
  have u := hup L
  have w := hlow L
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = δ L := ⟨_, rfl⟩
  rw [← hd] at u w hd0 hdη
  have hd1 : d ≤ 1 := le_trans hdη hη'1
  have eU := abs_le.mp (hLA (L + d) (by linarith))
  have eL := abs_le.mp (hLA (L - d) (by linarith))
  have r1 := abs_le.mp (hL1 L hL1L)
  have r2 := abs_le.mp (hL2 L hL2L)
  unfold realWeylPolynomial at eU eL ⊢
  have hdd : d * d ≤ d := by
    have := mul_le_mul_of_nonneg_left hd1 hd0
    linarith
  have hη'L : η' ≤ η' * L := by
    have := mul_le_mul_of_nonneg_left hL1' hη'pos.le
    linarith
  have hLd : d ≤ η' * L := le_trans hdη hη'L
  have hLdη : L * d ≤ L * η' := mul_le_mul_of_nonneg_left hdη hL0
  have hLd0 : 0 ≤ L * d := mul_nonneg hL0 hd0
  have hdd0 : 0 ≤ d * d := mul_nonneg hd0 hd0
  have ht0 : 0 ≤ 2 * L * d + d * d := by linarith
  have hLd2 : 2 * L * d + d * d ≤ 3 * (η' * L) := by linarith
  have hA1 : a * (2 * L * d + d * d) ≤ |a| * (2 * L * d + d * d) :=
    mul_le_mul_of_nonneg_right (le_abs_self a) ht0
  have hs : |(-(2 * L * d) + d * d)| ≤ 2 * L * d + d * d :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hA2 : -(|a| * (2 * L * d + d * d)) ≤ a * (-(2 * L * d) + d * d) := by
    have h1 := neg_abs_le (a * (-(2 * L * d) + d * d))
    rw [abs_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left hs (abs_nonneg a)
    linarith
  have hAb : |a| * (2 * L * d + d * d) ≤ |a| * (3 * (η' * L)) :=
    mul_le_mul_of_nonneg_left hLd2 (abs_nonneg a)
  have hB1 : b * d ≤ |b| * (η' * L) := by
    have h1 : b * d ≤ |b| * d := mul_le_mul_of_nonneg_right (le_abs_self b) hd0
    have h2 : |b| * d ≤ |b| * (η' * L) := mul_le_mul_of_nonneg_left hLd (abs_nonneg b)
    linarith
  have hB2 : -(|b| * (η' * L)) ≤ b * d := by
    have h1 : -|b| * d ≤ b * d := mul_le_mul_of_nonneg_right (neg_abs_le b) hd0
    have h2 : |b| * d ≤ |b| * (η' * L) := mul_le_mul_of_nonneg_left hLd (abs_nonneg b)
    linarith
  have hML : (3 * |a| + |b|) * (η' * L) ≤ ε / 2 * L := by
    have h1 : (3 * |a| + |b|) * η' ≤ M * η' :=
      mul_le_mul_of_nonneg_right (by linarith) hη'pos.le
    have h3 : (3 * |a| + |b|) * η' ≤ ε / 2 := by linarith
    have h4 := mul_le_mul_of_nonneg_right h3 hL0
    linarith
  have hdL : ε / 6 * d ≤ ε / 6 * L := mul_le_mul_of_nonneg_left (by linarith) hη.le
  have hdL0 : 0 ≤ ε / 6 * d := mul_nonneg hη.le hd0
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- `L^γ = o(L)` for `γ < 1`. -/
theorem rpow_little_o (γ : ℝ) (hγ : γ < 1) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → 0 < L ∧ L ^ γ ≤ η * L := by
  intro η hη
  have ht : Tendsto (fun x : ℝ => x ^ (-(1 - γ))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hev : ∀ᶠ x : ℝ in atTop, x ^ (-(1 - γ)) < η := (tendsto_order.1 ht).2 η hη
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 hev
  refine ⟨max L₁ 1, fun L hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hL)
  refine ⟨hLpos, ?_⟩
  have h1 := hL₁ L (le_trans (le_max_left _ _) hL)
  have e : L ^ γ = L ^ (-(1 - γ)) * L := by
    rw [← Real.rpow_add_one hLpos.ne']
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right h1.le hLpos.le

/-- `L^{−β} → 0` for `β > 0`, with nonnegativity. -/
theorem rpow_neg_small (β : ℝ) (hβ : 0 < β) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → 0 ≤ L ^ (-β) ∧ L ^ (-β) ≤ η := by
  intro η hη
  have ht : Tendsto (fun x : ℝ => x ^ (-β)) atTop (nhds 0) := tendsto_rpow_neg_atTop hβ
  have hev : ∀ᶠ x : ℝ in atTop, x ^ (-β) < η := (tendsto_order.1 ht).2 η hη
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 hev
  refine ⟨max L₁ 1, fun L hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hL)
  exact ⟨Real.rpow_nonneg hLpos.le _, (hL₁ L (le_trans (le_max_left _ _) hL)).le⟩

/-- `H / (L^{−β})² ≤ C L^{α + 2β}` when `0 ≤ H ≤ C L^α`. -/
theorem defect_over_shift (H C α β L : ℝ) (hL : 0 < L) (hH : H ≤ C * L ^ α) :
    H / (L ^ (-β)) ^ 2 ≤ C * L ^ (α + 2 * β) := by
  have hp : 0 < (L ^ (-β)) ^ 2 := pow_pos (Real.rpow_pos_of_pos hL _) 2
  have e1 : (L ^ (-β)) ^ 2 = L ^ (-(2 * β)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    push_cast
    ring
  have e2 : L ^ (α + 2 * β) * L ^ (-(2 * β)) = L ^ α := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  rw [div_le_iff₀ hp, e1, mul_assoc, e2]
  exact hH

/-- **E12.** Asymptotic counting transfer with the shift `δ = L^{−β}`. -/
theorem asymptotic_transfer (NA NB E₁ E₂ H₁ H₂ : ℝ → ℝ) (a b C α β : ℝ)
    (hα : 0 ≤ α) (hβ : 0 < β) (hαβ : α + 2 * β < 1) (hC : 0 ≤ C)
    (hA : HasSharpRealLaw NA a b) (hE₁ : LittleO E₁) (hE₂ : LittleO E₂)
    (hH₁ : ∀ L, 1 ≤ L → 0 ≤ H₁ L ∧ H₁ L ≤ C * L ^ α)
    (hH₂ : ∀ L, 1 ≤ L → 0 ≤ H₂ L ∧ H₂ L ≤ C * L ^ α)
    (hup : ∀ L δ, 0 < δ → NB L ≤ NA (L + δ) + E₁ L + H₁ L / δ ^ 2)
    (hlow : ∀ L δ, 0 < δ → NA L ≤ NB (L + δ) + E₂ L + H₂ L / δ ^ 2) :
    HasSharpRealLaw NB a b := by
  set δ : ℝ → ℝ := fun L => L ^ (-β) with hδdef
  -- remainders
  set R₁ : ℝ → ℝ := fun L => if 1 ≤ L then E₁ L + H₁ L / δ L ^ 2 else NB L - NA (L + δ L)
    with hR₁def
  set R₂ : ℝ → ℝ := fun L =>
    if 2 ≤ L then E₂ (L - δ L) + H₂ (L - δ L) / δ L ^ 2 else NA (L - δ L) - NB L with hR₂def
  have hpow := rpow_little_o (α + 2 * β) hαβ
  have hR₁ : LittleO R₁ := by
    intro η hη
    obtain ⟨LE, hLE⟩ := hE₁ (η / 2) (by linarith)
    obtain ⟨LP, hLP⟩ := hpow (η / 2 / (C + 1)) (div_pos (by linarith) (by linarith))
    refine ⟨max (max LE LP) 1, fun L hL => ?_⟩
    have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
    have hLpos : 0 < L := by linarith
    have hR : R₁ L = E₁ L + H₁ L / δ L ^ 2 := by simp [hR₁def, hL1]
    rw [hR]
    have e := hLE L (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL)
    obtain ⟨_, hp⟩ := hLP L (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL)
    obtain ⟨hH0, hH⟩ := hH₁ L hL1
    have hq0 : 0 ≤ H₁ L / δ L ^ 2 := div_nonneg hH0 (sq_nonneg _)
    have hq : H₁ L / δ L ^ 2 ≤ C * L ^ (α + 2 * β) := defect_over_shift (H₁ L) C α β L hLpos hH
    have hq2 : C * L ^ (α + 2 * β) ≤ (C + 1) * L ^ (α + 2 * β) := by
      have : 0 ≤ L ^ (α + 2 * β) := Real.rpow_nonneg hLpos.le _
      linarith
    have hq3 : (C + 1) * L ^ (α + 2 * β) ≤ η / 2 * L := by
      have h1 := mul_le_mul_of_nonneg_left hp (by linarith : (0 : ℝ) ≤ C + 1)
      have hC1 : C + 1 ≠ 0 := (by linarith : (0 : ℝ) < C + 1).ne'
      have h2 : (C + 1) * (η / 2 / (C + 1) * L) = η / 2 * L := by
        first
          | (field_simp; done)
          | (field_simp; ring)
          | (rw [← mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hC1])
      linarith
    rw [abs_le] at e ⊢
    constructor <;> linarith [e.1, e.2]
  have hR₂ : LittleO R₂ := by
    intro η hη
    obtain ⟨LE, hLE⟩ := hE₂ (η / 2) (by linarith)
    obtain ⟨LP, hLP⟩ := hpow (η / 2 / (C + 1)) (div_pos (by linarith) (by linarith))
    refine ⟨max (max (LE + 1) LP) 2, fun L hL => ?_⟩
    have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
    have hLpos : 0 < L := by linarith
    have hR : R₂ L = E₂ (L - δ L) + H₂ (L - δ L) / δ L ^ 2 := by simp [hR₂def, hL2]
    rw [hR]
    have hδ0 : 0 < δ L := Real.rpow_pos_of_pos hLpos _
    have hδ1 : δ L ≤ 1 := by
      show L ^ (-β) ≤ 1
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hM1 : 1 ≤ L - δ L := by linarith
    have hLEL : LE + 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
    have e := hLE (L - δ L) (by linarith)
    obtain ⟨_, hp⟩ := hLP L (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL)
    obtain ⟨hH0, hH⟩ := hH₂ (L - δ L) hM1
    have hmono : C * (L - δ L) ^ α ≤ C * L ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) hα) hC
    have hq0 : 0 ≤ H₂ (L - δ L) / δ L ^ 2 := div_nonneg hH0 (sq_nonneg _)
    have hq : H₂ (L - δ L) / δ L ^ 2 ≤ C * L ^ (α + 2 * β) :=
      defect_over_shift (H₂ (L - δ L)) C α β L hLpos (le_trans hH hmono)
    have hq2 : C * L ^ (α + 2 * β) ≤ (C + 1) * L ^ (α + 2 * β) := by
      have : 0 ≤ L ^ (α + 2 * β) := Real.rpow_nonneg hLpos.le _
      linarith
    have hq3 : (C + 1) * L ^ (α + 2 * β) ≤ η / 2 * L := by
      have h1 := mul_le_mul_of_nonneg_left hp (by linarith : (0 : ℝ) ≤ C + 1)
      have hC1 : C + 1 ≠ 0 := (by linarith : (0 : ℝ) < C + 1).ne'
      have h2 : (C + 1) * (η / 2 / (C + 1) * L) = η / 2 * L := by
        first
          | (field_simp; done)
          | (field_simp; ring)
          | (rw [← mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hC1])
      linarith
    have hEL : η / 2 * (L - δ L) ≤ η / 2 * L := by
      have := mul_le_mul_of_nonneg_left (by linarith : L - δ L ≤ L) (by linarith : (0 : ℝ) ≤ η / 2)
      linarith
    rw [abs_le] at e ⊢
    constructor <;> linarith [e.1, e.2]
  have hδ : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → 0 ≤ δ L ∧ δ L ≤ η :=
    rpow_neg_small β hβ
  refine law_of_shifted_bounds NA NB δ R₁ R₂ a b hA hδ hR₁ hR₂ ?_ ?_
  · intro L
    by_cases hL : 1 ≤ L
    · have hLpos : 0 < L := by linarith
      have hR : R₁ L = E₁ L + H₁ L / δ L ^ 2 := by simp [hR₁def, hL]
      rw [hR]
      have := hup L (δ L) (Real.rpow_pos_of_pos hLpos _)
      linarith
    · have hR : R₁ L = NB L - NA (L + δ L) := by simp [hR₁def, hL]
      rw [hR]
      linarith
  · intro L
    by_cases hL : 2 ≤ L
    · have hLpos : 0 < L := by linarith
      have hR : R₂ L = E₂ (L - δ L) + H₂ (L - δ L) / δ L ^ 2 := by simp [hR₂def, hL]
      rw [hR]
      have := hlow (L - δ L) (δ L) (Real.rpow_pos_of_pos hLpos _)
      rw [sub_add_cancel] at this
      linarith
    · have hR : R₂ L = NA (L - δ L) - NB L := by simp [hR₂def, hL]
      rw [hR]
      linarith

end SteklovAudit.AsymptoticTransfer
