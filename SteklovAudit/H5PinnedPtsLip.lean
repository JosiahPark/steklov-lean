import Mathlib
import SteklovAudit.AbstractTransferB
import SteklovAudit.H5PinnedDataRows

/-!
# G111: the Lipschitz row is needed only at the pinned spectral points

Roadmap item G111. `H5bPinnedPtsRows nA nB D₀ F₀` is `H5bPinnedDataRows` (G109) with the global
Lipschitz row `lip` replaced by `lipPts`: for `L ≥ 1`, `|F₀ aᵢ − F₀ bⱼ| ≤ Λ |aᵢ − bⱼ|` only at the
pinned spectral points of `D₀ ε γ L`.

* `trace_transfer_pts`: the `trace_transfer` bound under `lipPts` at one `L ≥ 1`.
* `ofDataRows`: global Lipschitz data rows give point rows.
* `sumLittleO_of_ptsRows`: the point rows still force `SumLittleO D₀ F₀` (Cauchy–Schwarz
  `abs_pair_le_sqrt`, then `sqrt_lin_prod` and `scale_le` as in `H5GlobalLipRows.toGlobalLip`).
* `h5b_of_ptsRows`: point rows plus the `o(L)` cutoff row give the target (7.29).

F table text: the row "Lipschitz-type bounds Λ" is needed only on the pinned spectral points, for
`L ≥ 1`.

What this file does NOT prove: no row is proved for any operator; `D₀`, `F₀` are arbitrary given data.
No DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5PinnedPtsLip

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5GlobalLipRows
  SteklovAudit.H5PinnedRows SteklovAudit.H5PinnedCutoffVanish SteklovAudit.H5PinnedSumSmall
  SteklovAudit.H5PinnedDataRows

/-- The data rows with the Lipschitz row weakened to the pinned spectral points, for `L ≥ 1`. -/
structure H5bPinnedPtsRows (nA nB : ℝ → ℝ → ℝ → ℕ)
    (D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F₀ : ℝ → ℝ → ℝ → ℝ → ℝ) where
  Λ : ℝ → ℝ → ℝ
  hΛ : ∀ ε γ, 0 ≤ Λ ε γ
  lipPts : ∀ ε γ L : ℝ, 1 ≤ L → ∀ i j, |F₀ ε γ L ((D₀ ε γ L).a i) - F₀ ε γ L ((D₀ ε γ L).b j)| ≤
    Λ ε γ * |(D₀ ε γ L).a i - (D₀ ε γ L).b j|
  m : ℝ → ℝ → ℝ
  hm : ∀ ε γ, 0 ≤ m ε γ
  massLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D₀ ε γ L).J ≤ m ε γ * L
  δ : ℝ → ℝ → ℝ → ℝ
  defectLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D₀ ε γ L).K ≤ δ ε γ L * L
  δVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    δ ε γ L ≤ η

variable {E Emod : ℝ → ℝ → ℝ → ℝ} {nA nB : ℝ → ℝ → ℝ → ℕ}
  {D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))} {F₀ : ℝ → ℝ → ℝ → ℝ → ℝ}

/-- **G111.** The `trace_transfer` bound needs `lipPts` only. -/
theorem trace_transfer_pts (R : H5bPinnedPtsRows nA nB D₀ F₀) (ε γ L : ℝ) (hL : 1 ≤ L) :
    |pinnedSum D₀ F₀ ε γ L| ≤
      R.Λ ε γ * ∑ i, ∑ j, |(D₀ ε γ L).K i j| * |(D₀ ε γ L).J i j| := by
  unfold pinnedSum
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    term_le (D₀ ε γ L) (F₀ ε γ L) (R.Λ ε γ) i j (R.lipPts ε γ L hL i j)

/-- **G111.** Global Lipschitz data rows give point rows. -/
def ofDataRows (R : H5bPinnedDataRows nA nB D₀ F₀) : H5bPinnedPtsRows nA nB D₀ F₀ where
  Λ := R.Λ
  hΛ := R.hΛ
  lipPts := fun ε γ L _ _ _ => R.lip ε γ L _ _
  m := R.m
  hm := R.hm
  massLin := R.massLin
  δ := R.δ
  defectLin := R.defectLin
  δVanish := R.δVanish

theorem ofDataRows_Λ (R : H5bPinnedDataRows nA nB D₀ F₀) : (ofDataRows R).Λ = R.Λ := rfl

/-- **G111.** Point rows force the data's spectral sum to be `o(L)`. -/
theorem sumLittleO_of_ptsRows (R : H5bPinnedPtsRows nA nB D₀ F₀) : SumLittleO D₀ F₀ := by
  intro ε γ hε hγ η hη
  have hs := scale_le (R.hΛ ε γ) (Real.sqrt_nonneg (R.m ε γ)) hη
  have hc : 0 < (R.Λ ε γ + 1) * (Real.sqrt (R.m ε γ) + 1) :=
    mul_pos (by linarith [R.hΛ ε γ]) (by linarith [Real.sqrt_nonneg (R.m ε γ)])
  have ht0 : 0 < η / ((R.Λ ε γ + 1) * (Real.sqrt (R.m ε γ) + 1)) := div_pos hη hc
  set t := η / ((R.Λ ε γ + 1) * (Real.sqrt (R.m ε γ) + 1)) with ht_def
  obtain ⟨L₀, hL₀⟩ := R.δVanish ε γ hε hγ (t ^ 2) (pow_pos ht0 2)
  refine ⟨max 1 L₀, fun L hL => ?_⟩
  have h1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have h2 : L₀ ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 ≤ L := by linarith
  have hmain := sqrt_lin_prod hL0 (R.defectLin ε γ L h1) (R.massLin ε γ L h1)
    (hs2_nonneg _) (hs2_nonneg _) (hL₀ L h2) ht0.le (R.hm ε γ) (R.hΛ ε γ)
  have htr := trace_transfer_pts R ε γ L h1
  have hcs := mul_le_mul_of_nonneg_left
    (abs_pair_le_sqrt (D₀ ε γ L).K (D₀ ε γ L).J) (R.hΛ ε γ)
  calc |pinnedSum D₀ F₀ ε γ L|
      ≤ R.Λ ε γ * ∑ i, ∑ j, |(D₀ ε γ L).K i j| * |(D₀ ε γ L).J i j| := htr
    _ ≤ R.Λ ε γ * Real.sqrt (hs2 (D₀ ε γ L).K * hs2 (D₀ ε γ L).J) := hcs
    _ ≤ R.Λ ε γ * (t * Real.sqrt (R.m ε γ) * L) := hmain
    _ = (R.Λ ε γ * Real.sqrt (R.m ε γ) * t) * L := by ring
    _ ≤ η * L := mul_le_mul_of_nonneg_right hs hL0

/-- **G111.** Point rows and the `o(L)` cutoff row give the target (7.29). -/
theorem h5b_of_ptsRows (R : H5bPinnedPtsRows nA nB D₀ F₀)
    (hc : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      coreDisc E Emod nA nB D₀ F₀ ε γ L ≤ η * L) :
    H5bTarget E Emod := by
  intro ε γ hε hγ η hη
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨L₀, h₀⟩ := hc ε γ hε hγ (η / 2) hη2
  obtain ⟨L₁, h₁⟩ := sumLittleO_of_ptsRows R ε γ hε hγ (η / 2) hη2
  refine ⟨max L₀ L₁, fun L hL => ?_⟩
  have ha : |(E ε γ L - Emod ε γ L) - pinnedSum D₀ F₀ ε γ L| ≤ η / 2 * L :=
    h₀ L (le_trans (le_max_left _ _) hL)
  have hb : |pinnedSum D₀ F₀ ε γ L| ≤ η / 2 * L := h₁ L (le_trans (le_max_right _ _) hL)
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SteklovAudit.H5PinnedPtsLip
