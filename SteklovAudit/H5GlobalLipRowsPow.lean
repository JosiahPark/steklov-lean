import Mathlib
import SteklovAudit.H5GlobalLipRowsEv

/-!
# G98: the G94 rows with a power trade-off between mass and defect

Roadmap item G98. `H5bGlobalLipRowsPow E Emod` has the fields of `H5bGlobalLipRowsEv`
(G94, `H5GlobalLipRowsEv.lean`) except `massEv` and `defectSmall`, which are replaced by an
exponent `p ε γ ∈ [0, 2]` and
* `massPow`: for each `ε γ`, eventually in `L`, `hs2 J ≤ m ε γ * L ^ (p ε γ)` (`Real.rpow`), and
* `defectPow`: for every `η > 0`, eventually `hs2 K ≤ η * L ^ (2 - p ε γ)`.
The two rows may trade powers of `L`: only the product `L ^ p * L ^ (2 - p) = L * L`
(`rpow_split`) enters. `ofEv` shows the G94 rows are the case `p = 1`; `toGlobalLipPow`
derives the G86 inputs, and `h5b_of_globalLipRowsPow` gives `H5bTarget E Emod`.

F table text: the mass and defect rows may trade powers of `L` (`O(L^p)` mass with
`o(L^(2-p))` defect, `0 ≤ p ≤ 2`); `p = 1` is G94.

What this file does NOT prove: `massPow` and `defectPow` are named hypotheses, proved for no
operator; whether the paper supplies them (for any `p`) is open. No field is proved for the
Steklov operator of the tetrahedron; no DtN operator is constructed; (7.29) and
Theorem 1.3 / 11.1 remain conditional. The F2 caveat on the `cutoff` row (unconstrained cutoff
data `D`) applies here unchanged.
-/

namespace SteklovAudit.H5GlobalLipRowsPow

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5GlobalLipRowsEv

/-- The G94 inputs with the mass and defect rows at complementary powers of `L`. -/
structure H5bGlobalLipRowsPow (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  F : ℝ → ℝ → ℝ → ℝ → ℝ
  disc : ℝ → ℝ → ℝ → ℝ
  cutoff : ∀ ε γ L : ℝ, |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j,
    (F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)) * (D ε γ L).J i j ^ 2| ≤ disc ε γ L
  discVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    disc ε γ L ≤ η * L
  Λ : ℝ → ℝ → ℝ
  hΛ : ∀ ε γ, 0 ≤ Λ ε γ
  lip : ∀ ε γ L x y : ℝ, |F ε γ L x - F ε γ L y| ≤ Λ ε γ * |x - y|
  m : ℝ → ℝ → ℝ
  hm : ∀ ε γ, 0 ≤ m ε γ
  p : ℝ → ℝ → ℝ
  hp : ∀ ε γ, 0 ≤ p ε γ ∧ p ε γ ≤ 2
  /-- Row: the overlap mass is eventually `O(L ^ p)` (named hypothesis). -/
  massPow : ∀ ε γ : ℝ, ∃ L₁ : ℝ, ∀ L, L₁ ≤ L → hs2 (D ε γ L).J ≤ m ε γ * L ^ (p ε γ)
  /-- Row: the Hilbert–Schmidt defect is `o(L ^ (2 - p))` (named hypothesis). -/
  defectPow : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    hs2 (D ε γ L).K ≤ η * L ^ (2 - p ε γ)

/-- Complementary real powers multiply to `L * L`. -/
theorem rpow_split {L : ℝ} (hL : 0 < L) (p : ℝ) : L ^ p * L ^ (2 - p) = L * L := by
  rw [← Real.rpow_add hL, show p + (2 - p) = (2 : ℝ) by ring]
  first
  | (rw [Real.rpow_two]; ring)
  | (rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring)
  | simp [sq]

/-- The `Real.sqrt` bound for complementary powers. -/
theorem sqrt_pow_prod {k j t m L p Λ : ℝ} (hL : 0 < L) (hk : k ≤ t ^ 2 * L ^ (2 - p))
    (hj : j ≤ m * L ^ p) (hk0 : 0 ≤ k) (hj0 : 0 ≤ j) (ht : 0 ≤ t) (hm : 0 ≤ m)
    (hΛ : 0 ≤ Λ) : Λ * Real.sqrt (k * j) ≤ Λ * (t * Real.sqrt m * L) := by
  have h1 : k * j ≤ (t ^ 2 * L ^ (2 - p)) * (m * L ^ p) :=
    mul_le_mul hk hj hj0 (le_trans hk0 hk)
  have h2 : (t ^ 2 * L ^ (2 - p)) * (m * L ^ p) = t ^ 2 * (m * (L ^ p * L ^ (2 - p))) := by
    ring
  have h3 : (t * Real.sqrt m * L) ^ 2 = t ^ 2 * (m * (L * L)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hm]
    ring
  have h4 : k * j ≤ (t * Real.sqrt m * L) ^ 2 := by
    rw [h3, ← rpow_split hL p, ← h2]
    exact h1
  have h5 : Real.sqrt (k * j) ≤ t * Real.sqrt m * L := by
    have h6 := Real.sqrt_le_sqrt h4
    rw [Real.sqrt_sq (mul_nonneg (mul_nonneg ht (Real.sqrt_nonneg m)) hL.le)] at h6
    exact h6
  exact mul_le_mul_of_nonneg_left h5 hΛ

/-- **G98.** The G94 rows are the case `p = 1`. -/
noncomputable def ofEv {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRowsEv E Emod) :
    H5bGlobalLipRowsPow E Emod where
  nA := H.nA
  nB := H.nB
  D := H.D
  F := H.F
  disc := H.disc
  cutoff := H.cutoff
  discVanish := H.discVanish
  Λ := H.Λ
  hΛ := H.hΛ
  lip := H.lip
  m := H.m
  hm := H.hm
  p := fun _ _ => 1
  hp := fun _ _ => ⟨by norm_num, by norm_num⟩
  massPow := by
    intro ε γ
    obtain ⟨L₁, h⟩ := H.massEv ε γ
    refine ⟨L₁, fun L hL => ?_⟩
    show hs2 (H.D ε γ L).J ≤ H.m ε γ * L ^ (1 : ℝ)
    rw [Real.rpow_one]
    exact h L hL
  defectPow := by
    intro ε γ hε hγ η hη
    obtain ⟨L₀, h⟩ := H.defectSmall ε γ hε hγ η hη
    refine ⟨L₀, fun L hL => ?_⟩
    show hs2 (H.D ε γ L).K ≤ η * L ^ ((2 : ℝ) - 1)
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    exact h L hL

theorem ofEv_p {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRowsEv E Emod) :
    (ofEv H).p = fun _ _ => 1 := rfl

/-- **G98.** The power rows give the G86 inputs. -/
noncomputable def toGlobalLipPow {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRowsPow E Emod) :
    H5bGlobalLipInputs E Emod where
  nA := H.nA
  nB := H.nB
  D := H.D
  F := H.F
  disc := H.disc
  cutoff := H.cutoff
  discVanish := H.discVanish
  Λ := H.Λ
  hΛ := H.hΛ
  lip := H.lip
  globalVanish := by
    intro ε γ hε hγ η hη
    have hs := H5GlobalLipRows.scale_le (H.hΛ ε γ) (Real.sqrt_nonneg (H.m ε γ)) hη
    have hc : 0 < (H.Λ ε γ + 1) * (Real.sqrt (H.m ε γ) + 1) :=
      mul_pos (by linarith [H.hΛ ε γ]) (by linarith [Real.sqrt_nonneg (H.m ε γ)])
    have ht0 : 0 < η / ((H.Λ ε γ + 1) * (Real.sqrt (H.m ε γ) + 1)) := div_pos hη hc
    set t := η / ((H.Λ ε γ + 1) * (Real.sqrt (H.m ε γ) + 1)) with ht_def
    obtain ⟨L₀, hL₀⟩ := H.defectPow ε γ hε hγ (t ^ 2) (pow_pos ht0 2)
    obtain ⟨L₁, hL₁⟩ := H.massPow ε γ
    refine ⟨max 1 (max L₀ L₁), fun L hL => ?_⟩
    have h1 : 1 ≤ L := le_trans (le_max_left 1 (max L₀ L₁)) hL
    have h2 : L₀ ≤ L :=
      le_trans (le_trans (le_max_left L₀ L₁) (le_max_right 1 (max L₀ L₁))) hL
    have h3 : L₁ ≤ L :=
      le_trans (le_trans (le_max_right L₀ L₁) (le_max_right 1 (max L₀ L₁))) hL
    have hL0 : 0 < L := by linarith
    have hmain := sqrt_pow_prod hL0 (hL₀ L h2) (hL₁ L h3)
      (hs2_nonneg _) (hs2_nonneg _) ht0.le (H.hm ε γ) (H.hΛ ε γ)
    refine le_trans hmain ?_
    calc H.Λ ε γ * (t * Real.sqrt (H.m ε γ) * L)
        = (H.Λ ε γ * Real.sqrt (H.m ε γ) * t) * L := by ring
      _ ≤ η * L := mul_le_mul_of_nonneg_right hs hL0.le

theorem toGlobalLipPow_Λ {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRowsPow E Emod) :
    (toGlobalLipPow H).Λ = H.Λ := rfl

/-- **G98.** The power rows give the H5b comparison (7.29). -/
theorem h5b_of_globalLipRowsPow {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRowsPow E Emod) :
    H5bTarget E Emod :=
  h5b_of_globalLipInputs (toGlobalLipPow H)

end SteklovAudit.H5GlobalLipRowsPow
