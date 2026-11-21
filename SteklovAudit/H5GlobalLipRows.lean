import Mathlib
import SteklovAudit.H5GlobalLip

/-!
# G90: `globalVanish` replaced by two rows at the linear scale

Roadmap item G90. `H5bGlobalLipRows E Emod` has the fields of `H5bGlobalLipInputs`
(G86, `H5GlobalLip.lean`) except `globalVanish`, which is replaced by
* `massLin`: `hs2 J ≤ m ε γ * L` for `1 ≤ L` (the mass row (2.2) at the scale `L` rather
  than `(1 + L)²`), and
* `defectLin` + `δVanish`: `hs2 K ≤ δ ε γ L * L` with `δ ε γ L → 0` as `L → ∞` (an `o(L)`
  Hilbert–Schmidt defect).
`sqrt_lin_prod` is the elementary estimate `Λ √(k j) ≤ Λ (t √m L)`; `toGlobalLip` derives
`globalVanish` from the two rows, and `h5b_of_globalLipRows` gives `H5bTarget E Emod`.

What this file does NOT prove: whether the paper supplies `massLin` or `defectLin` at this
scale is open (Josiah to say). Both are named hypotheses and are proved for no operator; G89
(`H5GlobalVanishNeeded.lean`) shows the rows of `PDEInputs` at the scale `(1 + L)²` do not
suffice. No field is proved for the Steklov operator of the tetrahedron; no DtN operator is
constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional. The F2 caveat on the `cutoff`
row (unconstrained cutoff data `D`) applies here unchanged.
-/

namespace SteklovAudit.H5GlobalLipRows

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip

/-- The G86 inputs with `globalVanish` replaced by a linear mass row and an `o(L)` defect row. -/
structure H5bGlobalLipRows (E Emod : ℝ → ℝ → ℝ → ℝ) where
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
  /-- Row: the overlap mass is `O(L)` (named hypothesis). -/
  massLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D ε γ L).J ≤ m ε γ * L
  δ : ℝ → ℝ → ℝ → ℝ
  /-- Row: the Hilbert–Schmidt defect is `δ ε γ L * L` (named hypothesis). -/
  defectLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D ε γ L).K ≤ δ ε γ L * L
  /-- Row: `δ ε γ L → 0` as `L → ∞` (named hypothesis). -/
  δVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    δ ε γ L ≤ η

/-- **G90.** Elementary estimate: linear bounds on `k` and `j` bound `Λ √(k j)` linearly. -/
theorem sqrt_lin_prod {k j d m t L Λ : ℝ} (hL : 0 ≤ L) (hk : k ≤ d * L) (hj : j ≤ m * L)
    (hk0 : 0 ≤ k) (hj0 : 0 ≤ j) (hd : d ≤ t ^ 2) (ht : 0 ≤ t) (hm : 0 ≤ m) (hΛ : 0 ≤ Λ) :
    Λ * Real.sqrt (k * j) ≤ Λ * (t * Real.sqrt m * L) := by
  have h1 : k * j ≤ (d * L) * (m * L) := mul_le_mul hk hj hj0 (le_trans hk0 hk)
  have h2 : d * (m * L ^ 2) ≤ t ^ 2 * (m * L ^ 2) :=
    mul_le_mul_of_nonneg_right hd (mul_nonneg hm (sq_nonneg L))
  have h3 : (t * Real.sqrt m * L) ^ 2 = t ^ 2 * (m * L ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hm]
    ring
  have h4 : k * j ≤ (t * Real.sqrt m * L) ^ 2 :=
    calc k * j ≤ (d * L) * (m * L) := h1
      _ = d * (m * L ^ 2) := by ring
      _ ≤ t ^ 2 * (m * L ^ 2) := h2
      _ = (t * Real.sqrt m * L) ^ 2 := h3.symm
  have h5 : Real.sqrt (k * j) ≤ t * Real.sqrt m * L := by
    have h6 := Real.sqrt_le_sqrt h4
    rw [Real.sqrt_sq (mul_nonneg (mul_nonneg ht (Real.sqrt_nonneg m)) hL)] at h6
    exact h6
  exact mul_le_mul_of_nonneg_left h5 hΛ

/-- The scaling used in `toGlobalLip`: `Λ s (η / ((Λ + 1)(s + 1))) ≤ η`. -/
theorem scale_le {Λ s η : ℝ} (hΛ : 0 ≤ Λ) (hs : 0 ≤ s) (hη : 0 < η) :
    Λ * s * (η / ((Λ + 1) * (s + 1))) ≤ η := by
  have hc : 0 < (Λ + 1) * (s + 1) := mul_pos (by linarith) (by linarith)
  have h1 : Λ * s ≤ (Λ + 1) * (s + 1) := by nlinarith
  have h2 : 0 ≤ η / ((Λ + 1) * (s + 1)) := div_nonneg hη.le hc.le
  have hc0 : (Λ + 1) * (s + 1) ≠ 0 := hc.ne'
  have ha0 : Λ + 1 ≠ 0 := ne_of_gt (by linarith)
  have hb0 : s + 1 ≠ 0 := ne_of_gt (by linarith)
  calc Λ * s * (η / ((Λ + 1) * (s + 1)))
      ≤ ((Λ + 1) * (s + 1)) * (η / ((Λ + 1) * (s + 1))) := mul_le_mul_of_nonneg_right h1 h2
    _ = η := by
      first
        | (field_simp; done)
        | exact mul_div_cancel₀ η hc0
        | (rw [mul_comm]; exact div_mul_cancel₀ η hc0)
        | (field_simp; ring)

/-- **G90.** The two linear-scale rows give the G86 inputs. -/
noncomputable def toGlobalLip {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRows E Emod) :
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
    have hs := scale_le (H.hΛ ε γ) (Real.sqrt_nonneg (H.m ε γ)) hη
    have hc : 0 < (H.Λ ε γ + 1) * (Real.sqrt (H.m ε γ) + 1) :=
      mul_pos (by linarith [H.hΛ ε γ]) (by linarith [Real.sqrt_nonneg (H.m ε γ)])
    have ht0 : 0 < η / ((H.Λ ε γ + 1) * (Real.sqrt (H.m ε γ) + 1)) := div_pos hη hc
    set t := η / ((H.Λ ε γ + 1) * (Real.sqrt (H.m ε γ) + 1)) with ht_def
    obtain ⟨L₀, hL₀⟩ := H.δVanish ε γ hε hγ (t ^ 2) (pow_pos ht0 2)
    refine ⟨max 1 L₀, fun L hL => ?_⟩
    have h1 : 1 ≤ L := le_trans (le_max_left _ _) hL
    have h2 : L₀ ≤ L := le_trans (le_max_right _ _) hL
    have hL0 : 0 ≤ L := by linarith
    have hmain := sqrt_lin_prod hL0 (H.defectLin ε γ L h1) (H.massLin ε γ L h1)
      (hs2_nonneg _) (hs2_nonneg _) (hL₀ L h2) ht0.le (H.hm ε γ) (H.hΛ ε γ)
    refine le_trans hmain ?_
    calc H.Λ ε γ * (t * Real.sqrt (H.m ε γ) * L)
        = (H.Λ ε γ * Real.sqrt (H.m ε γ) * t) * L := by ring
      _ ≤ η * L := mul_le_mul_of_nonneg_right hs hL0

theorem toGlobalLip_Λ {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRows E Emod) :
    (toGlobalLip H).Λ = H.Λ := rfl

/-- **G90.** The linear-scale rows give the H5b comparison (7.29). -/
theorem h5b_of_globalLipRows {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRows E Emod) :
    H5bTarget E Emod :=
  h5b_of_globalLipInputs (toGlobalLip H)

end SteklovAudit.H5GlobalLipRows
