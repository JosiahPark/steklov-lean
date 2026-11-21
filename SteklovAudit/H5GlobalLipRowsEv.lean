import Mathlib
import SteklovAudit.H5GlobalLipRows

/-!
# G94: the G90 rows in eventual form, with no rate function

Roadmap item G94. `H5bGlobalLipRowsEv E Emod` has the fields of `H5bGlobalLipRows`
(G90, `H5GlobalLipRows.lean`) except `massLin`, `δ`, `defectLin`, `δVanish`, which are
replaced by
* `massEv`: for each `ε γ`, eventually in `L`, `hs2 J ≤ m ε γ * L` (an eventual `O(L)` mass
  row), and
* `defectSmall`: for every `η > 0`, eventually `hs2 K ≤ η * L` (an `o(L)` Hilbert–Schmidt
  defect stated directly, with no auxiliary `δ`).
`ofRows` shows the G90 rows imply these, so this is a weaker (or equal) input;
`toGlobalLipEv` derives the G86 inputs, and `h5b_of_globalLipRowsEv` gives `H5bTarget E Emod`.

What this file does NOT prove: `massEv` and `defectSmall` are named hypotheses, proved for no
operator; whether the paper supplies them is open (Josiah to say). No field is proved for the
Steklov operator of the tetrahedron; no DtN operator is constructed; (7.29) and
Theorem 1.3 / 11.1 remain conditional. The F2 caveat on the `cutoff` row (unconstrained cutoff
data `D`) applies here unchanged.
-/

namespace SteklovAudit.H5GlobalLipRowsEv

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows

/-- The G90 inputs with the mass row only eventual and the defect row stated as `o(L)`. -/
structure H5bGlobalLipRowsEv (E Emod : ℝ → ℝ → ℝ → ℝ) where
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
  /-- Row: the overlap mass is eventually `O(L)` (named hypothesis). -/
  massEv : ∀ ε γ : ℝ, ∃ L₁ : ℝ, ∀ L, L₁ ≤ L → hs2 (D ε γ L).J ≤ m ε γ * L
  /-- Row: the Hilbert–Schmidt defect is `o(L)` (named hypothesis). -/
  defectSmall : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    hs2 (D ε γ L).K ≤ η * L

/-- **G94.** The G90 rows give the eventual rows. -/
noncomputable def ofRows {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRows E Emod) :
    H5bGlobalLipRowsEv E Emod where
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
  massEv := fun ε γ => ⟨1, fun L hL => H.massLin ε γ L hL⟩
  defectSmall := by
    intro ε γ hε hγ η hη
    obtain ⟨L₀, hL₀⟩ := H.δVanish ε γ hε hγ η hη
    refine ⟨max 1 L₀, fun L hL => ?_⟩
    have h1 : 1 ≤ L := le_trans (le_max_left 1 L₀) hL
    have h2 : L₀ ≤ L := le_trans (le_max_right 1 L₀) hL
    have hL0 : 0 ≤ L := by linarith
    exact le_trans (H.defectLin ε γ L h1) (mul_le_mul_of_nonneg_right (hL₀ L h2) hL0)

theorem ofRows_m {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRows E Emod) :
    (ofRows H).m = H.m := rfl

/-- **G94.** The eventual rows give the G86 inputs. -/
noncomputable def toGlobalLipEv {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRowsEv E Emod) :
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
    obtain ⟨L₀, hL₀⟩ := H.defectSmall ε γ hε hγ (t ^ 2) (pow_pos ht0 2)
    obtain ⟨L₁, hL₁⟩ := H.massEv ε γ
    refine ⟨max 1 (max L₀ L₁), fun L hL => ?_⟩
    have h1 : 1 ≤ L := le_trans (le_max_left 1 (max L₀ L₁)) hL
    have h2 : L₀ ≤ L :=
      le_trans (le_trans (le_max_left L₀ L₁) (le_max_right 1 (max L₀ L₁))) hL
    have h3 : L₁ ≤ L :=
      le_trans (le_trans (le_max_right L₀ L₁) (le_max_right 1 (max L₀ L₁))) hL
    have hL0 : 0 ≤ L := by linarith
    have hmain := H5GlobalLipRows.sqrt_lin_prod hL0 (hL₀ L h2) (hL₁ L h3)
      (hs2_nonneg _) (hs2_nonneg _) (le_refl (t ^ 2)) ht0.le (H.hm ε γ) (H.hΛ ε γ)
    refine le_trans hmain ?_
    calc H.Λ ε γ * (t * Real.sqrt (H.m ε γ) * L)
        = (H.Λ ε γ * Real.sqrt (H.m ε γ) * t) * L := by ring
      _ ≤ η * L := mul_le_mul_of_nonneg_right hs hL0

theorem toGlobalLipEv_Λ {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRowsEv E Emod) :
    (toGlobalLipEv H).Λ = H.Λ := rfl

/-- **G94.** The eventual rows give the H5b comparison (7.29). -/
theorem h5b_of_globalLipRowsEv {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipRowsEv E Emod) :
    H5bTarget E Emod :=
  h5b_of_globalLipInputs (toGlobalLipEv H)

end SteklovAudit.H5GlobalLipRowsEv
