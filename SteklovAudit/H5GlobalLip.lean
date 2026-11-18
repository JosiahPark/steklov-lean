import Mathlib
import SteklovAudit.H5SelMin
import SteklovAudit.H5MaskSplit

/-!
# G86: the uniform-Lipschitz case of the row "Lipschitz-type bounds Λ, λ"

Roadmap item G86. `H5bGlobalLipInputs E Emod` replaces the split-energy rows of
`H5bSelMinInputs` (G83, `H5SelMin.lean`) by one global Lipschitz bound: `F ε γ L` is
`Λ ε γ`-Lipschitz on all of `ℝ`, uniformly in `L`, and the unsplit defect/overlap product
`Λ ε γ * √(hs2 K * hs2 J)` is `o(L)`. `toSelMin` builds the G83 inputs with `Λ0 := Λ`,
`lam := Λ`, the selector `Msel := 0`, and `directVanish` obtained from `split_le_unsplit`
(G85, `H5MaskSplit.lean`). `h5b_of_globalLipInputs` then gives `H5bTarget E Emod`.

F table text: the split energy (high/low parts, `Msel`) is not needed when `F ε γ L` is
Lipschitz uniformly in `L`; the row becomes `lip` + `globalVanish`.

What this file does NOT prove: whether the smoothed counting function of the paper is Lipschitz
uniformly in `L` is the open row (Josiah to say); `globalVanish` is a named hypothesis and is not
proved for any operator. No field is proved for the Steklov operator of the tetrahedron; no DtN
operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional. The F2 caveat on the
`cutoff` row (unconstrained cutoff data `D`) applies here unchanged.
-/

namespace SteklovAudit.H5GlobalLip

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5MaskSplit

/-- The G83 inputs with the split Lipschitz rows replaced by one global Lipschitz bound. -/
structure H5bGlobalLipInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
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
  /-- Row: `F ε γ L` is `Λ ε γ`-Lipschitz on all of `ℝ`, uniformly in `L`. -/
  lip : ∀ ε γ L x y : ℝ, |F ε γ L x - F ε γ L y| ≤ Λ ε γ * |x - y|
  /-- Row: the unsplit defect/overlap product is `o(L)`. -/
  globalVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    Λ ε γ * Real.sqrt (hs2 (D ε γ L).K * hs2 (D ε γ L).J) ≤ η * L

/-- **G86.** The global-Lipschitz inputs give the G83 inputs (selector `Msel := 0`). -/
noncomputable def toSelMin {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipInputs E Emod) :
    H5bSelMinInputs E Emod where
  nA := H.nA
  nB := H.nB
  D := H.D
  F := H.F
  disc := H.disc
  cutoff := H.cutoff
  discVanish := H.discVanish
  Λ0 := H.Λ
  hΛ0 := H.hΛ
  lam := fun ε γ _ _ => H.Λ ε γ
  hlam := fun ε γ _ _ => H.hΛ ε γ
  lipHi := fun ε γ _ L _ _ _ => H.lip ε γ L _ _
  lipLo := fun ε γ _ L _ _ _ => H.lip ε γ L _ _
  directVanish := by
    intro ε γ hε hγ η hη
    obtain ⟨L₀, hL⟩ := H.globalVanish ε γ hε hγ η hη
    refine ⟨fun _ => 0, L₀, fun L hL' => ?_⟩
    refine le_trans ?_ (hL L hL')
    have hs := split_le_unsplit (hiE (H.D ε γ L) 0) (H.D ε γ L).K (H.D ε γ L).J
    have h1 := mul_le_mul_of_nonneg_left hs (H.hΛ ε γ)
    rw [mul_add] at h1
    exact h1

theorem toSelMin_Λ0 {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipInputs E Emod) :
    (toSelMin H).Λ0 = H.Λ := rfl

/-- **G86.** The global-Lipschitz inputs give the H5b comparison (7.29). -/
theorem h5b_of_globalLipInputs {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bGlobalLipInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_selMinInputs (toSelMin H)

end SteklovAudit.H5GlobalLip
