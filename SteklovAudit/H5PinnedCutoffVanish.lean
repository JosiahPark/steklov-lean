import Mathlib
import SteklovAudit.H5PinnedRows

/-!
# G107: for pinned data the `disc` field carries no content

Roadmap item G107. `H5bPinnedCore E Emod nA nB D₀ F₀` is `H5bPinnedRows` (G101) with the
three fields `disc`, `cutoff`, `discVanish` replaced by the single row `cutoffVanish`: the
cutoff discrepancy `coreDisc` (the absolute difference between `E − Emod` and the explicit
spectral sum of `D₀`, `F₀`) is `o(L)`. `ofCore` and `toCore` convert in both directions, so
`pinned_iff_core` shows the two structures are inhabited for exactly the same inputs, and
`h5b_of_pinnedCore` gives `H5bTarget E Emod`.

What this file does NOT prove: no row (in particular not `cutoffVanish`) is proved for any
operator. The cutoff data of the Steklov operator of the tetrahedron is not defined in Lean;
`D₀`, `F₀` are arbitrary given data. No DtN operator is constructed; (7.29) and
Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5PinnedCutoffVanish

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5PinnedRows

/-- The cutoff discrepancy of pinned data: `|(E − Emod) − Σᵢⱼ (F₀ aᵢ − F₀ bⱼ) Jᵢⱼ²|`. -/
noncomputable def coreDisc (E Emod : ℝ → ℝ → ℝ → ℝ) (nA nB : ℝ → ℝ → ℝ → ℕ)
    (D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F₀ : ℝ → ℝ → ℝ → ℝ → ℝ) (ε γ L : ℝ) : ℝ :=
  |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j,
    (F₀ ε γ L ((D₀ ε γ L).a i) - F₀ ε γ L ((D₀ ε γ L).b j)) * (D₀ ε γ L).J i j ^ 2|

/-- The G101 rows with `disc`/`cutoff`/`discVanish` merged into one `o(L)` row. -/
structure H5bPinnedCore (E Emod : ℝ → ℝ → ℝ → ℝ) (nA nB : ℝ → ℝ → ℝ → ℕ)
    (D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F₀ : ℝ → ℝ → ℝ → ℝ → ℝ) where
  /-- Row: the cutoff discrepancy of the pinned data is `o(L)` (named hypothesis). -/
  cutoffVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    coreDisc E Emod nA nB D₀ F₀ ε γ L ≤ η * L
  Λ : ℝ → ℝ → ℝ
  hΛ : ∀ ε γ, 0 ≤ Λ ε γ
  lip : ∀ ε γ L x y : ℝ, |F₀ ε γ L x - F₀ ε γ L y| ≤ Λ ε γ * |x - y|
  m : ℝ → ℝ → ℝ
  hm : ∀ ε γ, 0 ≤ m ε γ
  massLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D₀ ε γ L).J ≤ m ε γ * L
  δ : ℝ → ℝ → ℝ → ℝ
  defectLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D₀ ε γ L).K ≤ δ ε γ L * L
  δVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    δ ε γ L ≤ η

variable {E Emod : ℝ → ℝ → ℝ → ℝ} {nA nB : ℝ → ℝ → ℝ → ℕ}
  {D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))} {F₀ : ℝ → ℝ → ℝ → ℝ → ℝ}

/-- **G107.** A core family is a pinned family with `disc := coreDisc`. -/
noncomputable def ofCore (H : H5bPinnedCore E Emod nA nB D₀ F₀) :
    H5bPinnedRows E Emod nA nB D₀ F₀ where
  disc := coreDisc E Emod nA nB D₀ F₀
  cutoff := fun _ _ _ => le_refl _
  discVanish := H.cutoffVanish
  Λ := H.Λ
  hΛ := H.hΛ
  lip := H.lip
  m := H.m
  hm := H.hm
  massLin := H.massLin
  δ := H.δ
  defectLin := H.defectLin
  δVanish := H.δVanish

/-- **G107.** Any pinned family yields a core family: `coreDisc ≤ disc = o(L)`. -/
noncomputable def toCore (H : H5bPinnedRows E Emod nA nB D₀ F₀) :
    H5bPinnedCore E Emod nA nB D₀ F₀ where
  cutoffVanish := by
    intro ε γ hε hγ η hη
    obtain ⟨L₀, hL⟩ := H.discVanish ε γ hε hγ η hη
    exact ⟨L₀, fun L hL₀ => le_trans (H.cutoff ε γ L) (hL L hL₀)⟩
  Λ := H.Λ
  hΛ := H.hΛ
  lip := H.lip
  m := H.m
  hm := H.hm
  massLin := H.massLin
  δ := H.δ
  defectLin := H.defectLin
  δVanish := H.δVanish

theorem ofCore_disc (H : H5bPinnedCore E Emod nA nB D₀ F₀) :
    (ofCore H).disc = coreDisc E Emod nA nB D₀ F₀ := rfl

/-- **G107.** The pinned rows and the core rows are inhabited for the same inputs. -/
theorem pinned_iff_core :
    Nonempty (H5bPinnedRows E Emod nA nB D₀ F₀) ↔ Nonempty (H5bPinnedCore E Emod nA nB D₀ F₀) :=
  ⟨fun ⟨H⟩ => ⟨toCore H⟩, fun ⟨H⟩ => ⟨ofCore H⟩⟩

/-- **G107.** The core rows give the H5b comparison (7.29). -/
theorem h5b_of_pinnedCore (H : H5bPinnedCore E Emod nA nB D₀ F₀) : H5bTarget E Emod :=
  h5b_of_pinnedRows (ofCore H)

end SteklovAudit.H5PinnedCutoffVanish
