import Mathlib
import SteklovAudit.H5PinnedRows

/-!
# G108: pinned rows force the data's own spectral sum to be `o(L)`

Roadmap item G108. For pinned cutoff data `D₀`, `F₀` (G101, `H5PinnedRows.lean`),
`pinnedSum D₀ F₀ ε γ L` is the explicit finite-cutoff spectral sum
`Σᵢⱼ (F₀ aᵢ − F₀ bⱼ) Jᵢⱼ²`. `pinned_sum_littleO` shows that any `H5bPinnedRows E Emod nA nB D₀ F₀`
forces `|pinnedSum D₀ F₀ ε γ L| = o(L)`: the target gives `|E − Emod| = o(L)` and the cutoff
row gives `|(E − Emod) − pinnedSum| = o(L)`. This is a condition on `D₀`, `F₀` alone, with no
reference to `E`; `not_pinned_of_sum_large` records that data failing it admits pinned rows for
no `E`, `Emod` at all.

What this file does NOT prove: no row is proved for any operator, and `SumLittleO` is not
proved for any data coming from the Steklov operator of the tetrahedron, whose cutoff data is
not defined in Lean. No DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain
conditional.
-/

namespace SteklovAudit.H5PinnedSumSmall

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5PinnedRows

/-- The explicit finite-cutoff spectral sum of pinned data: `Σᵢⱼ (F₀ aᵢ − F₀ bⱼ) Jᵢⱼ²`. -/
noncomputable def pinnedSum {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F₀ : ℝ → ℝ → ℝ → ℝ → ℝ) (ε γ L : ℝ) : ℝ :=
  ∑ i, ∑ j, (F₀ ε γ L ((D₀ ε γ L).a i) - F₀ ε γ L ((D₀ ε γ L).b j)) * (D₀ ε γ L).J i j ^ 2

/-- The data's own spectral sum is `o(L)` (a property of `D₀`, `F₀` only). -/
def SumLittleO {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F₀ : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |pinnedSum D₀ F₀ ε γ L| ≤ η * L

variable {E Emod : ℝ → ℝ → ℝ → ℝ} {nA nB : ℝ → ℝ → ℝ → ℕ}
  {D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))} {F₀ : ℝ → ℝ → ℝ → ℝ → ℝ}

/-- **G108.** Pinned rows force the pinned spectral sum to be `o(L)`. -/
theorem pinned_sum_littleO (H : H5bPinnedRows E Emod nA nB D₀ F₀) : SumLittleO D₀ F₀ := by
  intro ε γ hε hγ η hη
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨L₀, h₀⟩ := h5b_of_pinnedRows H ε γ hε hγ (η / 2) hη2
  obtain ⟨L₁, h₁⟩ := H.discVanish ε γ hε hγ (η / 2) hη2
  refine ⟨max L₀ L₁, fun L hL => ?_⟩
  have ha : |E ε γ L - Emod ε γ L| ≤ η / 2 * L := h₀ L (le_trans (le_max_left _ _) hL)
  have hb0 := le_trans (H.cutoff ε γ L) (h₁ L (le_trans (le_max_right _ _) hL))
  have hb : |(E ε γ L - Emod ε γ L) - pinnedSum D₀ F₀ ε γ L| ≤ η / 2 * L := hb0
  have hsplit : η / 2 * L + η / 2 * L = η * L := by ring
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **G108.** Pinned rows give both the target (7.29) and the data condition. -/
theorem pinned_target_and_sum (H : H5bPinnedRows E Emod nA nB D₀ F₀) :
    H5bTarget E Emod ∧ SumLittleO D₀ F₀ :=
  ⟨h5b_of_pinnedRows H, pinned_sum_littleO H⟩

/-- **G108.** Data whose spectral sum is not `o(L)` admits pinned rows for no `E`, `Emod`. -/
theorem not_pinned_of_sum_large (h : ¬ SumLittleO D₀ F₀) :
    ∀ E Emod : ℝ → ℝ → ℝ → ℝ, ¬ Nonempty (H5bPinnedRows E Emod nA nB D₀ F₀) :=
  fun _ _ ⟨H⟩ => h (pinned_sum_littleO H)

end SteklovAudit.H5PinnedSumSmall
