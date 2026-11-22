import Mathlib
import SteklovAudit.H5PinnedDataRows

/-!
# G110: relative to the data rows, the cutoff row is the target

Roadmap item G110. Given the data rows `R : H5bPinnedDataRows nA nB D₀ F₀` (G109), pinned rows for
`E`, `Emod` exist exactly when the H5b target (7.29) holds for `E`, `Emod`
(`pinned_iff_target_of_dataRows`). Forward: `h5b_of_pinnedRows`. Converse
(`cutoffVanish_of_target`): the data rows give `|pinnedSum| = o(L)` (`sumLittleO_of_dataRows`), the
target gives `|E − Emod| = o(L)`, so `coreDisc ≤ |E − Emod| + |pinnedSum| = o(L)`; then
`pinned_iff_dataRows_core`.

F table text: once the data rows hold, the remaining row carries exactly the content of (7.29); all
non-trivial content of the pinned form is in the data rows and in the choice of `D₀` (the paper's
cutoff data, which is open).

What this file does NOT prove: no row is proved for any operator; `D₀`, `F₀` are arbitrary given data.
No DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5PinnedCutoffIsTarget

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5PinnedRows
  SteklovAudit.H5PinnedCutoffVanish SteklovAudit.H5PinnedSumSmall SteklovAudit.H5PinnedDataRows

variable {E Emod : ℝ → ℝ → ℝ → ℝ} {nA nB : ℝ → ℝ → ℝ → ℕ}
  {D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))} {F₀ : ℝ → ℝ → ℝ → ℝ → ℝ}

/-- **G110.** Data rows and the target give the `o(L)` cutoff row. -/
theorem cutoffVanish_of_target (R : H5bPinnedDataRows nA nB D₀ F₀) (hT : H5bTarget E Emod) :
    ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      coreDisc E Emod nA nB D₀ F₀ ε γ L ≤ η * L := by
  intro ε γ hε hγ η hη
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨L₀, h₀⟩ := hT ε γ hε hγ (η / 2) hη2
  obtain ⟨L₁, h₁⟩ := sumLittleO_of_dataRows R ε γ hε hγ (η / 2) hη2
  refine ⟨max L₀ L₁, fun L hL => ?_⟩
  have ha : |E ε γ L - Emod ε γ L| ≤ η / 2 * L := h₀ L (le_trans (le_max_left _ _) hL)
  have hb : |pinnedSum D₀ F₀ ε γ L| ≤ η / 2 * L := h₁ L (le_trans (le_max_right _ _) hL)
  show |(E ε γ L - Emod ε γ L) - pinnedSum D₀ F₀ ε γ L| ≤ η * L
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **G110.** Relative to the data rows, pinned rows exist iff the target (7.29) holds. -/
theorem pinned_iff_target_of_dataRows (R : H5bPinnedDataRows nA nB D₀ F₀) :
    Nonempty (H5bPinnedRows E Emod nA nB D₀ F₀) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_pinnedRows H,
    fun hT => pinned_iff_dataRows_core.2 ⟨⟨R⟩, cutoffVanish_of_target R hT⟩⟩

end SteklovAudit.H5PinnedCutoffIsTarget
