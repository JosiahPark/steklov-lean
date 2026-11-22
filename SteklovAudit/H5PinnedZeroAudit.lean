import Mathlib
import SteklovAudit.H5PinnedRows
import SteklovAudit.H5GlobalLipRowsAudit

/-!
# G102: pinned to empty data, the rows are the target

Roadmap item G102. With the cutoff data pinned to the empty family (`nA = nB = 0`, zero
coefficients, `F = 0`), the pinned rows `H5bPinnedRows` (G101, `H5PinnedRows.lean`) are
equivalent to `H5bTarget E Emod`. This isolates the F2 caveat: the equivalence of the G90–G100
forms with the target comes exactly from choosing this empty data, so all content of those
forms depends on which data is pinned.

What this file does NOT prove: no row is proved for any operator; the Steklov operator's cutoff
data is not defined in Lean and is not claimed to be empty. No DtN operator is constructed;
(7.29) and Theorem 1.3 / 11.1 remain conditional. This is an audit only.
-/

namespace SteklovAudit.H5PinnedZeroAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5PinnedRows

/-- Empty index sizes. -/
def zA : ℝ → ℝ → ℝ → ℕ := fun _ _ _ => 0

/-- The empty cutoff data. -/
def zD : ∀ ε γ L : ℝ, Data (Fin (zA ε γ L)) (Fin (zA ε γ L)) :=
  fun _ _ _ => ⟨fun _ => 0, fun _ => 0, fun _ _ => 0⟩

/-- The zero function. -/
def zF : ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ _ => 0

/-- **G102.** The target gives the rows pinned to the empty data (`Λ = m = δ = 0`). -/
noncomputable def ofTargetZero {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    H5bPinnedRows E Emod zA zA zD zF where
  disc := fun ε γ L => |E ε γ L - Emod ε γ L|
  cutoff := by
    intro ε γ L
    first
      | (simp [zF, zD, zA]; done)
      | (simp [zF]; done)
      | (simp only [zF, sub_self, zero_mul, Finset.sum_const_zero, sub_zero]; exact le_refl _)
  discVanish := h
  Λ := fun _ _ => 0
  hΛ := fun _ _ => le_refl _
  lip := by
    intro ε γ L x y
    simp [zF]
  m := fun _ _ => 0
  hm := fun _ _ => le_refl _
  massLin := by
    intro ε γ L _
    first
      | (simp [hs2, zD, zA]; done)
      | (simp [hs2]; done)
      | (unfold hs2; simp)
  δ := fun _ _ _ => 0
  defectLin := by
    intro ε γ L _
    first
      | (simp [hs2, Data.K, zD, zA]; done)
      | (simp [hs2, Data.K]; done)
      | (unfold hs2 Data.K; simp)
  δVanish := by
    intro ε γ _ _ η hη
    exact ⟨0, fun _ _ => hη.le⟩

/-- The converse's `disc` is the whole comparison `|E - Emod|`. -/
theorem pinnedZero_disc {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    (ofTargetZero h).disc = fun ε γ L => |E ε γ L - Emod ε γ L| := rfl

/-- **G102 (F2 caveat isolated).** Pinned to the empty data, the rows hold exactly when the
target holds. -/
theorem pinnedZero_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bPinnedRows E Emod zA zA zD zF) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_pinnedRows H, fun h => ⟨ofTargetZero h⟩⟩

end SteklovAudit.H5PinnedZeroAudit
