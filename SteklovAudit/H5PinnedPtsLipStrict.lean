import Mathlib
import SteklovAudit.H5PinnedPtsLip

/-!
# G112: the pointwise Lipschitz row is strictly weaker than the global one

Roadmap item G112. One-point data `flatD` (both spectral points `0`, overlap `1`, so `K = 0` and
`hs2 J = 1`) with `F₀ x = x²` satisfies the point rows of G111 (`Λ = 0`, `m = 1`, `δ = 0`), but admits
no data rows of G109: the global row at `x = Λ + 1`, `y = 0` would give `(Λ + 1)² ≤ Λ (Λ + 1)`.

F table text: the pointwise Lipschitz row admits data and `F₀` that the global row rejects.

What this file does NOT prove: anything about the Steklov operator; this is a toy example about the
form of the rows. (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5PinnedPtsLipStrict

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5PinnedDataRows
  SteklovAudit.H5PinnedPtsLip

/-- One spectral point on each side. -/
def oA : ℝ → ℝ → ℝ → ℕ := fun _ _ _ => 1

/-- Both spectral points `0`, overlap `1`. -/
noncomputable def flatD : ∀ ε γ L : ℝ, Data (Fin (oA ε γ L)) (Fin (oA ε γ L)) :=
  fun _ _ _ => ⟨fun _ => 0, fun _ => 0, fun _ _ => 1⟩

/-- `F₀ x = x²`, not globally Lipschitz. -/
noncomputable def sqF : ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ x => x ^ 2

/-- **G112.** The point rows hold for `flatD`, `sqF`. -/
theorem ptsRows_flat : Nonempty (H5bPinnedPtsRows oA oA flatD sqF) :=
  ⟨{ Λ := fun _ _ => 0
     hΛ := fun _ _ => le_refl _
     lipPts := by
       intro ε γ L _ i j
       simp [flatD, sqF]
     m := fun _ _ => 1
     hm := fun _ _ => zero_le_one
     massLin := by
       intro ε γ L hL
       first
         | (simp [hs2, flatD, oA, Finset.card_univ, Fintype.card_fin]; done)
         | (simp [hs2, flatD, oA, Finset.card_univ, Fintype.card_fin]; linarith)
         | (simp [hs2, flatD, oA, Finset.card_univ, Fintype.card_fin]; norm_num; linarith)
         | (simp [hs2, flatD, oA, Finset.card_univ, Fintype.card_fin, hL])
         | (simp only [hs2, flatD, oA, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
             nsmul_eq_mul]; norm_num; linarith)
     δ := fun _ _ _ => 0
     defectLin := by
       intro ε γ L _
       simp [hs2, Data.K, flatD]
     δVanish := fun _ _ _ _ η hη => ⟨0, fun _ _ => hη.le⟩ }⟩

/-- **G112.** No data rows (global Lipschitz row) exist for `flatD`, `sqF`. -/
theorem not_dataRows_flat : ¬ Nonempty (H5bPinnedDataRows oA oA flatD sqF) := by
  rintro ⟨R⟩
  have hΛ := R.hΛ 0 0
  have h : |(R.Λ 0 0 + 1) ^ 2 - 0 ^ 2| ≤ R.Λ 0 0 * |R.Λ 0 0 + 1 - 0| := R.lip 0 0 0 (R.Λ 0 0 + 1) 0
  have hB : |R.Λ 0 0 + 1 - 0| = R.Λ 0 0 + 1 := by
    rw [sub_zero]
    exact abs_of_pos (by linarith)
  have hA : (R.Λ 0 0 + 1) ^ 2 - 0 ^ 2 ≤ |(R.Λ 0 0 + 1) ^ 2 - 0 ^ 2| := le_abs_self _
  rw [hB] at h
  nlinarith [h, hA, hΛ]

/-- **G112.** The pointwise row is strictly weaker than the global row. -/
theorem ptsLip_strictly_weaker :
    Nonempty (H5bPinnedPtsRows oA oA flatD sqF) ∧ ¬ Nonempty (H5bPinnedDataRows oA oA flatD sqF) :=
  ⟨ptsRows_flat, not_dataRows_flat⟩

end SteklovAudit.H5PinnedPtsLipStrict
