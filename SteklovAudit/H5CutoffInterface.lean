import Mathlib
import SteklovAudit.CountableCutoffTail

/-!
# What a growing edge family must supply for H5 (roadmap item G116)

At each cutoff `L` an edge probe family gives finite certificates `X L` (weights, eigenvalues,
comparison values, total mass `M`, summed squared defect `E_L`), a multiplier `F L` with Lipschitz
constant `Lip L`, and a largest comparison value `μ*(L) < L` (for `L ≥ Lgap`). Then G114 gives

  `|S_L − S≤L_L| ≤ Lip(F_L) · E_L / (L − μ*(L))`             (`cutoff_error_le`).

H5 through this route needs exactly two estimates, both OPEN and both only named here:
(i)  `RatioLittleO`: `Lip(F_L) · E_L / (L − μ*(L)) = o(L)`;
(ii) `TraceMatches`: the truncated probe trace `S≤L_L` approximates the localized tetrahedron–wedge
     discrepancy `E − E_mod` (the function `D`) to `o(L)` — the remaining geometric question.
`full_trace_matches` shows that (i) and (ii) together give `|S_L − D L| = o(L)`.

What this file does NOT prove: (i), (ii), the existence of such an edge family, (7.29), H5, or
Theorem 1.3 / 11.1. It only makes the two remaining estimates explicit.
-/

namespace SteklovAudit.H5CutoffInterface

open SteklovAudit.CountableCutoffTail

/-- A cutoff-indexed probe family with the data needed for the G114 bound at every `L ≥ Lgap`. -/
structure H5EdgeFamilyCutoff (ι : Type*) (κ : Type*) where
  X : ℝ → Cert ι κ
  F : ℝ → ℝ → ℝ
  Lip : ℝ → ℝ
  muStar : ℝ → ℝ
  Lgap : ℝ
  hLip : ∀ L, 0 ≤ Lip L
  hF : ∀ L x y, |F L x - F L y| ≤ Lip L * |x - y|
  hmu : ∀ L j, (X L).mu j ≤ muStar L
  hgap : ∀ L, Lgap ≤ L → muStar L < L

namespace H5EdgeFamilyCutoff

variable {ι κ : Type*} (Y : H5EdgeFamilyCutoff ι κ)

/-- The cutoff ratio `Lip(F_L) · E_L / (L − μ*(L))`. -/
noncomputable def ratio (L : ℝ) : ℝ := Y.Lip L * (Y.X L).E / (L - Y.muStar L)

/-- **G116.** At each `L ≥ Lgap` the cutoff error is at most the ratio. -/
theorem cutoff_error_le (L : ℝ) (hL : Y.Lgap ≤ L) :
    |(Y.X L).S (Y.F L) - (Y.X L).Sle (Y.F L) L| ≤ Y.ratio L :=
  (Y.X L).cutoff_tail_le (Y.F L) (Y.Lip L) (Y.hLip L) (Y.hF L) (Y.muStar L) L (Y.hmu L)
    (Y.hgap L hL)

/-- Open estimate (i), named only: the cutoff ratio is `o(L)`. -/
def RatioLittleO : Prop := ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → Y.ratio L ≤ η * L

/-- Open estimate (ii), named only: the truncated probe trace matches `D L` (the paper's localized
`E − E_mod` at cutoff `L`) to `o(L)`. -/
def TraceMatches (D : ℝ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |(Y.X L).Sle (Y.F L) L - D L| ≤ η * L

/-- **G116.** (i) and (ii) together give `|S_L − D L| = o(L)`. -/
theorem full_trace_matches (D : ℝ → ℝ) (h1 : Y.RatioLittleO) (h2 : Y.TraceMatches D) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |(Y.X L).S (Y.F L) - D L| ≤ η * L := by
  intro η hη
  obtain ⟨L1, hL1⟩ := h1 (η / 2) (by linarith)
  obtain ⟨L2, hL2⟩ := h2 (η / 2) (by linarith)
  refine ⟨max (max L1 L2) Y.Lgap, fun L hL => ?_⟩
  have a1 : L1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have a2 : L2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have a3 : Y.Lgap ≤ L := le_trans (le_max_right _ _) hL
  have b1 := (Y.cutoff_error_le L a3).trans (hL1 L a1)
  have b2 := hL2 L a2
  have tri : |(Y.X L).S (Y.F L) - D L| ≤
      |(Y.X L).S (Y.F L) - (Y.X L).Sle (Y.F L) L| + |(Y.X L).Sle (Y.F L) L - D L| := by
    have e : (Y.X L).S (Y.F L) - D L =
        ((Y.X L).S (Y.F L) - (Y.X L).Sle (Y.F L) L) + ((Y.X L).Sle (Y.F L) L - D L) := by ring
    rw [e]
    first
      | exact abs_add _ _
      | exact abs_add_le _ _
  linarith

end H5EdgeFamilyCutoff

end SteklovAudit.H5CutoffInterface
