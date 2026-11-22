import Mathlib
import SteklovAudit.H5CutoffInterface

/-!
# The terminal condition of the H5 cutoff route (roadmap item G122)

`full_trace_matches` (G116) turns (i) `RatioLittleO` and (ii) `TraceMatches D` into
`S_L − D L = o(L)`. To conclude `D L = o(L)` one needs a third estimate:

(iii) `FullTraceSmall`: the full probe trace satisfies `S_L = o(L)`.

`h5_of_cutoff_route` shows (i), (ii), (iii) give `|D L| = o(L)`. Item G123
(`H5CutoffObstruction.lean`) shows (iii) cannot be dropped from the abstract implication.

What this file does NOT prove: any of (i), (ii), (iii) for an actual edge family, the existence of
such a family, (7.29), H5, or Theorem 1.3 / 11.1. All three estimates remain named hypotheses.
-/

namespace SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff

variable {ι κ : Type*} (Y : H5EdgeFamilyCutoff ι κ)

/-- Open estimate (iii), named only: the full probe trace `S_L` is `o(L)`. -/
def FullTraceSmall : Prop :=
  ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |(Y.X L).S (Y.F L)| ≤ η * L

/-- **G122.** (i) ratio `o(L)`, (ii) truncated-trace matching and (iii) full-trace smallness
together give `|D L| = o(L)`. -/
theorem h5_of_cutoff_route (D : ℝ → ℝ) (h1 : Y.RatioLittleO) (h2 : Y.TraceMatches D)
    (h3 : Y.FullTraceSmall) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |D L| ≤ η * L := by
  intro η hη
  obtain ⟨L1, hL1⟩ := Y.full_trace_matches D h1 h2 (η / 2) (by linarith)
  obtain ⟨L2, hL2⟩ := h3 (η / 2) (by linarith)
  refine ⟨max L1 L2, fun L hL => ?_⟩
  have b1 := hL1 L (le_trans (le_max_left _ _) hL)
  have b2 := hL2 L (le_trans (le_max_right _ _) hL)
  have tri : |D L| ≤ |(Y.X L).S (Y.F L) - D L| + |(Y.X L).S (Y.F L)| := by
    have e : D L = -((Y.X L).S (Y.F L) - D L) + (Y.X L).S (Y.F L) := by ring
    have t : |-((Y.X L).S (Y.F L) - D L) + (Y.X L).S (Y.F L)| ≤
        |-((Y.X L).S (Y.F L) - D L)| + |(Y.X L).S (Y.F L)| := by
      first
        | exact abs_add _ _
        | exact abs_add_le _ _
    rw [abs_neg, ← e] at t
    exact t
  linarith

end SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff
