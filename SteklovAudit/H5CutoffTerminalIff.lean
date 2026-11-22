import Mathlib
import SteklovAudit.H5CutoffTerminal

/-!
# Given (i) and (ii), the full-trace condition IS the target (companion to G122)

`H5CutoffTerminal.h5_of_cutoff_route` proves (i) + (ii) + (iii) ⇒ `D L = o(L)`. Here the converse:
(i) + (ii) + `D L = o(L)` ⇒ (iii) (`fullTraceSmall_of_h5`), so `h5_iff_fullTraceSmall`: given (i) and
(ii), `D L = o(L)` holds if and only if `S_L = o(L)`. The cutoff route therefore moves the whole
difficulty of H5 into the single estimate `S_L = o(L)`; (i) and (ii) alone carry none of it.

What this file does NOT prove: (i), (ii), (iii) for any actual edge family, (7.29), H5, or
Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.H5CutoffTerminalIff

open SteklovAudit.CountableCutoffTail SteklovAudit.H5CutoffInterface

variable {ι κ : Type*}

/-- Given (i) and (ii), `D L = o(L)` forces (iii). -/
theorem fullTraceSmall_of_h5 (Y : H5EdgeFamilyCutoff ι κ) (D : ℝ → ℝ)
    (h1 : Y.RatioLittleO) (h2 : Y.TraceMatches D)
    (hD : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |D L| ≤ η * L) :
    Y.FullTraceSmall := by
  intro η hη
  obtain ⟨L1, hL1⟩ := Y.full_trace_matches D h1 h2 (η / 2) (by linarith)
  obtain ⟨L2, hL2⟩ := hD (η / 2) (by linarith)
  refine ⟨max L1 L2, fun L hL => ?_⟩
  obtain ⟨a1, a2⟩ := abs_le.mp (hL1 L (le_trans (le_max_left _ _) hL))
  obtain ⟨b1, b2⟩ := abs_le.mp (hL2 L (le_trans (le_max_right _ _) hL))
  rw [abs_le]
  constructor <;> linarith

/-- Given (i) and (ii): `D L = o(L)` if and only if (iii). -/
theorem h5_iff_fullTraceSmall (Y : H5EdgeFamilyCutoff ι κ) (D : ℝ → ℝ)
    (h1 : Y.RatioLittleO) (h2 : Y.TraceMatches D) :
    (∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |D L| ≤ η * L) ↔ Y.FullTraceSmall :=
  ⟨fullTraceSmall_of_h5 Y D h1 h2, Y.h5_of_cutoff_route D h1 h2⟩

end SteklovAudit.H5CutoffTerminalIff
