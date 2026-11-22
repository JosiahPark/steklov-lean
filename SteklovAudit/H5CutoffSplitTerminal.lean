import Mathlib
import SteklovAudit.H5CutoffTerminal
import SteklovAudit.CumulativeBudgetSplit

/-!
# Row (iii) of the H5 cutoff route as a split estimate (roadmap item G128)

G122 (`h5_of_cutoff_route`) needs (iii) `FullTraceSmall`: the full probe trace `S_L` is `o(L)`.
Here (iii) is replaced by the named split input `FullTraceSplit C`: for each cutoff `M > 0` there is
a fixed-`M` part `P` with `P L = o(L)` and a tail `|S_L − P L| ≤ C L / M`, with ONE constant
`C ≥ 0` independent of `M` and `L` (the same shape as the τ(M) row).

* `fullTraceSmall_of_split`: the split gives (iii), via `CumulativeBudgetSplit.littleO_of_split`.
* `h5_of_cutoff_split`: (i), (ii) and the split give `|D L| = o(L)`.
* `fullTraceSplit_of_small`, `fullTraceSplit_iff`: the split is not stronger than (iii)
  (take `P = S`, `C = 0`), so this is an equivalent reformulation that exposes the order of limits.

What this file does NOT prove: the split, (i), (ii) or (iii) for an actual edge family, the
existence of such a family, the uniform high-energy tail `C/M`, (7.29), H5, or Theorem 1.3 / 11.1.
`FullTraceSplit` is a named hypothesis.
-/

namespace SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff

open Filter

variable {ι κ : Type*} (Y : H5EdgeFamilyCutoff ι κ)

/-- Named split input for row (iii): a fixed-`M` part that is `o(L)` plus a tail `≤ C L / M`
with `C ≥ 0` uniform in `M`. -/
def FullTraceSplit (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ M : ℝ, 0 < M → ∃ P : ℝ → ℝ,
    (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |P L| ≤ η * L) ∧
      ∀ᶠ L in atTop, |(Y.X L).S (Y.F L) - P L| ≤ C * L / M

/-- **G128.** The split input implies (iii) `FullTraceSmall`. -/
theorem fullTraceSmall_of_split (C : ℝ) (h : Y.FullTraceSplit C) : Y.FullTraceSmall := by
  intro η hη
  have hev := SteklovAudit.CumulativeBudgetSplit.littleO_of_split
    (fun L => (Y.X L).S (Y.F L)) C h.1 h.2 η hη
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨L₀, fun L hL => hL₀ L hL⟩

/-- **G128.** (i) ratio `o(L)`, (ii) truncated-trace matching and the split input give
`|D L| = o(L)`. -/
theorem h5_of_cutoff_split (D : ℝ → ℝ) (h1 : Y.RatioLittleO) (h2 : Y.TraceMatches D)
    (C : ℝ) (h3 : Y.FullTraceSplit C) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |D L| ≤ η * L :=
  Y.h5_of_cutoff_route D h1 h2 (Y.fullTraceSmall_of_split C h3)

/-- Conversely (iii) gives the split with `P = S` and `C = 0`; the split is no stronger. -/
theorem fullTraceSplit_of_small (h : Y.FullTraceSmall) : Y.FullTraceSplit 0 := by
  refine ⟨le_refl 0, fun M _ => ⟨fun L => (Y.X L).S (Y.F L), fun η hη => ?_, ?_⟩⟩
  · obtain ⟨L₀, hL₀⟩ := h η hη
    exact Filter.eventually_atTop.mpr ⟨L₀, fun L hL => hL₀ L hL⟩
  · filter_upwards with L
    simp

/-- The split input (for some `C`) is equivalent to (iii). -/
theorem fullTraceSplit_iff : (∃ C : ℝ, Y.FullTraceSplit C) ↔ Y.FullTraceSmall :=
  ⟨fun ⟨C, h⟩ => Y.fullTraceSmall_of_split C h, fun h => ⟨0, Y.fullTraceSplit_of_small h⟩⟩

end SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff
