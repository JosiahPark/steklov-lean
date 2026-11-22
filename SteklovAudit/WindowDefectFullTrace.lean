import Mathlib
import SteklovAudit.H5CutoffTerminal
import SteklovAudit.CumulativeBudgetQuantifiers

/-!
# Row (iii) of the H5 cutoff route from a window-shaped bound (roadmap item G135)

Row (iii) of the H5 cutoff route (`FullTraceSmall`, G122) asks for `S_L = o(L)` for the full probe
trace. This file replaces it by the named hypothesis `WindowTraceBound Y C K ε`: `C, K ≥ 0`,
`ε h → 0` as `h ↓ 0` (in the upper-bound form used by G133), and for every window `T > 0`, eventually
`|S_L| ≤ C L / T + K T L ε(1/L)`. This is the shape that G129/G130/G134 produce: a uniform window tail
`C L / T` plus the windowed HS defect `K T L ε(1/L)`.

* `fullTraceSmall_of_window`: `WindowTraceBound` gives (iii), via
  `CumulativeBudgetQuantifiers.littleO_of_window_defect`.
* `h5_of_cutoff_window`: (i) + (ii) + `WindowTraceBound` give `|D L| = o(L)`, via `h5_of_cutoff_route`.
* `windowTraceBound_of_trace_zero`: a family with vanishing probe trace satisfies `WindowTraceBound`
  with `C = K = 0`, `ε = 0`, so the hypothesis is not vacuous.

What this file does NOT prove: `WindowTraceBound` (the uniform tail `C L / T` or the vanishing HS defect
`ε(h) → 0`) for the actual edge family, rows (i) and (ii), the existence of such a family, (7.29), H5,
or Theorem 1.3 / 11.1. `WindowTraceBound` is a named hypothesis.
-/

namespace SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff

open Filter SteklovAudit.CumulativeBudgetQuantifiers

/-- Named hypothesis replacing row (iii): a window-shaped bound on the full probe trace `S_L`. -/
structure WindowTraceBound {ι κ : Type*} (Y : H5EdgeFamilyCutoff ι κ) (C K : ℝ) (ε : ℝ → ℝ) :
    Prop where
  C_nonneg : 0 ≤ C
  K_nonneg : 0 ≤ K
  eps_small : ∀ δ : ℝ, 0 < δ → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ε h ≤ δ
  bound : ∀ T : ℝ, 0 < T →
    ∀ᶠ L in atTop, |(Y.X L).S (Y.F L)| ≤ C * L / T + K * T * L * ε (1 / L)

variable {ι κ : Type*} (Y : H5EdgeFamilyCutoff ι κ)

/-- **G135.** The window-shaped bound gives row (iii), `S_L = o(L)`. -/
theorem fullTraceSmall_of_window {C K : ℝ} {ε : ℝ → ℝ} (hw : Y.WindowTraceBound C K ε) :
    Y.FullTraceSmall := by
  intro η hη
  have h := littleO_of_window_defect (fun L => (Y.X L).S (Y.F L)) C K hw.C_nonneg hw.K_nonneg ε
    hw.eps_small hw.bound η hη
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨L₀, fun L hL => hL₀ L hL⟩

/-- **G135.** (i) ratio `o(L)`, (ii) truncated-trace matching and the window-shaped bound give
`|D L| = o(L)`. -/
theorem h5_of_cutoff_window (D : ℝ → ℝ) {C K : ℝ} {ε : ℝ → ℝ} (h1 : Y.RatioLittleO)
    (h2 : Y.TraceMatches D) (hw : Y.WindowTraceBound C K ε) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |D L| ≤ η * L :=
  Y.h5_of_cutoff_route D h1 h2 (Y.fullTraceSmall_of_window hw)

/-- Non-vacuity: a family whose probe trace vanishes satisfies `WindowTraceBound` with `C = K = 0`
and `ε = 0`. -/
theorem windowTraceBound_of_trace_zero (hS : ∀ L, (Y.X L).S (Y.F L) = 0) :
    Y.WindowTraceBound 0 0 (fun _ => 0) :=
  { C_nonneg := le_refl 0
    K_nonneg := le_refl 0
    eps_small := fun δ hδ => ⟨1, one_pos, fun _ _ _ => le_of_lt hδ⟩
    bound := fun T _ => by
      filter_upwards with L
      rw [hS L]
      simp }

end SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff
