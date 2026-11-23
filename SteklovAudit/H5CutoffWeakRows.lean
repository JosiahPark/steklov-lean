import Mathlib
import SteklovAudit.WindowDefectFullTrace
import SteklovAudit.H5CutoffRatioSufficient
import SteklovAudit.FullTraceSmallSeparate

/-!
# The H5 cutoff route on row (ii) plus three weaker named inputs (roadmap item G137)

G122 (`h5_of_cutoff_route`) needs three rows: (i) `RatioLittleO`, (ii) `TraceMatches D` and
(iii) `FullTraceSmall`. G136 replaces (i) by `GapLinear` and `EnergySmall`
(`ratioLittleO_of_gap_energy`), and G135 replaces (iii) by `WindowTraceBound`
(`fullTraceSmall_of_window`). This file puts the pieces together:

* `h5_of_weak_rows`: (ii) + `GapLinear` + `EnergySmall` + `WindowTraceBound` give `|D L| = o(L)`.
* Non-vacuity: the zero family of G132 (`zeroFamily`) satisfies `GapLinear` (`c = 1/2`, `L₁ = 1`),
  `EnergySmall` and `WindowTraceBound` (`C = K = 0`, `ε = 0`); `weak_rows_zeroFamily` bundles the three.
* `weak_rows_need_traceMatches`: for the same family and `D L = L`, the three weaker inputs hold but
  (ii) fails, so (ii) cannot be dropped: it is the only row that links the probe family to `D`.

What this file does NOT prove: (ii), `GapLinear`, `EnergySmall` or `WindowTraceBound` for the actual
edge family, the existence of such a family, (7.29), H5, or Theorem 1.3 / 11.1. All four inputs of
`h5_of_weak_rows` are named hypotheses; the zero family is a toy with zero weights.
-/

namespace SteklovAudit.H5CutoffWeakRows

open SteklovAudit.H5CutoffInterface SteklovAudit.FullTraceSmallSeparate

/-- **G137.** Row (ii), a linear gap, `Lip · E = o(L²)` and the window-shaped trace bound give
`|D L| = o(L)`. -/
theorem h5_of_weak_rows {ι κ : Type*} (Y : H5EdgeFamilyCutoff ι κ) (D : ℝ → ℝ)
    {c L₁ C K : ℝ} {ε : ℝ → ℝ} (h2 : Y.TraceMatches D) (hg : Y.GapLinear c L₁)
    (he : Y.EnergySmall) (hw : Y.WindowTraceBound C K ε) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |D L| ≤ η * L :=
  Y.h5_of_cutoff_window D (Y.ratioLittleO_of_gap_energy hg he) h2 hw

/-- Non-vacuity: the zero family keeps the linear gap `L / 2` below the cutoff for `L ≥ 1`. -/
theorem gapLinear_zeroFamily : zeroFamily.GapLinear (1 / 2) 1 := by
  unfold H5EdgeFamilyCutoff.GapLinear
  refine ⟨by norm_num, fun L hL => ?_⟩
  first
    | (show (1 / 2 : ℝ) * L ≤ L - 0; linarith)
    | (simp [zeroFamily]; linarith)

/-- Non-vacuity: for the zero family `Lip · E = 1 · 0`, so `EnergySmall` holds. -/
theorem energySmall_zeroFamily : zeroFamily.EnergySmall := by
  unfold H5EdgeFamilyCutoff.EnergySmall
  intro η hη
  refine ⟨0, fun L _ => ?_⟩
  have h : (0 : ℝ) ≤ η * L ^ 2 := mul_nonneg hη.le (sq_nonneg L)
  first
    | (show (1 : ℝ) * 0 ≤ η * L ^ 2; linarith)
    | (simp [zeroFamily, zeroCert] <;> nlinarith [h])

/-- Non-vacuity: the zero family satisfies `WindowTraceBound` with `C = K = 0`, `ε = 0`. -/
theorem windowTraceBound_zeroFamily : zeroFamily.WindowTraceBound 0 0 (fun _ => 0) :=
  zeroFamily.windowTraceBound_of_trace_zero S_zero

/-- **G137.** The three weaker inputs are jointly satisfiable. -/
theorem weak_rows_zeroFamily :
    zeroFamily.GapLinear (1 / 2) 1 ∧ zeroFamily.EnergySmall ∧
      zeroFamily.WindowTraceBound 0 0 (fun _ => 0) :=
  ⟨gapLinear_zeroFamily, energySmall_zeroFamily, windowTraceBound_zeroFamily⟩

/-- **G137.** Row (ii) cannot be dropped: the zero family satisfies the three weaker inputs, yet
`D L = L` is not `o(L)`, so `TraceMatches idD` fails. -/
theorem weak_rows_need_traceMatches : ¬ zeroFamily.TraceMatches idD := fun h =>
  not_littleO_idD (h5_of_weak_rows zeroFamily idD h gapLinear_zeroFamily energySmall_zeroFamily
    windowTraceBound_zeroFamily)

end SteklovAudit.H5CutoffWeakRows
