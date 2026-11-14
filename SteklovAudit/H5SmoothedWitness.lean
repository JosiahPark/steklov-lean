import Mathlib
import SteklovAudit.H5SmoothedIdent
import SteklovAudit.H5DiffAudit

/-!
# G42: the smoothed-route inputs are satisfiable and no stronger than the G35 form

Roadmap item G42.

* `H5bDiffInputs.toSmoothed`: every `H5bDiffInputs E Emod` (G35), for any `E`, `Emod`, gives an
  `H5bSmoothedInputs` (G40) by forgetting `e12`, `diffCount`, `e12Vanish`. So the G40 structure is
  no stronger than the G35 form.
* `toSmoothed_Esm`, `toSmoothed_Emodsm`, `toSmoothed_P`: the profile is kept and the smoothed
  counts of `W.toSmoothed` are built from the same coupled spectra as `W`.
* `smoothedWitness_nonempty`: `H5bSmoothedInputs` is not vacuous (G36's `diffWitness`, the empty
  family, composed with `toSmoothed`).
* `smoothed_witness_target`: some `W : H5bSmoothedInputs` has `H5bTarget W.Esm W.Emodsm`
  (from `h5b_of_smoothed`).

What this file does NOT prove: the witness is G24's empty family, a consistency check and not a
model of the Steklov spectrum; no E-free row (missing mass, Bessel, count, defect, tail, low count)
is proved for the Steklov operator of the tetrahedron or for any actual coupling; that the paper's
`E`, `Emod` equal the smoothed counts is not proved; no Dirichlet-to-Neumann operator is
constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5SmoothedWitness

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5MissingMass SteklovAudit.H5DiffCount SteklovAudit.H5SmoothedIdent

/-- **G42.** Forget the difference row: every G35 input set gives the G40 E-free rows. -/
noncomputable def _root_.SteklovAudit.H5DiffCount.H5bDiffInputs.toSmoothed
    {E Emod : ℝ → ℝ → ℝ → ℝ} (W : SteklovAudit.H5DiffCount.H5bDiffInputs E Emod) :
    SteklovAudit.H5SmoothedIdent.H5bSmoothedInputs where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  m1 := W.m1
  rowMiss := W.rowMiss
  m1Vanish := W.m1Vanish
  m2 := W.m2
  colMiss := W.colMiss
  m2Vanish := W.m2Vanish
  colBessel := W.colBessel
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
  bessel := W.bessel
  count := W.count
  defect := W.defect
  τ := W.τ
  tail := W.tail
  Cτ := W.Cτ
  tailRate := W.tailRate
  ha := W.ha
  hb := W.hb
  c := W.c
  lowCount := W.lowCount

/-- The smoothed true count of `W.toSmoothed` is built from `W`'s own spectrum and profile. -/
theorem toSmoothed_Esm {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bDiffInputs E Emod) :
    W.toSmoothed.Esm = fun ε γ L => ∑ i, W.P.φ ((W.D ε γ L).a i - L) := rfl

/-- The smoothed model count of `W.toSmoothed` is built from `W`'s own model spectrum. -/
theorem toSmoothed_Emodsm {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bDiffInputs E Emod) :
    W.toSmoothed.Emodsm = fun ε γ L => ∑ j, W.P.φ ((W.D ε γ L).b j - L) := rfl

/-- `toSmoothed` keeps the window profile. -/
theorem toSmoothed_P {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bDiffInputs E Emod) :
    W.toSmoothed.P = W.P := rfl

/-- **G42.** The smoothed-route structure is satisfiable. -/
theorem smoothedWitness_nonempty : Nonempty H5bSmoothedInputs :=
  ⟨H5bDiffInputs.toSmoothed SteklovAudit.H5DiffAudit.diffWitness⟩

/-- **G42.** Some smoothed-route input set gives (7.29) for its smoothed counts. -/
theorem smoothed_witness_target :
    ∃ W : H5bSmoothedInputs, H5bTarget W.Esm W.Emodsm :=
  ⟨H5bDiffInputs.toSmoothed SteklovAudit.H5DiffAudit.diffWitness,
    h5b_of_smoothed (H5bDiffInputs.toSmoothed SteklovAudit.H5DiffAudit.diffWitness)⟩

end SteklovAudit.H5SmoothedWitness
