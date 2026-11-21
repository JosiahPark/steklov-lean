import Mathlib
import SteklovAudit.H5GlobalLipRowsEv
import SteklovAudit.H5GlobalLipRowsAudit

/-!
# G96: the F2 audit for the eventual rows of the H5b inputs

Roadmap item G96. With the cutoff data `D` unconstrained, the eventual form
`H5bGlobalLipRowsEv E Emod` (G94, `H5GlobalLipRowsEv.lean`) is equivalent to the target
`H5bTarget E Emod`: one direction is `h5b_of_globalLipRowsEv`; the other is
`ofRows (H5GlobalLipRowsAudit.ofTarget h)`, which uses empty spectral data (`nA = nB = 0`),
`F = 0`, `Λ = m = 0`, and puts the whole comparison into the `disc` row. As with F2, G87 and
G91, the content sits in the `cutoff`/`disc` row; `massEv` and `defectSmall` carry content only
once `D` is the operator's cutoff data.

`globalLipRowsEv_nonempty_zero` is a satisfiability check (non-vacuity) for `E = Emod = 0`.

What this file does NOT prove: no field (row) of `H5bGlobalLipRowsEv` is proved for the Steklov
operator of the tetrahedron; whether the paper supplies `massEv` or `defectSmall` is open; no
DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional. Audit only.
-/

namespace SteklovAudit.H5GlobalLipRowsEvAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5GlobalLipRowsEv

/-- **G96 (F2 audit, eventual rows).** The eventual rows hold exactly when the target holds. -/
theorem globalLipRowsEv_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bGlobalLipRowsEv E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_globalLipRowsEv H,
    fun h => ⟨ofRows (H5GlobalLipRowsAudit.ofTarget h)⟩⟩

/-- The target-built eventual rows have mass constant `m = 0`. -/
theorem ofTarget_ev_m {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    (ofRows (H5GlobalLipRowsAudit.ofTarget h)).m = fun _ _ => 0 := rfl

/-- Satisfiability: an explicit witness with `E = Emod = 0`. -/
theorem globalLipRowsEv_nonempty_zero :
    Nonempty (H5bGlobalLipRowsEv (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ))) :=
  (globalLipRowsEv_iff_target _ _).2
    (h5b_of_globalLipRows (Classical.choice H5GlobalLipRowsAudit.globalLipRows_nonempty_zero))

end SteklovAudit.H5GlobalLipRowsEvAudit
