import Mathlib
import SteklovAudit.H5GlobalLipRowsPow
import SteklovAudit.H5GlobalLipRowsEvAudit

/-!
# G100: the F2 audit for the power trade-off rows of the H5b inputs

Roadmap item G100. With the cutoff data `D` unconstrained, the power form
`H5bGlobalLipRowsPow E Emod` (G98, `H5GlobalLipRowsPow.lean`) is equivalent to the target
`H5bTarget E Emod`: one direction is `h5b_of_globalLipRowsPow`; the other is
`ofEv (ofRows (H5GlobalLipRowsAudit.ofTarget h))`, which uses empty spectral data, `F = 0`,
`Λ = m = 0`, exponent `p = 1`, and puts the whole comparison into the `disc` row. As with F2,
G87, G91 and G96, the content sits in the `cutoff`/`disc` row; `massPow` and `defectPow` carry
content only once `D` is the operator's cutoff data.

`globalLipRowsPow_nonempty_zero` is a satisfiability check (non-vacuity) for `E = Emod = 0`.

F table text: the G98 rows are satisfiable and, like G90/G94, equivalent to the target only
through the unconstrained `cutoff` row; the F2 caveat stands.

What this file does NOT prove: no field (row) of `H5bGlobalLipRowsPow` is proved for the
Steklov operator of the tetrahedron; whether the paper supplies `massPow` or `defectPow` (for any
`p`) is open; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
Audit only.
-/

namespace SteklovAudit.H5GlobalLipRowsPowAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5GlobalLipRowsEv
  SteklovAudit.H5GlobalLipRowsPow

/-- **G100 (F2 audit, power rows).** The power rows hold exactly when the target holds. -/
theorem globalLipRowsPow_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bGlobalLipRowsPow E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_globalLipRowsPow H,
    fun h => ⟨H5GlobalLipRowsPow.ofEv (ofRows (H5GlobalLipRowsAudit.ofTarget h))⟩⟩

/-- The target-built power rows have exponent `p = 1`. -/
theorem ofTarget_pow_p {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    (H5GlobalLipRowsPow.ofEv (ofRows (H5GlobalLipRowsAudit.ofTarget h))).p = fun _ _ => 1 := rfl

/-- Satisfiability: an explicit witness with `E = Emod = 0`. -/
theorem globalLipRowsPow_nonempty_zero :
    Nonempty (H5bGlobalLipRowsPow (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ))) :=
  ⟨H5GlobalLipRowsPow.ofEv (Classical.choice H5GlobalLipRowsEvAudit.globalLipRowsEv_nonempty_zero)⟩

end SteklovAudit.H5GlobalLipRowsPowAudit
