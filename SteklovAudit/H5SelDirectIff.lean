import Mathlib
import SteklovAudit.H5SelDirectAudit
import SteklovAudit.H5JointSelIff

/-!
# G82: the F2 audit for the direct selector form of the H5b inputs

Roadmap item G82. With the cutoff data `D` unconstrained, the direct selector form
`H5bSelDirectInputs E Emod` (G80, `H5SelDirect.lean`) is equivalent to the target
`H5bTarget E Emod`: one direction is `h5b_of_selDirectInputs`, the other takes the G79 witness
(`H5JointSelIff.selInputs_iff_target`) and maps it through `H5SelDirectAudit.ofSel` (G81).
As with F1, G72 and G77, the content of the direct form sits in the `cutoff`/`disc` row once `D`
is constrained by the operator.

`selDirect_nonempty_zero` is a satisfiability check (non-vacuity): the structure has an
inhabitant for `E = Emod = 0`.

What this file does NOT prove: no field (row) of `H5bSelDirectInputs` is proved for the Steklov
operator of the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1
remain conditional. This is an audit only.
-/

namespace SteklovAudit.H5SelDirectIff

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
  SteklovAudit.H5JointSel SteklovAudit.H5SelDirect

/-- **G82 (F2 audit, direct selector form).** The direct inputs hold exactly when the target
holds. -/
theorem selDirect_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bSelDirectInputs E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_selDirectInputs H,
   fun h => Nonempty.map H5SelDirectAudit.ofSel
     ((H5JointSelIff.selInputs_iff_target E Emod).2 h)⟩

/-- Satisfiability: an explicit witness with `E = Emod = 0`. -/
theorem selDirect_nonempty_zero :
    Nonempty (H5bSelDirectInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ))) :=
  Nonempty.map H5SelDirectAudit.ofSel H5JointSelIff.selInputs_nonempty_zero

end SteklovAudit.H5SelDirectIff
