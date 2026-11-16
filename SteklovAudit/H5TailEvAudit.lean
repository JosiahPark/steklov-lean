import Mathlib
import SteklovAudit.H5TailEv

/-!
# G67: the eventual-tail inputs are no stronger than the L-dependent low inputs

Roadmap item G67. `ofLowL` turns any `H5bLowLInputs E Emod` (G62, `H5LowLinear.lean`) into
`H5bTailEvInputs E Emod` (G66, `H5TailEv.lean`): the `L`-dependent tail is the L-uniform
`τ ε γ M`, the tail bound is used only for `1 ≤ L`, and `tailVanish` holds with `L₀ = 0`.
So every G62 input set is a G66 input set; strictness is the subject of G68.

What this file does NOT prove: no field of either structure is proved for the Steklov operator of
the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5TailEvAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5LowLinear
  SteklovAudit.H5TailEv

/-- **G67.** Every G62 input set is a G66 input set. -/
noncomputable def ofLowL {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bLowLInputs E Emod) :
    H5bTailEvInputs E Emod where
  nA := H.nA
  nB := H.nB
  D := H.D
  F := H.F
  disc := H.disc
  cutoff := H.cutoff
  discVanish := H.discVanish
  Cm := H.Cm
  Ck := H.Ck
  hCm := H.hCm
  pde := H.pde
  τ := fun ε γ M _ => H.τ ε γ M
  tail := fun ε γ M L _ => H.tail ε γ M L
  tailVanish := by
    intro ε γ hε hγ δ hδ
    obtain ⟨M, hM⟩ := H.tailVanish ε γ hε hγ δ hδ
    exact ⟨M, 0, fun _ _ => hM⟩
  κ2 := H.κ2
  lowDefect := H.lowDefect
  mLo := H.mLo
  lowMass := H.lowMass
  Λ0 := H.Λ0
  hΛ0 := H.hΛ0
  lam := H.lam
  hlam := H.hlam
  lipHi := H.lipHi
  lipLo := H.lipLo
  lowVanish := H.lowVanish

theorem ofLowL_nA {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bLowLInputs E Emod) :
    (ofLowL H).nA = H.nA := rfl

theorem ofLowL_τ {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bLowLInputs E Emod) (ε γ M L : ℝ) :
    (ofLowL H).τ ε γ M L = H.τ ε γ M := rfl

/-- The G62 inputs, routed through G66, give the H5b comparison (7.29). -/
theorem ofLowL_target {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bLowLInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_tailEv (ofLowL H)

end SteklovAudit.H5TailEvAudit
