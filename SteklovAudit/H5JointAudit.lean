import Mathlib
import SteklovAudit.H5Joint

/-!
# G73: the joint-row inputs are no stronger than the high-mass inputs

Roadmap item G73. `ofHiL` turns any `H5bHiLInputs E Emod` (G69, `H5HiLinear.lean`) into
`H5bJointInputs E Emod` (G72, `H5Joint.lean`). All fields are copied; `jointVanish` is obtained
by taking the split energy `M` from `hiVanish` at `η / 2`, then `lowVanish` at that same `M` and
`η / 2`, and adding. So every G69 input set is a G72 input set.

What this file does NOT prove: no field of either structure is proved for the Steklov operator of
the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
Strictness of G72 over G69 (as row shapes) is G74, not claimed here.
-/

namespace SteklovAudit.H5JointAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
  SteklovAudit.H5HiLinear SteklovAudit.H5Joint

/-- **G73.** Every G69 input set is a G72 input set. -/
noncomputable def ofHiL {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bHiLInputs E Emod) :
    H5bJointInputs E Emod where
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
  τ := H.τ
  tail := H.tail
  mHi := H.mHi
  hiMass := H.hiMass
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
  jointVanish := by
    intro ε γ hε hγ η hη
    obtain ⟨M, L1, h1⟩ := H.hiVanish ε γ hε hγ (η / 2) (by linarith)
    obtain ⟨L2, h2⟩ := H.lowVanish ε γ hε hγ M (η / 2) (by linarith)
    refine ⟨M, max L1 L2, fun L hL => ?_⟩
    have a1 := h1 L (le_trans (le_max_left _ _) hL)
    have a2 := h2 L (le_trans (le_max_right _ _) hL)
    have a3 : η / 2 * L + η / 2 * L = η * L := by ring
    linarith

theorem ofHiL_nA {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bHiLInputs E Emod) :
    (ofHiL H).nA = H.nA := rfl

theorem ofHiL_τ {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bHiLInputs E Emod) :
    (ofHiL H).τ = H.τ := rfl

/-- The G69 inputs, routed through G72, give the H5b comparison (7.29). -/
theorem ofHiL_target {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bHiLInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_jointInputs (ofHiL H)

end SteklovAudit.H5JointAudit
