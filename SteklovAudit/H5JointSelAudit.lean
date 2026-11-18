import Mathlib
import SteklovAudit.H5JointSel

/-!
# G78: the selector row is no stronger than the joint row, and strictly weaker as a row shape

Roadmap item G78. `ofJoint` turns any `H5bJointInputs E Emod` (G72, `H5Joint.lean`) into
`H5bJointSelInputs E Emod` (G77, `H5JointSel.lean`): all fields are copied and the selector is the
constant `Msel := fun _ => M`, with `M` the split energy given by `jointVanish`. So every G72
input set is a G77 input set, and `ofJoint_target` recovers (7.29) through G77.

Strictness as row shapes: for `late M L := if L ≤ M then 0 else L`, the term is `o(L)` along the
selector `Msel L = L` (`sel_holds`), but at no fixed split energy `M` is it even `≤ L / 2` for all
large `L` (`const_fails`). F table text: the split energy in (7.29) may be chosen as a function of
`L`.

What this file does NOT prove: no field (row) of either structure is proved for the Steklov
operator of the tetrahedron; no DtN operator is constructed; `late` is a toy row shape, not a
quantity computed from the operator; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5JointSelAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
  SteklovAudit.H5Joint SteklovAudit.H5JointSel

/-- **G78.** Every G72 input set is a G77 input set (constant selector). -/
noncomputable def ofJoint {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bJointInputs E Emod) :
    H5bJointSelInputs E Emod where
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
  selVanish := by
    intro ε γ hε hγ η hη
    obtain ⟨M, L₀, h⟩ := H.jointVanish ε γ hε hγ η hη
    exact ⟨fun _ => M, L₀, fun L hL => h L hL⟩

theorem ofJoint_τ {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bJointInputs E Emod) :
    (ofJoint H).τ = H.τ := rfl

/-- The G72 inputs, routed through G77, give the H5b comparison (7.29). -/
theorem ofJoint_target {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bJointInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_jointSelInputs (ofJoint H)

/-- A toy row shape: zero once the split energy reaches `L`, and `L` before that. -/
noncomputable def late (M L : ℝ) : ℝ := if L ≤ M then 0 else L

/-- Along the selector `Msel L = L` the row `late` vanishes, so it is `o(L)`. -/
theorem sel_holds : ∀ η : ℝ, 0 < η → ∃ (Msel : ℝ → ℝ) (L₀ : ℝ), ∀ L, L₀ ≤ L →
    late (Msel L) L ≤ η * L := by
  intro η hη
  refine ⟨fun L => L, 0, fun L hL => ?_⟩
  show (if L ≤ L then (0 : ℝ) else L) ≤ η * L
  rw [if_pos le_rfl]
  exact mul_nonneg hη.le hL

/-- At no fixed split energy is `late` bounded by `L / 2` for all large `L`. -/
theorem const_fails : ¬ ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → late M L ≤ 1 / 2 * L := by
  rintro ⟨M, L₀, h⟩
  obtain ⟨L, hL0, hM, h1⟩ : ∃ L : ℝ, L₀ ≤ L ∧ M + 1 ≤ L ∧ 1 ≤ L :=
    ⟨max (max L₀ (M + 1)) 1, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  have hlt : ¬ L ≤ M := fun hle => by linarith
  have hv : late M L = L := by
    show (if L ≤ M then (0 : ℝ) else L) = L
    exact if_neg hlt
  have hb := h L hL0
  rw [hv] at hb
  linarith

/-- **G78.** The selector row is strictly weaker than the fixed-split row, as row shapes. -/
theorem sel_strictly_weaker :
    (∀ η : ℝ, 0 < η → ∃ (Msel : ℝ → ℝ) (L₀ : ℝ), ∀ L, L₀ ≤ L → late (Msel L) L ≤ η * L) ∧
      ¬ ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → late M L ≤ 1 / 2 * L :=
  ⟨sel_holds, const_fails⟩

end SteklovAudit.H5JointSelAudit
