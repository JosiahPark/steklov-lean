import Mathlib
import SteklovAudit.H5SelDirect

/-!
# G81: the direct selector row is no stronger than the selector row

Roadmap item G81. `ofSel` turns any `H5bJointSelInputs E Emod` (G77, `H5JointSel.lean`) into
`H5bSelDirectInputs E Emod` (G80, `H5SelDirect.lean`): the shared fields are copied, and
`directVanish` follows from `selVanish` at the same `η`, with the same selector `Msel` and the
threshold `max 1 L₀` (the `tail` row of G77 needs `1 ≤ L`). Each masked `hs2` product is bounded by
the corresponding `τ · mHi` / `κ2 · mLo` product, then `√` and the nonnegative weights `Λ0`, `lam`
preserve the bound. So every G77 input set is a G80 input set, and `ofSel_target` recovers (7.29)
through G80. F table text: the four bounding functions τ, mHi, κ2, mLo are needed only along the
chosen split.

What this file does NOT prove: no field (row) of either structure is proved for the Steklov
operator of the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain
conditional. It does not show that G80 is strictly weaker than G77. The F2 caveat on the
`cutoff` row applies unchanged (that is G82).
-/

namespace SteklovAudit.H5SelDirectAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
  SteklovAudit.H5JointSel SteklovAudit.H5SelDirect

/-- **G81.** Every G77 input set is a G80 input set. -/
noncomputable def ofSel {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bJointSelInputs E Emod) :
    H5bSelDirectInputs E Emod where
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
  Λ0 := H.Λ0
  hΛ0 := H.hΛ0
  lam := H.lam
  hlam := H.hlam
  lipHi := H.lipHi
  lipLo := H.lipLo
  directVanish := by
    intro ε γ hε hγ η hη
    obtain ⟨Msel, L₀, h⟩ := H.selVanish ε γ hε hγ η hη
    refine ⟨Msel, max 1 L₀, fun L hL => ?_⟩
    have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
    have hL0 : L₀ ≤ L := le_trans (le_max_right _ _) hL
    have hK1 := H.tail ε γ (Msel L) L hL1
    have hJ1 := H.hiMass ε γ (Msel L) L
    have hK2 := H.lowDefect ε γ (Msel L) L
    have hJ2 := H.lowMass ε γ (Msel L) L
    have p1 : hs2 (mask (hiE (H.D ε γ L) (Msel L)) (H.D ε γ L).K)
        * hs2 (mask (hiE (H.D ε γ L) (Msel L)) (H.D ε γ L).J)
        ≤ H.τ ε γ (Msel L) L * H.mHi ε γ (Msel L) L :=
      mul_le_mul hK1 hJ1 (hs2_nonneg _) (le_trans (hs2_nonneg _) hK1)
    have p2 : hs2 (mask (fun i j => ¬ hiE (H.D ε γ L) (Msel L) i j) (H.D ε γ L).K)
        * hs2 (mask (fun i j => ¬ hiE (H.D ε γ L) (Msel L) i j) (H.D ε γ L).J)
        ≤ H.κ2 ε γ (Msel L) L * H.mLo ε γ (Msel L) L :=
      mul_le_mul hK2 hJ2 (hs2_nonneg _) (le_trans (hs2_nonneg _) hK2)
    have r1 : Real.sqrt (hs2 (mask (hiE (H.D ε γ L) (Msel L)) (H.D ε γ L).K)
        * hs2 (mask (hiE (H.D ε γ L) (Msel L)) (H.D ε γ L).J))
        ≤ Real.sqrt (H.τ ε γ (Msel L) L * H.mHi ε γ (Msel L) L) := by
      first
        | exact Real.sqrt_le_sqrt p1
        | gcongr
    have r2 : Real.sqrt (hs2 (mask (fun i j => ¬ hiE (H.D ε γ L) (Msel L) i j) (H.D ε γ L).K)
        * hs2 (mask (fun i j => ¬ hiE (H.D ε γ L) (Msel L) i j) (H.D ε γ L).J))
        ≤ Real.sqrt (H.κ2 ε γ (Msel L) L * H.mLo ε γ (Msel L) L) := by
      first
        | exact Real.sqrt_le_sqrt p2
        | gcongr
    have s1 := mul_le_mul_of_nonneg_left r1 (H.hΛ0 ε γ)
    have s2 := mul_le_mul_of_nonneg_left r2 (H.hlam ε γ (Msel L) L)
    exact le_trans (add_le_add s1 s2) (h L hL0)

theorem ofSel_Λ0 {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bJointSelInputs E Emod) :
    (ofSel H).Λ0 = H.Λ0 := rfl

/-- The G77 inputs, routed through G80, give the H5b comparison (7.29). -/
theorem ofSel_target {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bJointSelInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_selDirectInputs (ofSel H)

end SteklovAudit.H5SelDirectAudit
