import Mathlib
import SteklovAudit.H5HiLinear

/-!
# G70: the high-mass inputs are no stronger than the eventual-tail inputs

Roadmap item G70. `ofTailEv` turns any `H5bTailEvInputs E Emod` (G66, `H5TailEv.lean`) into
`H5bHiLInputs E Emod` (G69, `H5HiLinear.lean`): the high-energy mass bound is the full mass bound
`Cm (1 + L)²` from `pde.mass` (via `hs2_mask_le`), and `hiVanish` follows from `tailVanish` by the
identity `√(τ · (Cm (1 + L)²)) = √τ · √Cm · (1 + L)` and the scalar step `hi_term_le`.
So every G66 input set is a G69 input set: the high-energy row may be stated as one product
bound `Λ0 · √(τ · mHi) = o(L)` at a single split energy `M`.

What this file does NOT prove: no field of either structure is proved for the Steklov operator of
the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
Strictness of G69 over G66 is not claimed here.
-/

namespace SteklovAudit.H5HiLinearAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5TailEv
  SteklovAudit.H5HiLinear

/-- Scalar step: if `0 ≤ t ≤ d` and `C · d · 4 ≤ δ` then `C · t · (1 + L) ≤ δ L` for `L ≥ 1`. -/
theorem hi_term_le {C t d L δ : ℝ} (hC : 0 ≤ C) (ht0 : 0 ≤ t) (hL : 1 ≤ L) (ht : t ≤ d)
    (hd : C * d * 4 ≤ δ) : C * t * (1 + L) ≤ δ * L := by
  have hd0 : 0 ≤ d := le_trans ht0 ht
  have k1 : C * t ≤ C * d := mul_le_mul_of_nonneg_left ht hC
  have k2 : C * t * (1 + L) ≤ C * d * (2 * L) :=
    mul_le_mul k1 (by linarith) (by linarith) (mul_nonneg hC hd0)
  have k3 : C * d * (2 * L) = (C * d * 4) * (L / 2) := by ring
  have k4 : (C * d * 4) * (L / 2) ≤ δ * (L / 2) := mul_le_mul_of_nonneg_right hd (by linarith)
  have hδ : 0 ≤ δ := le_trans (mul_nonneg (mul_nonneg hC hd0) (by norm_num)) hd
  have k5 : δ * (L / 2) ≤ δ * L := mul_le_mul_of_nonneg_left (by linarith) hδ
  linarith

/-- **G70.** Every G66 input set is a G69 input set. -/
noncomputable def ofTailEv {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bTailEvInputs E Emod) :
    H5bHiLInputs E Emod where
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
  mHi := fun ε γ _ L => H.Cm ε γ * (1 + L) ^ 2
  hiMass := fun ε γ _ L => le_trans (hs2_mask_le _ _) (H.pde ε γ L).mass
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
  hiVanish := by
    intro ε γ hε hγ δ hδ
    have hC : 0 ≤ H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) :=
      mul_nonneg (H.hΛ0 ε γ) (Real.sqrt_nonneg _)
    have hpos : 0 < 4 * (H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) + 1) := by linarith
    have hd0 : 0 < δ / (4 * (H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) + 1)) := div_pos hδ hpos
    obtain ⟨M, L₀, hM⟩ := H.tailVanish ε γ hε hγ
      ((δ / (4 * (H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) + 1))) ^ 2) (pow_pos hd0 2)
    refine ⟨M, max L₀ 1, fun L hL => ?_⟩
    have hLone : 1 ≤ L := le_trans (le_max_right _ _) hL
    have hτ := hM L (le_trans (le_max_left _ _) hL)
    have hs : Real.sqrt (H.τ ε γ M L)
        ≤ δ / (4 * (H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) + 1)) := by
      have h' := Real.sqrt_le_sqrt hτ
      rwa [Real.sqrt_sq hd0.le] at h'
    have hdd : δ / (4 * (H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) + 1))
        * (4 * (H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) + 1)) ≤ δ :=
      (le_div_iff₀ hpos).1 le_rfl
    have h4 : H.Λ0 ε γ * Real.sqrt (H.Cm ε γ)
        * (δ / (4 * (H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) + 1))) * 4 ≤ δ := by
      nlinarith [hd0, hdd]
    have hL0 : 0 ≤ 1 + L := by linarith
    have e1 : Real.sqrt (H.τ ε γ M L * (H.Cm ε γ * (1 + L) ^ 2))
        = Real.sqrt (H.τ ε γ M L) * Real.sqrt (H.Cm ε γ) * (1 + L) := by
      rw [show H.τ ε γ M L * (H.Cm ε γ * (1 + L) ^ 2)
          = (H.τ ε γ M L * H.Cm ε γ) * (1 + L) ^ 2 by ring,
        Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hL0, Real.sqrt_mul' _ (H.hCm ε γ)]
    show H.Λ0 ε γ * Real.sqrt (H.τ ε γ M L * (H.Cm ε γ * (1 + L) ^ 2)) ≤ δ * L
    rw [e1, show H.Λ0 ε γ * (Real.sqrt (H.τ ε γ M L) * Real.sqrt (H.Cm ε γ) * (1 + L))
        = H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) * Real.sqrt (H.τ ε γ M L) * (1 + L) by ring]
    exact hi_term_le hC (Real.sqrt_nonneg _) hLone hs h4

theorem ofTailEv_nA {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bTailEvInputs E Emod) :
    (ofTailEv H).nA = H.nA := rfl

theorem ofTailEv_mHi {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bTailEvInputs E Emod) (ε γ M L : ℝ) :
    (ofTailEv H).mHi ε γ M L = H.Cm ε γ * (1 + L) ^ 2 := rfl

/-- The G66 inputs, routed through G69, give the H5b comparison (7.29). -/
theorem ofTailEv_target {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bTailEvInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_hiLInputs (ofTailEv H)

end SteklovAudit.H5HiLinearAudit
