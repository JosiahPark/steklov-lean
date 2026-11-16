import Mathlib
import SteklovAudit.H5LowLinear

/-!
# G63: the L-dependent low-energy inputs are no stronger than F1

Roadmap item G63. `ofInputs` turns any `H5bInputs E Emod` (F1, `H5Compare.lean`) into
`H5bLowLInputs E Emod` (G62, `H5LowLinear.lean`): the low-energy defect bound is the L-uniform
`κ2 ε γ M`, the low-energy mass bound is the full mass bound `Cm (1 + L)²`, and `lowVanish`
follows from `lamVanish` by the scalar step `low_term_le` (the `k2`–`k4` steps of `h5b_of_inputs`).
So every F1 input set is a G62 input set, and G62 is a (non-strict, so far) weakening of F1;
strictness on the count level is the subject of G64–G65.

What this file does NOT prove: no field of either structure is proved for the Steklov operator of
the tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5LowLinearAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5LowLinear

/-- Scalar step: if `lam · 4(s + 1) ≤ η` then `lam · s(1 + L) ≤ η L` for `L ≥ 1`. -/
theorem low_term_le {lam s L η : ℝ} (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hL : 1 ≤ L)
    (h : lam * (4 * (s + 1)) ≤ η) : lam * (s * (1 + L)) ≤ η * L := by
  have k2 : lam * (s * (1 + L)) ≤ lam * ((s + 1) * (2 * L)) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hs (sub_nonneg.2 hL)]) hlam
  have k3 : lam * ((s + 1) * (2 * L)) = (lam * (4 * (s + 1))) * (L / 2) := by ring
  have k4 : (lam * (4 * (s + 1))) * (L / 2) ≤ η * (L / 2) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  have hη : 0 ≤ η := le_trans (mul_nonneg hlam (by linarith)) h
  have k5 : η * (L / 2) ≤ η * L := mul_le_mul_of_nonneg_left (by linarith) hη
  linarith

/-- **G63.** Every F1 input set is a G62 input set. -/
noncomputable def ofInputs {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) :
    H5bLowLInputs E Emod where
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
  tailVanish := H.tailVanish
  κ2 := fun ε γ M _ => H.κ2 ε γ M
  lowDefect := fun ε γ M L => H.lowDefect ε γ M L
  mLo := fun ε γ _ L => H.Cm ε γ * (1 + L) ^ 2
  lowMass := fun ε γ _ L => le_trans (hs2_mask_le _ _) (H.pde ε γ L).mass
  Λ0 := H.Λ0
  hΛ0 := H.hΛ0
  lam := H.lam
  hlam := H.hlam
  lipHi := H.lipHi
  lipLo := H.lipLo
  lowVanish := by
    intro ε γ hε hγ M η hη
    obtain ⟨L1, h1⟩ := H.lamVanish ε γ hε hγ M
      (η / (4 * (Real.sqrt (H.κ2 ε γ M * H.Cm ε γ) + 1))) (div_pos hη (by positivity))
    refine ⟨max L1 1, fun L hL => ?_⟩
    have hLone : 1 ≤ L := le_trans (le_max_right _ _) hL
    have a1 := h1 L (le_trans (le_max_left _ _) hL)
    rw [le_div_iff₀ (by positivity)] at a1
    have hL0 : 0 ≤ 1 + L := by linarith
    have e2 : Real.sqrt (H.κ2 ε γ M * (H.Cm ε γ * (1 + L) ^ 2))
        = Real.sqrt (H.κ2 ε γ M * H.Cm ε γ) * (1 + L) := by
      rw [show H.κ2 ε γ M * (H.Cm ε γ * (1 + L) ^ 2) = (H.κ2 ε γ M * H.Cm ε γ) * (1 + L) ^ 2 by
        ring, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hL0]
    show H.lam ε γ M L * Real.sqrt (H.κ2 ε γ M * (H.Cm ε γ * (1 + L) ^ 2)) ≤ η * L
    rw [e2]
    exact low_term_le (H.hlam ε γ M L) (Real.sqrt_nonneg _) hLone a1

theorem ofInputs_nA {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) :
    (ofInputs H).nA = H.nA := rfl

theorem ofInputs_κ2 {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) (ε γ M L : ℝ) :
    (ofInputs H).κ2 ε γ M L = H.κ2 ε γ M := rfl

theorem ofInputs_mLo {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) (ε γ M L : ℝ) :
    (ofInputs H).mLo ε γ M L = H.Cm ε γ * (1 + L) ^ 2 := rfl

/-- F1 recovered through G62. -/
theorem ofInputs_target {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_lowLInputs (ofInputs H)

end SteklovAudit.H5LowLinearAudit
