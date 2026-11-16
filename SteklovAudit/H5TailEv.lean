import Mathlib
import SteklovAudit.H5LowLinear

/-!
# G66: the H5b comparison with an eventual, L-dependent high-energy tail

Roadmap item G66. `H5bTailEvInputs E Emod` has the fields of `H5bLowLInputs` (from
`H5LowLinear.lean`), except that the L-uniform tail row (`τ`, `tail`, `tailVanish`) is replaced by:

* `τ ε γ M L` and `tail`: a high-energy defect bound that may depend on `L`, required only for `1 ≤ L`;
* `tailVanish`: for every `δ > 0` there are a split energy `M` and a scale `L₀` with
  `τ ε γ M L ≤ δ` for all `L ≥ L₀`.

`h5b_of_tailEv` proves `H5bTarget E Emod` directly (not via `little_o_of_vanishing_tail`, whose
tail is L-free), using `cumulative_transfer_bound` at each `L ≥ 1`.

What this file does NOT prove: no field is proved for the Steklov operator of the tetrahedron;
no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional. The F2 caveat
on the `cutoff` row (unconstrained cutoff data `D`) applies here unchanged.
-/

namespace SteklovAudit.H5TailEv

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- The named inputs of (7.29) with an `L`-dependent low row and an eventual `L`-dependent tail. -/
structure H5bTailEvInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  F : ℝ → ℝ → ℝ → ℝ → ℝ
  disc : ℝ → ℝ → ℝ → ℝ
  cutoff : ∀ ε γ L : ℝ, |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j,
    (F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)) * (D ε γ L).J i j ^ 2| ≤ disc ε γ L
  discVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    disc ε γ L ≤ η * L
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  pde : ∀ ε γ L : ℝ, PDEInputs (D ε γ L) L (Cm ε γ) (Ck ε γ)
  /-- Row: high-energy defect tail, allowed to depend on `L`, needed only for `1 ≤ L`. -/
  τ : ℝ → ℝ → ℝ → ℝ → ℝ
  tail : ∀ ε γ M L : ℝ, 1 ≤ L → hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M L
  /-- Row: the tail is eventually small in `L` at some split energy. -/
  tailVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ → ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L →
    τ ε γ M L ≤ δ
  κ2 : ℝ → ℝ → ℝ → ℝ → ℝ
  lowDefect : ∀ ε γ M L : ℝ,
    hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).K) ≤ κ2 ε γ M L
  mLo : ℝ → ℝ → ℝ → ℝ → ℝ
  lowMass : ∀ ε γ M L : ℝ,
    hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).J) ≤ mLo ε γ M L
  Λ0 : ℝ → ℝ → ℝ
  hΛ0 : ∀ ε γ, 0 ≤ Λ0 ε γ
  lam : ℝ → ℝ → ℝ → ℝ → ℝ
  hlam : ∀ ε γ M L, 0 ≤ lam ε γ M L
  lipHi : ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), hiE (D ε γ L) M i j →
    |F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)|
      ≤ Λ0 ε γ * |(D ε γ L).a i - (D ε γ L).b j|
  lipLo : ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), ¬ hiE (D ε γ L) M i j →
    |F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)|
      ≤ lam ε γ M L * |(D ε γ L).a i - (D ε γ L).b j|
  lowVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    lam ε γ M L * Real.sqrt (κ2 ε γ M L * mLo ε γ M L) ≤ η * L

/-- **G66.** The eventual-tail inputs give the H5b comparison (7.29). -/
theorem h5b_of_tailEv {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bTailEvInputs E Emod) :
    H5bTarget E Emod := by
  unfold H5bTarget
  intro ε γ hε hγ η hη
  have key : ∀ M L : ℝ, 1 ≤ L → |E ε γ L - Emod ε γ L| ≤
      H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) * Real.sqrt (H.τ ε γ M L) * (1 + L)
        + (H.lam ε γ M L * Real.sqrt (H.κ2 ε γ M L * H.mLo ε γ M L) + H.disc ε γ L) := by
    intro M L hL
    have hL0 : 0 ≤ 1 + L := by linarith
    have hm : hs2 (H.D ε γ L).J ≤ H.Cm ε γ * (1 + L) ^ 2 := (H.pde ε γ L).mass
    have hb := cumulative_transfer_bound (H.D ε γ L) (H.F ε γ L) (hiE (H.D ε γ L) M)
      (H.Λ0 ε γ) (H.lam ε γ M L) (H.τ ε γ M L) (H.Cm ε γ * (1 + L) ^ 2) (H.κ2 ε γ M L)
      (H.mLo ε γ M L) (H.hΛ0 ε γ) (H.hlam ε γ M L) (H.lipHi ε γ M L)
      (H.lipLo ε γ M L) (H.tail ε γ M L hL) (le_trans (hs2_mask_le _ _) hm)
      (H.lowDefect ε γ M L) (H.lowMass ε γ M L)
    have e1 : Real.sqrt (H.τ ε γ M L * (H.Cm ε γ * (1 + L) ^ 2))
        = Real.sqrt (H.τ ε γ M L) * Real.sqrt (H.Cm ε γ) * (1 + L) := by
      rw [show H.τ ε γ M L * (H.Cm ε γ * (1 + L) ^ 2) = (H.τ ε γ M L * H.Cm ε γ) * (1 + L) ^ 2 by
        ring, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_mul' _ (H.hCm ε γ), Real.sqrt_sq hL0]
    rw [e1] at hb
    have e3 : H.Λ0 ε γ * (Real.sqrt (H.τ ε γ M L) * Real.sqrt (H.Cm ε γ) * (1 + L))
        = H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) * Real.sqrt (H.τ ε γ M L) * (1 + L) := by ring
    rw [e3] at hb
    have hc := H.cutoff ε γ L
    have h4 := abs_sub_abs_le_abs_sub (E ε γ L - Emod ε γ L) (∑ i, ∑ j,
      (H.F ε γ L ((H.D ε γ L).a i) - H.F ε γ L ((H.D ε γ L).b j)) * (H.D ε γ L).J i j ^ 2)
    linarith
  obtain ⟨C, hCe⟩ : ∃ C, H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) = C := ⟨_, rfl⟩
  have hC : 0 ≤ C := by rw [← hCe]; exact mul_nonneg (H.hΛ0 ε γ) (Real.sqrt_nonneg _)
  have hC1 : 0 < 4 * (C + 1) := by linarith
  have hne : 4 * (C + 1) ≠ 0 := ne_of_gt hC1
  obtain ⟨δ, hδe, hδ⟩ : ∃ δ : ℝ, δ * (4 * (C + 1)) = η ∧ 0 < δ :=
    ⟨η / (4 * (C + 1)), by first | exact div_mul_cancel₀ η hne | field_simp, div_pos hη hC1⟩
  have hCδ : C * δ ≤ η / 4 := by nlinarith [hδe, hδ.le]
  obtain ⟨M, L1, hM⟩ := H.tailVanish ε γ hε hγ (δ ^ 2) (pow_pos hδ 2)
  obtain ⟨L2, h2⟩ := H.lowVanish ε γ hε hγ M (η / 4) (by linarith)
  obtain ⟨L3, h3⟩ := H.discVanish ε γ hε hγ (η / 4) (by linarith)
  refine ⟨max (max 1 L1) (max L2 L3), fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLt : L1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL2 : L2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL3 : L3 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hs : Real.sqrt (H.τ ε γ M L) ≤ δ :=
    le_trans (Real.sqrt_le_sqrt (hM L hLt)) (le_of_eq (Real.sqrt_sq hδ.le))
  have k := key M L hL1
  rw [hCe] at k
  have s1 : C * Real.sqrt (H.τ ε γ M L) ≤ η / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hs hC) hCδ
  have s2 : C * Real.sqrt (H.τ ε γ M L) * (1 + L) ≤ η / 4 * (1 + L) :=
    mul_le_mul_of_nonneg_right s1 (by linarith)
  have s3 : η / 4 * (1 + L) ≤ η / 4 * (2 * L) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a2 := h2 L hL2
  have a3 := h3 L hL3
  have a4 : η / 4 * (2 * L) + η / 4 * L + η / 4 * L = η * L := by ring
  linarith

end SteklovAudit.H5TailEv
