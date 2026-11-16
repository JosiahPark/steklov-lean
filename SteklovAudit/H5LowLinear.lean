import Mathlib
import SteklovAudit.H5Compare

/-!
# G62: the H5b comparison with an L-dependent low-energy row

Roadmap item G62. `H5bLowLInputs E Emod` has the fields of `H5bInputs` (from `H5Compare.lean`),
except that the L-uniform low-energy row (`κ2`, `lowDefect`, `lamVanish`) is replaced by:

* `κ2 ε γ M L` and `lowDefect`: a low-energy defect bound that may depend on `L`;
* `mLo ε γ M L` and `lowMass`: a separate bound on the low-energy spectral mass;
* `lowVanish`: the product `lam · √(κ2 · mLo)` is `o(L)` for each fixed split energy `M`.

`h5b_of_lowLInputs` proves `H5bTarget E Emod` by the same chain as `h5b_of_inputs`
(`cumulative_transfer_bound`, then `little_o_of_vanishing_tail`).

What this file does NOT prove: no field is proved for the Steklov operator of the tetrahedron;
no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional. The F2 caveat
on the `cutoff` row (unconstrained cutoff data `D`) applies here unchanged.
-/

namespace SteklovAudit.H5LowLinear

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- The named inputs of (7.29) with an `L`-dependent low-energy row. -/
structure H5bLowLInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
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
  τ : ℝ → ℝ → ℝ → ℝ
  tail : ∀ ε γ M L : ℝ, hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M
  tailVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ → ∃ M, τ ε γ M ≤ δ
  /-- Row: low-energy defect bound, allowed to depend on `L`. -/
  κ2 : ℝ → ℝ → ℝ → ℝ → ℝ
  lowDefect : ∀ ε γ M L : ℝ,
    hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).K) ≤ κ2 ε γ M L
  /-- Low-energy spectral mass, kept as its own bound. -/
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
  /-- Row: the low-energy term is `o(L)` for each fixed split energy. -/
  lowVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    lam ε γ M L * Real.sqrt (κ2 ε γ M L * mLo ε γ M L) ≤ η * L

/-- **G62.** The `L`-dependent low-energy inputs give the H5b comparison (7.29). -/
theorem h5b_of_lowLInputs {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bLowLInputs E Emod) :
    H5bTarget E Emod := by
  unfold H5bTarget
  intro ε γ hε hγ η hη
  have key : ∀ M L : ℝ, 1 ≤ L → |E ε γ L - Emod ε γ L| ≤
      H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) * Real.sqrt (H.τ ε γ M) * (1 + L)
        + (H.lam ε γ M L * Real.sqrt (H.κ2 ε γ M L * H.mLo ε γ M L) + H.disc ε γ L) := by
    intro M L hL
    have hL0 : 0 ≤ 1 + L := by linarith
    have hm : hs2 (H.D ε γ L).J ≤ H.Cm ε γ * (1 + L) ^ 2 := (H.pde ε γ L).mass
    have hb := cumulative_transfer_bound (H.D ε γ L) (H.F ε γ L) (hiE (H.D ε γ L) M)
      (H.Λ0 ε γ) (H.lam ε γ M L) (H.τ ε γ M) (H.Cm ε γ * (1 + L) ^ 2) (H.κ2 ε γ M L)
      (H.mLo ε γ M L) (H.hΛ0 ε γ) (H.hlam ε γ M L) (H.lipHi ε γ M L)
      (H.lipLo ε γ M L) (H.tail ε γ M L) (le_trans (hs2_mask_le _ _) hm)
      (H.lowDefect ε γ M L) (H.lowMass ε γ M L)
    have e1 : Real.sqrt (H.τ ε γ M * (H.Cm ε γ * (1 + L) ^ 2))
        = Real.sqrt (H.τ ε γ M) * Real.sqrt (H.Cm ε γ) * (1 + L) := by
      rw [show H.τ ε γ M * (H.Cm ε γ * (1 + L) ^ 2) = (H.τ ε γ M * H.Cm ε γ) * (1 + L) ^ 2 by
        ring, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_mul' _ (H.hCm ε γ), Real.sqrt_sq hL0]
    rw [e1] at hb
    have e3 : H.Λ0 ε γ * (Real.sqrt (H.τ ε γ M) * Real.sqrt (H.Cm ε γ) * (1 + L))
        = H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) * Real.sqrt (H.τ ε γ M) * (1 + L) := by ring
    rw [e3] at hb
    have hc := H.cutoff ε γ L
    have h4 := abs_sub_abs_le_abs_sub (E ε γ L - Emod ε γ L) (∑ i, ∑ j,
      (H.F ε γ L ((H.D ε γ L).a i) - H.F ε γ L ((H.D ε γ L).b j)) * (H.D ε γ L).J i j ^ 2)
    linarith
  have htail : ∀ δ : ℝ, 0 < δ → ∃ M, Real.sqrt (H.τ ε γ M) ≤ δ := by
    intro δ hδ
    obtain ⟨M, hM⟩ := H.tailVanish ε γ hε hγ (δ ^ 2) (by positivity)
    refine ⟨M, ?_⟩
    calc Real.sqrt (H.τ ε γ M) ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hM
      _ = δ := Real.sqrt_sq hδ.le
  have hlow : ∀ M δ : ℝ, 0 < δ → ∃ L0 : ℝ, ∀ L, L0 ≤ L →
      H.lam ε γ M L * Real.sqrt (H.κ2 ε γ M L * H.mLo ε γ M L) + H.disc ε γ L ≤ δ * L := by
    intro M δ hδ
    obtain ⟨L1, h1⟩ := H.lowVanish ε γ hε hγ M (δ / 2) (half_pos hδ)
    obtain ⟨L2, h2⟩ := H.discVanish ε γ hε hγ (δ / 2) (half_pos hδ)
    refine ⟨max L1 L2, fun L hL => ?_⟩
    have a1 := h1 L (le_trans (le_max_left _ _) hL)
    have a2 := h2 L (le_trans (le_max_right _ _) hL)
    have a3 : δ / 2 * L + δ / 2 * L = δ * L := by ring
    linarith
  exact little_o_of_vanishing_tail (fun L => E ε γ L - Emod ε γ L)
    (H.Λ0 ε γ * Real.sqrt (H.Cm ε γ)) (mul_nonneg (H.hΛ0 ε γ) (Real.sqrt_nonneg _))
    (fun M => Real.sqrt (H.τ ε γ M))
    (fun M L => H.lam ε γ M L * Real.sqrt (H.κ2 ε γ M L * H.mLo ε γ M L) + H.disc ε γ L)
    (fun M => Real.sqrt_nonneg _) key htail hlow η hη

end SteklovAudit.H5LowLinear
