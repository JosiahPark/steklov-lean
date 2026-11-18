import Mathlib
import SteklovAudit.H5JointSel

/-!
# G80: the selector row stated directly on the masked `hs2` quantities

Roadmap item G80. `H5bSelDirectInputs E Emod` has the fields of `H5bJointSelInputs` (from
`H5JointSel.lean`) without the bounding functions `τ`, `mHi`, `κ2`, `mLo` and their rows `tail`,
`hiMass`, `lowDefect`, `lowMass`. The row `selVanish` is replaced by `directVanish`: for every
`η > 0` there are a split-energy selector `Msel : ℝ → ℝ` and a scale `L₀` with
`Λ0 ε γ * √(hs2 K_hi * hs2 J_hi) + lam ε γ (Msel L) L * √(hs2 K_lo * hs2 J_lo) ≤ η * L`
for all `L ≥ L₀`, where `K_hi`, `J_hi` (resp. `K_lo`, `J_lo`) are the defect matrix `K` and the
overlap `J` masked to the high (resp. low) energy pairs `hiE (D ε γ L) (Msel L)`.
`h5b_of_selDirectInputs` proves `H5bTarget E Emod` from `cumulative_transfer_bound`, taking the
four bounding functions to be the four `hs2` values themselves (all bounds `le_rfl`).

What this file does NOT prove: no field (row) is proved for the Steklov operator of the
tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
`directVanish` bounds the defect matrix `K` and the overlap `J`, not `E − Emod` directly. The F2
caveat on the `cutoff` row (unconstrained cutoff data `D`) applies here unchanged. That G80 is no
stronger than G77 is G81; the F2 audit for G80 is G82.
-/

namespace SteklovAudit.H5SelDirect

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- The named inputs of (7.29) with the selector row stated on the masked `hs2` quantities. -/
structure H5bSelDirectInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
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
  /-- Row: the masked defect/overlap products are `o(L)` along a selected split energy. -/
  directVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ (Msel : ℝ → ℝ) (L₀ : ℝ),
    ∀ L, L₀ ≤ L →
      Λ0 ε γ * Real.sqrt (hs2 (mask (hiE (D ε γ L) (Msel L)) (D ε γ L).K)
          * hs2 (mask (hiE (D ε γ L) (Msel L)) (D ε γ L).J))
        + lam ε γ (Msel L) L * Real.sqrt
          (hs2 (mask (fun i j => ¬ hiE (D ε γ L) (Msel L) i j) (D ε γ L).K)
            * hs2 (mask (fun i j => ¬ hiE (D ε γ L) (Msel L) i j) (D ε γ L).J)) ≤ η * L

/-- **G80.** The direct selector-row inputs give the H5b comparison (7.29). -/
theorem h5b_of_selDirectInputs {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bSelDirectInputs E Emod) :
    H5bTarget E Emod := by
  unfold H5bTarget
  intro ε γ hε hγ η hη
  have key : ∀ M L : ℝ, |E ε γ L - Emod ε γ L| ≤
      H.Λ0 ε γ * Real.sqrt (hs2 (mask (hiE (H.D ε γ L) M) (H.D ε γ L).K)
          * hs2 (mask (hiE (H.D ε γ L) M) (H.D ε γ L).J))
        + (H.lam ε γ M L * Real.sqrt
            (hs2 (mask (fun i j => ¬ hiE (H.D ε γ L) M i j) (H.D ε γ L).K)
              * hs2 (mask (fun i j => ¬ hiE (H.D ε γ L) M i j) (H.D ε γ L).J))
          + H.disc ε γ L) := by
    intro M L
    have hb := cumulative_transfer_bound (H.D ε γ L) (H.F ε γ L) (hiE (H.D ε γ L) M)
      (H.Λ0 ε γ) (H.lam ε γ M L)
      (hs2 (mask (hiE (H.D ε γ L) M) (H.D ε γ L).K))
      (hs2 (mask (hiE (H.D ε γ L) M) (H.D ε γ L).J))
      (hs2 (mask (fun i j => ¬ hiE (H.D ε γ L) M i j) (H.D ε γ L).K))
      (hs2 (mask (fun i j => ¬ hiE (H.D ε γ L) M i j) (H.D ε γ L).J))
      (H.hΛ0 ε γ) (H.hlam ε γ M L) (H.lipHi ε γ M L) (H.lipLo ε γ M L)
      le_rfl le_rfl le_rfl le_rfl
    have hc := H.cutoff ε γ L
    have h4 := abs_sub_abs_le_abs_sub (E ε γ L - Emod ε γ L) (∑ i, ∑ j,
      (H.F ε γ L ((H.D ε γ L).a i) - H.F ε γ L ((H.D ε γ L).b j)) * (H.D ε γ L).J i j ^ 2)
    linarith
  obtain ⟨Msel, L1, hM⟩ := H.directVanish ε γ hε hγ (η / 2) (by linarith)
  obtain ⟨L2, h2⟩ := H.discVanish ε γ hε hγ (η / 2) (by linarith)
  refine ⟨max (max 1 L1) L2, fun L hL => ?_⟩
  have hLt : L1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL2 : L2 ≤ L := le_trans (le_max_right _ _) hL
  have k := key (Msel L) L
  have a1 := hM L hLt
  have a2 := h2 L hL2
  have a3 : η / 2 * L + η / 2 * L = η * L := by ring
  linarith

end SteklovAudit.H5SelDirect
