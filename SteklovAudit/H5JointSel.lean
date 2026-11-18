import Mathlib
import SteklovAudit.H5Joint

/-!
# G77: the H5b comparison with an `L`-dependent split energy

Roadmap item G77. `H5bJointSelInputs E Emod` has the fields of `H5bJointInputs` (from
`H5Joint.lean`), except that `jointVanish` is replaced by `selVanish`: for every `η > 0` there are
a split-energy selector `Msel : ℝ → ℝ` and a scale `L₀` with
`Λ0 ε γ * √(τ ε γ (Msel L) L * mHi ε γ (Msel L) L)
  + lam ε γ (Msel L) L * √(κ2 ε γ (Msel L) L * mLo ε γ (Msel L) L) ≤ η * L`
for all `L ≥ L₀`. So the split energy in (7.29) may be chosen as a function of `L`.
`h5b_of_jointSelInputs` proves `H5bTarget E Emod` from `cumulative_transfer_bound`, as
`h5b_of_jointInputs` does: the pointwise bound holds for every `M` and `L`, so it is applied at
`M = Msel L`.

What this file does NOT prove: no field (row) is proved for the Steklov operator of the
tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
The F2 caveat on the `cutoff` row (unconstrained cutoff data `D`) applies here unchanged. That
G77 is no stronger than G72, and strictly weaker as row shapes, is G78.
-/

namespace SteklovAudit.H5JointSel

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- The named inputs of (7.29) with the joint row taken at an `L`-dependent split energy. -/
structure H5bJointSelInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
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
  τ : ℝ → ℝ → ℝ → ℝ → ℝ
  tail : ∀ ε γ M L : ℝ, 1 ≤ L → hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M L
  mHi : ℝ → ℝ → ℝ → ℝ → ℝ
  hiMass : ∀ ε γ M L : ℝ, hs2 (mask (hiE (D ε γ L) M) (D ε γ L).J) ≤ mHi ε γ M L
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
  /-- Row: the joint term is `o(L)` along a split energy `Msel L` chosen as a function of `L`. -/
  selVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ (Msel : ℝ → ℝ) (L₀ : ℝ),
    ∀ L, L₀ ≤ L →
      Λ0 ε γ * Real.sqrt (τ ε γ (Msel L) L * mHi ε γ (Msel L) L)
        + lam ε γ (Msel L) L * Real.sqrt (κ2 ε γ (Msel L) L * mLo ε γ (Msel L) L) ≤ η * L

/-- **G77.** The selector-row inputs give the H5b comparison (7.29). -/
theorem h5b_of_jointSelInputs {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bJointSelInputs E Emod) :
    H5bTarget E Emod := by
  unfold H5bTarget
  intro ε γ hε hγ η hη
  have key : ∀ M L : ℝ, 1 ≤ L → |E ε γ L - Emod ε γ L| ≤
      H.Λ0 ε γ * Real.sqrt (H.τ ε γ M L * H.mHi ε γ M L)
        + (H.lam ε γ M L * Real.sqrt (H.κ2 ε γ M L * H.mLo ε γ M L) + H.disc ε γ L) := by
    intro M L hL
    have hb := cumulative_transfer_bound (H.D ε γ L) (H.F ε γ L) (hiE (H.D ε γ L) M)
      (H.Λ0 ε γ) (H.lam ε γ M L) (H.τ ε γ M L) (H.mHi ε γ M L) (H.κ2 ε γ M L)
      (H.mLo ε γ M L) (H.hΛ0 ε γ) (H.hlam ε γ M L) (H.lipHi ε γ M L)
      (H.lipLo ε γ M L) (H.tail ε γ M L hL) (H.hiMass ε γ M L)
      (H.lowDefect ε γ M L) (H.lowMass ε γ M L)
    have hc := H.cutoff ε γ L
    have h4 := abs_sub_abs_le_abs_sub (E ε γ L - Emod ε γ L) (∑ i, ∑ j,
      (H.F ε γ L ((H.D ε γ L).a i) - H.F ε γ L ((H.D ε γ L).b j)) * (H.D ε γ L).J i j ^ 2)
    linarith
  obtain ⟨Msel, L1, hM⟩ := H.selVanish ε γ hε hγ (η / 2) (by linarith)
  obtain ⟨L2, h2⟩ := H.discVanish ε γ hε hγ (η / 2) (by linarith)
  refine ⟨max (max 1 L1) L2, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLt : L1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL2 : L2 ≤ L := le_trans (le_max_right _ _) hL
  have k := key (Msel L) L hL1
  have a1 := hM L hLt
  have a2 := h2 L hL2
  have a3 : η / 2 * L + η / 2 * L = η * L := by ring
  linarith

end SteklovAudit.H5JointSel
