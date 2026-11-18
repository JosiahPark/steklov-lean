import Mathlib
import SteklovAudit.H5SelDirect

/-!
# G83: the PDE rows are not used by the direct selector form

Roadmap item G83. `H5bSelMinInputs E Emod` has the fields of `H5bSelDirectInputs` (G80,
`H5SelDirect.lean`) without the PDE rows `Cm`, `Ck`, `hCm`, `pde` (the mass bound (2.2) and the
defect bound of Lemma 7.1′ packaged in `PDEInputs`). `h5b_of_selMinInputs` proves `H5bTarget E Emod`
by the proof of `h5b_of_selDirectInputs`, which never uses those fields. `forgetPde` maps the G80
inputs to the G83 inputs, and `forgetPde_target` recovers the G80 conclusion through it.

F table text: in the direct form the rows (2.2) and Lemma 7.1′ (`PDEInputs.mass`, `.defect`) are not
separate inputs; they matter only as a means of proving `directVanish`.

What this file does NOT prove: no field (row) is proved for the Steklov operator of the
tetrahedron; no DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
Dropping the PDE rows does not make `directVanish` easier to verify; it only shows they are not
used by the assembly. The F2 caveat on the `cutoff` row (unconstrained cutoff data `D`) applies
here unchanged.
-/

namespace SteklovAudit.H5SelMin

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelDirect

/-- The direct-form inputs of (7.29) (`H5bSelDirectInputs`) without the PDE rows
`Cm`, `Ck`, `hCm`, `pde`. -/
structure H5bSelMinInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  F : ℝ → ℝ → ℝ → ℝ → ℝ
  disc : ℝ → ℝ → ℝ → ℝ
  cutoff : ∀ ε γ L : ℝ, |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j,
    (F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)) * (D ε γ L).J i j ^ 2| ≤ disc ε γ L
  discVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    disc ε γ L ≤ η * L
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

/-- **G83.** The direct inputs without PDE rows give the H5b comparison (7.29). -/
theorem h5b_of_selMinInputs {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bSelMinInputs E Emod) :
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

/-- Forget the PDE rows of the G80 inputs. -/
noncomputable def forgetPde {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bSelDirectInputs E Emod) :
    H5bSelMinInputs E Emod where
  nA := H.nA
  nB := H.nB
  D := H.D
  F := H.F
  disc := H.disc
  cutoff := H.cutoff
  discVanish := H.discVanish
  Λ0 := H.Λ0
  hΛ0 := H.hΛ0
  lam := H.lam
  hlam := H.hlam
  lipHi := H.lipHi
  lipLo := H.lipLo
  directVanish := H.directVanish

theorem forgetPde_Λ0 {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bSelDirectInputs E Emod) :
    (forgetPde H).Λ0 = H.Λ0 := rfl

/-- **G83.** The G80 conclusion, routed through the inputs without PDE rows. -/
theorem forgetPde_target {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bSelDirectInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_selMinInputs (forgetPde H)

end SteklovAudit.H5SelMin
