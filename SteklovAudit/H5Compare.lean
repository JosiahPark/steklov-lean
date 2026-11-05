import Mathlib
import SteklovAudit.EdgeFromModel
import SteklovAudit.AbstractTransferB

/-!
# F1: the H5b comparison (7.29) from one named input per table row

Roadmap item F1. `H5bTarget E Emod` is exactly the type of `Thm111InputsC4.compare`
(`compare_is_target`). `H5bInputs E Emod` has one named hypothesis field per row of the
section F table in ROADMAP.md:

* row "finite cutoff → continuous model spectrum": `cutoff`, `discVanish`
  (the true-minus-model edge count equals the finite-cutoff trace comparison up to `disc = o(L)`);
* row "localized spectral mass (2.2)" and row "uniform localized HS defect (Lemma 7.1′)":
  `pde` (the `PDEInputs` structure of `AbstractTransfer.lean`; the chain uses its `mass` part);
* row "high-energy defect tail": `tail`, `tailVanish` (split energy `M`, `τ(M) → 0`);
* row "low-energy defect bound κ": `lowDefect` (independent of `L` for fixed `M`);
* row "Lipschitz-type bounds Λ, λ": `lipHi`, `lipLo`, `lamVanish` (`λ(M, L) → 0` as `L → ∞`).

`h5b_of_inputs` proves the target by chaining `cumulative_transfer_bound` (B4) and
`little_o_of_vanishing_tail` (B5). Propagation (9.1) does not enter this chain.

What this file does NOT prove: none of the fields is proved for the Steklov operator of the
tetrahedron; no DtN operator or wave group is constructed; (7.29) and Theorem 1.3 / 11.1 remain
conditional. Caveat for F2: `cutoff` has content only when `D` is the actual spectral data.
With `D` empty the trace is `0`, and `cutoff` plus `discVanish` then say the target itself;
Lean cannot enforce that `D` is the true data, so this row must be reviewed on paper.
-/

namespace SteklovAudit.H5Compare

open SteklovAudit SteklovAudit.AbstractTransfer

/-- Exactly the type of `Thm111InputsC4.compare` for the counts `E` and `Emod`. -/
def H5bTarget (E Emod : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |E ε γ L - Emod ε γ L| ≤ η * L

theorem compare_is_target {N : ℝ → ℝ} {a c : ℝ} (H : EdgeFromModel.Thm111InputsC4 N a c) :
    H5bTarget (fun ε γ L => (H.part ε γ).E L) H.Emod := H.compare

/-- High-energy pairs at split energy `M`: `max(a i, b j) > M`. -/
def hiE {ι κ : Type*} (D : Data ι κ) (M : ℝ) (i : ι) (j : κ) : Prop := M < max (D.a i) (D.b j)

noncomputable instance hiE.decidable {ι κ : Type*} (D : Data ι κ) (M : ℝ) (i : ι) (j : κ) :
    Decidable (hiE D M i j) := Classical.dec _

theorem hs2_mask_le {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → κ → Prop)
    [∀ i j, Decidable (p i j)] (M : ι → κ → ℝ) : hs2 (mask p M) ≤ hs2 M := by
  dsimp only [hs2, mask]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_refl _
  · nlinarith [sq_nonneg (M i j)]

/-- The named inputs of (7.29), one group per row of the section F table. -/
structure H5bInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  F : ℝ → ℝ → ℝ → ℝ → ℝ
  disc : ℝ → ℝ → ℝ → ℝ
  /-- Row: finite cutoff → continuous model spectrum. -/
  cutoff : ∀ ε γ L : ℝ, |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j,
    (F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)) * (D ε γ L).J i j ^ 2| ≤ disc ε γ L
  discVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    disc ε γ L ≤ η * L
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  /-- Rows: localized spectral mass (2.2) and uniform localized HS defect (Lemma 7.1′). -/
  pde : ∀ ε γ L : ℝ, PDEInputs (D ε γ L) L (Cm ε γ) (Ck ε γ)
  τ : ℝ → ℝ → ℝ → ℝ
  /-- Row: high-energy defect tail. -/
  tail : ∀ ε γ M L : ℝ, hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M
  tailVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ → ∃ M, τ ε γ M ≤ δ
  κ2 : ℝ → ℝ → ℝ → ℝ
  /-- Row: low-energy defect bound. -/
  lowDefect : ∀ ε γ M L : ℝ,
    hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).K) ≤ κ2 ε γ M
  Λ0 : ℝ → ℝ → ℝ
  hΛ0 : ∀ ε γ, 0 ≤ Λ0 ε γ
  lam : ℝ → ℝ → ℝ → ℝ → ℝ
  hlam : ∀ ε γ M L, 0 ≤ lam ε γ M L
  /-- Row: Lipschitz-type bounds for the smoothed counting test. -/
  lipHi : ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), hiE (D ε γ L) M i j →
    |F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)|
      ≤ Λ0 ε γ * |(D ε γ L).a i - (D ε γ L).b j|
  lipLo : ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), ¬ hiE (D ε γ L) M i j →
    |F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)|
      ≤ lam ε γ M L * |(D ε γ L).a i - (D ε γ L).b j|
  lamVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    lam ε γ M L ≤ η

/-- **F1.** The named inputs give the H5b comparison (7.29). -/
theorem h5b_of_inputs {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) : H5bTarget E Emod := by
  unfold H5bTarget
  intro ε γ hε hγ η hη
  have key : ∀ M L : ℝ, 1 ≤ L → |E ε γ L - Emod ε γ L| ≤
      H.Λ0 ε γ * Real.sqrt (H.Cm ε γ) * Real.sqrt (H.τ ε γ M) * (1 + L)
        + (H.lam ε γ M L * (Real.sqrt (H.κ2 ε γ M * H.Cm ε γ) * (1 + L)) + H.disc ε γ L) := by
    intro M L hL
    have hL0 : 0 ≤ 1 + L := by linarith
    have hm : hs2 (H.D ε γ L).J ≤ H.Cm ε γ * (1 + L) ^ 2 := (H.pde ε γ L).mass
    have hb := cumulative_transfer_bound (H.D ε γ L) (H.F ε γ L) (hiE (H.D ε γ L) M)
      (H.Λ0 ε γ) (H.lam ε γ M L) (H.τ ε γ M) (H.Cm ε γ * (1 + L) ^ 2) (H.κ2 ε γ M)
      (H.Cm ε γ * (1 + L) ^ 2) (H.hΛ0 ε γ) (H.hlam ε γ M L) (H.lipHi ε γ M L)
      (H.lipLo ε γ M L) (H.tail ε γ M L) (le_trans (hs2_mask_le _ _) hm)
      (H.lowDefect ε γ M L) (le_trans (hs2_mask_le _ _) hm)
    have e1 : Real.sqrt (H.τ ε γ M * (H.Cm ε γ * (1 + L) ^ 2))
        = Real.sqrt (H.τ ε γ M) * Real.sqrt (H.Cm ε γ) * (1 + L) := by
      rw [show H.τ ε γ M * (H.Cm ε γ * (1 + L) ^ 2) = (H.τ ε γ M * H.Cm ε γ) * (1 + L) ^ 2 by
        ring, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_mul' _ (H.hCm ε γ), Real.sqrt_sq hL0]
    have e2 : Real.sqrt (H.κ2 ε γ M * (H.Cm ε γ * (1 + L) ^ 2))
        = Real.sqrt (H.κ2 ε γ M * H.Cm ε γ) * (1 + L) := by
      rw [show H.κ2 ε γ M * (H.Cm ε γ * (1 + L) ^ 2) = (H.κ2 ε γ M * H.Cm ε γ) * (1 + L) ^ 2 by
        ring, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hL0]
    rw [e1, e2] at hb
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
      H.lam ε γ M L * (Real.sqrt (H.κ2 ε γ M * H.Cm ε γ) * (1 + L)) + H.disc ε γ L ≤ δ * L := by
    intro M δ hδ
    have hs0 : 0 ≤ Real.sqrt (H.κ2 ε γ M * H.Cm ε γ) := Real.sqrt_nonneg _
    generalize Real.sqrt (H.κ2 ε γ M * H.Cm ε γ) = s at hs0 ⊢
    obtain ⟨L1, h1⟩ := H.lamVanish ε γ hε hγ M (δ / (4 * (s + 1))) (div_pos hδ (by linarith))
    obtain ⟨L2, h2⟩ := H.discVanish ε γ hε hγ (δ / 2) (half_pos hδ)
    refine ⟨max (max L1 L2) 1, fun L hL => ?_⟩
    have hL1 : L1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
    have hL2 : L2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
    have hLone : 1 ≤ L := le_trans (le_max_right _ _) hL
    have a1 := h1 L hL1
    rw [le_div_iff₀ (by linarith)] at a1
    have a2 := h2 L hL2
    have hlam0 := H.hlam ε γ M L
    have k2 : H.lam ε γ M L * (s * (1 + L)) ≤ H.lam ε γ M L * ((s + 1) * (2 * L)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hs0 (sub_nonneg.2 hLone)]) hlam0
    have k3 : H.lam ε γ M L * ((s + 1) * (2 * L))
        = (H.lam ε γ M L * (4 * (s + 1))) * (L / 2) := by ring
    have k4 : (H.lam ε γ M L * (4 * (s + 1))) * (L / 2) ≤ δ * (L / 2) :=
      mul_le_mul_of_nonneg_right a1 (by linarith)
    linarith
  exact little_o_of_vanishing_tail (fun L => E ε γ L - Emod ε γ L)
    (H.Λ0 ε γ * Real.sqrt (H.Cm ε γ)) (mul_nonneg (H.hΛ0 ε γ) (Real.sqrt_nonneg _))
    (fun M => Real.sqrt (H.τ ε γ M))
    (fun M L => H.lam ε γ M L * (Real.sqrt (H.κ2 ε γ M * H.Cm ε γ) * (1 + L)) + H.disc ε γ L)
    (fun M => Real.sqrt_nonneg _) key htail hlow η hη

/-! ### F2: satisfiability, the disguise audit, and the F ledger

Audit result (proved below, `inputs_iff_target`): `Nonempty (H5bInputs E Emod) ↔ H5bTarget E Emod`.
So in Lean the inputs are satisfiable but are *not* strictly weaker than the target: since the
cutoff data `D` is unconstrained, the empty cutoff turns `cutoff` + `discVanish` into the target
itself. The fields `cutoff`/`discVanish` state a bound on `E − Emod` at scale `L` (through `disc`);
no other field mentions `E` or `Emod`. The ledger `Thm111InputsF` is therefore equivalent to
`Thm111InputsC4` (`toC4`, `ofC4`); its content over C4 is only in the paper review of the
`cutoff` row with `D` the actual spectral data. Nothing here proves H5b for the Steklov operator. -/

/-- The cutoff with no eigenvalues. -/
def emptyData : Data (Fin 0) (Fin 0) := ⟨fun i => i.elim0, fun j => j.elim0, fun i _ => i.elim0⟩

/-- From the target alone: empty cutoff, `disc = |E − Emod|`, all other inputs zero. -/
noncomputable def inputsOfTarget {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    H5bInputs E Emod where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => emptyData
  F := fun _ _ _ _ => 0
  disc := fun ε γ L => |E ε γ L - Emod ε γ L|
  cutoff := by intro ε γ L; simp
  discVanish := fun ε γ hε hγ η hη => h ε γ hε hγ η hη
  Cm := fun _ _ => 0
  Ck := fun _ _ => 0
  hCm := fun _ _ => le_refl 0
  pde := fun _ _ _ => ⟨by simp [hs2], by simp [hs2]⟩
  τ := fun _ _ _ => 0
  tail := by intro ε γ M L; simp [hs2]
  tailVanish := fun _ _ _ _ _ hδ => ⟨0, hδ.le⟩
  κ2 := fun _ _ _ => 0
  lowDefect := by intro ε γ M L; simp [hs2]
  Λ0 := fun _ _ => 0
  hΛ0 := fun _ _ => le_refl 0
  lam := fun _ _ _ _ => 0
  hlam := fun _ _ _ _ => le_refl 0
  lipHi := fun _ _ _ _ i => Fin.elim0 i
  lipLo := fun _ _ _ _ i => Fin.elim0 i
  lamVanish := fun _ _ _ _ _ _ hη => ⟨0, fun _ _ => hη.le⟩

/-- **F2 audit.** The inputs hold exactly when the target holds. -/
theorem inputs_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bInputs E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨H⟩ => h5b_of_inputs H, fun h => ⟨inputsOfTarget h⟩⟩

/-- **F2 satisfiability.** An explicit witness: `E = Emod`. -/
theorem inputs_nonempty (E : ℝ → ℝ → ℝ → ℝ) : Nonempty (H5bInputs E E) := by
  refine ⟨inputsOfTarget ?_⟩
  unfold H5bTarget
  intro ε γ _ _ η hη
  refine ⟨0, fun L hL => ?_⟩
  rw [sub_self, abs_zero]
  exact mul_nonneg hη.le hL

/-- The C4 ledger with `compare` replaced by `H5bInputs`. -/
structure Thm111InputsF (N : ℝ → ℝ) (a c : ℝ) where
  vert : ℝ → MainConditional.VertexPart
  part : ℝ → ℝ → MainConditional.EdgeFacePart
  CL : ℝ
  CV : ℝ
  DE : ℝ → ℝ
  hCL : 0 ≤ CL
  hCV : 0 ≤ CV
  hDE : ∀ ε, 0 ≤ DE ε
  splitting : ∀ ε γ L, N L = (vert ε).V L + (part ε γ).E L + (part ε γ).F L
  area : ∀ ε γ, (vert ε).AV + (part ε γ).AE + (part ε γ).AF = MainConditional.areaCoeff a
  length : ∀ ε, 0 < ε → |(vert ε).len - 6 * a| ≤ CL * ε
  vertex : ∀ ε, 0 < ε → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |(vert ε).V L - (vert ε).AV * L ^ 2| ≤ (CV * ε + η) * L
  face : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |(part ε γ).F L - (part ε γ).AF * L ^ 2| ≤ η * L
  Emod : ℝ → ℝ → ℝ → ℝ
  model : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |Emod ε γ L - (part ε γ).AE * L ^ 2 - c * (vert ε).len * L| ≤ (DE ε * γ + η) * L
  /-- H5b, as the named inputs of F1. -/
  h5b : H5bInputs (fun ε γ L => (part ε γ).E L) Emod

/-- The F ledger gives the C4 ledger. -/
noncomputable def toC4 {N : ℝ → ℝ} {a c : ℝ} (H : Thm111InputsF N a c) :
    EdgeFromModel.Thm111InputsC4 N a c where
  vert := H.vert
  part := H.part
  CL := H.CL
  CV := H.CV
  DE := H.DE
  hCL := H.hCL
  hCV := H.hCV
  hDE := H.hDE
  splitting := H.splitting
  area := H.area
  length := H.length
  vertex := H.vertex
  face := H.face
  Emod := H.Emod
  model := H.model
  compare := h5b_of_inputs H.h5b

/-- Converse (from `inputs_iff_target`): the F ledger is no stronger than the C4 ledger. -/
noncomputable def ofC4 {N : ℝ → ℝ} {a c : ℝ} (H : EdgeFromModel.Thm111InputsC4 N a c) :
    Thm111InputsF N a c where
  vert := H.vert
  part := H.part
  CL := H.CL
  CV := H.CV
  DE := H.DE
  hCL := H.hCL
  hCV := H.hCV
  hDE := H.hDE
  splitting := H.splitting
  area := H.area
  length := H.length
  vertex := H.vertex
  face := H.face
  Emod := H.Emod
  model := H.model
  h5b := inputsOfTarget (compare_is_target H)

/-- **Theorem 11.1 (conditional), F ledger.** Not a proof of Theorem 1.3 / 11.1. -/
theorem theorem_11_1_of_F (N : ℝ → ℝ) (a c : ℝ) (H : Thm111InputsF N a c) :
    HasSharpRealLaw N (MainConditional.areaCoeff a) (6 * a * c) :=
  EdgeFromModel.theorem_11_1_of_C4 N a c (toC4 H)

end SteklovAudit.H5Compare
