import Mathlib
import SteklovAudit.H5CountRows

/-!
# G26: profile-free missing-mass rows for the H5b count inputs

Roadmap item G26. `H5bMassInputs E Emod` is `H5bCountInputs E Emod` (G23) with the two
profile-weighted completeness rows replaced by

* a profile bound `Φ`, `hΦ : 0 ≤ Φ`, `profBound : ∀ x, |P.φ x| ≤ Φ`;
* a row missing-mass row `m1`, `rowMiss` (`∑ i, (1 - ∑ j, J i j ^ 2) ≤ m1`), `m1Vanish`;
* a column missing-mass row `m2`, `colMiss` (`∑ j, (1 - ∑ i, J i j ^ 2) ≤ m2`), `m2Vanish`.

`vanish_const_mul` shows `Φ * m` is `o(L)` when `m` is. `H5bMassInputs.toCounts` (a `def`, via G22's
`defect_le_sup`) rebuilds `H5bCountInputs` with `k1 = Φ * m1`, `k2 = Φ * m2`, and `h5b_of_mass`
gives `H5bTarget E Emod` through `h5b_of_counts`. These rows are a sufficient form of the
completeness rows; G27 records that they are stronger, not weaker.

What this file does NOT prove: no count, missing-mass or Bessel row is proved for the Steklov
operator of the tetrahedron (or for any concrete operator); no field of `H5bMassInputs` is proved for
the actual operator; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and
Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5MissingMass

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5SideRows SteklovAudit.H5CountRows

/-- A nonnegative constant multiple of an `o(L)` rate is `o(L)`. -/
theorem vanish_const_mul (m : ℝ → ℝ → ℝ → ℝ) (Φ : ℝ) (hΦ : 0 ≤ Φ)
    (hm : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      m ε γ L ≤ η * L) :
    ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      Φ * m ε γ L ≤ η * L := by
  intro ε γ hε hγ η hη
  rcases hΦ.eq_or_lt with h0 | hpos
  · refine ⟨0, fun L hL => ?_⟩
    rw [← h0, zero_mul]
    exact mul_nonneg hη.le hL
  · obtain ⟨L₀, hL₀⟩ := hm ε γ hε hγ (η / Φ) (div_pos hη hpos)
    refine ⟨L₀, fun L hL => ?_⟩
    have hne : Φ ≠ 0 := hpos.ne'
    have h1 : Φ * m ε γ L ≤ Φ * (η / Φ * L) := mul_le_mul_of_nonneg_left (hL₀ L hL) hΦ
    have h2 : Φ * (η / Φ * L) = η * L := by
      first
        | (field_simp; done)
        | (field_simp; ring)
        | (rw [← mul_assoc, mul_div_cancel₀ η hne])
    rw [h2] at h1
    exact h1

/-- **G26.** The count-form H5b inputs with profile-free missing-mass rows in place of the
profile-weighted completeness rows. -/
structure H5bMassInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  /-- Row: window profile (G7); the test is `F ε γ L x = P.φ (x - L)`. -/
  P : ProfileLipRows
  /-- Row: sup bound on the window profile. -/
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  e1 : ℝ → ℝ → ℝ → ℝ
  /-- Row: smoothed count of the true spectrum (no `J`). -/
  trueCount : ∀ ε γ L : ℝ, |E ε γ L - ∑ i, P.φ ((D ε γ L).a i - L)| ≤ e1 ε γ L
  e1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    e1 ε γ L ≤ η * L
  m1 : ℝ → ℝ → ℝ → ℝ
  /-- Row: total missing mass of the rows of `J` (no profile). -/
  rowMiss : ∀ ε γ L : ℝ, ∑ i, (1 - ∑ j, (D ε γ L).J i j ^ 2) ≤ m1 ε γ L
  m1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m1 ε γ L ≤ η * L
  e2 : ℝ → ℝ → ℝ → ℝ
  /-- Row: smoothed count of the model spectrum (no `J`). -/
  modelCount : ∀ ε γ L : ℝ, |Emod ε γ L - ∑ j, P.φ ((D ε γ L).b j - L)| ≤ e2 ε γ L
  e2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    e2 ε γ L ≤ η * L
  m2 : ℝ → ℝ → ℝ → ℝ
  /-- Row: total missing mass of the columns of `J` (no profile). -/
  colMiss : ∀ ε γ L : ℝ, ∑ j, (1 - ∑ i, (D ε γ L).J i j ^ 2) ≤ m2 ε γ L
  m2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m2 ε γ L ≤ η * L
  /-- Row: Bessel bound on the columns of `J`. -/
  colBessel : ∀ ε γ L j, ∑ i, (D ε γ L).J i j ^ 2 ≤ 1
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  /-- Row (G12): Bessel bound on the rows of `J`. -/
  bessel : ∀ ε γ L i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1
  /-- Row (G12): Weyl count of the eigenvalues below the cutoff. -/
  count : ∀ ε γ L : ℝ, (Fintype.card (Fin (nA ε γ L)) : ℝ) ≤ Cm ε γ * (1 + L) ^ 2
  /-- Row: Lemma 7.1′, the `defect` field of `PDEInputs` verbatim. -/
  defect : ∀ ε γ L : ℝ, hs2 (D ε γ L).K ≤ Ck ε γ ^ 2 * (1 + L) ^ 2
  τ : ℝ → ℝ → ℝ → ℝ
  /-- Row: high-energy defect tail. -/
  tail : ∀ ε γ M L : ℝ, hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M
  /-- Row (G9): decay rate of the tail. -/
  Cτ : ℝ → ℝ → ℝ
  tailRate : SteklovAudit.H5TailRate.TailRate τ Cτ
  /-- Row: nonnegative energies. -/
  ha : ∀ ε γ L i, 0 ≤ (D ε γ L).a i
  hb : ∀ ε γ L j, 0 ≤ (D ε γ L).b j
  /-- Row (G15): L-uniform count of eigenvalues `≤ M`. -/
  c : ℝ → ℝ → ℝ → ℝ
  lowCount : ∀ ε γ M L : ℝ,
    ((Finset.univ.filter fun i => (D ε γ L).a i ≤ M).card : ℝ) ≤ c ε γ M

/-- **G26.** Missing-mass rows rebuild the count-form inputs of G23, with `k1 = Φ * m1` and
`k2 = Φ * m2`. -/
noncomputable def H5bMassInputs.toCounts {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bMassInputs E Emod) : H5bCountInputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  e1 := W.e1
  trueCount := W.trueCount
  e1Vanish := W.e1Vanish
  k1 := fun ε γ L => W.Φ * W.m1 ε γ L
  rowDefect := fun ε γ L =>
    (SteklovAudit.H5Completeness.defect_le_sup
      (fun i => W.P.φ ((W.D ε γ L).a i - L)) (fun i => ∑ j, (W.D ε γ L).J i j ^ 2) W.Φ
      (fun i => W.profBound ((W.D ε γ L).a i - L)) (W.bessel ε γ L)).trans
      (mul_le_mul_of_nonneg_left (W.rowMiss ε γ L) W.hΦ)
  k1Vanish := vanish_const_mul W.m1 W.Φ W.hΦ W.m1Vanish
  e2 := W.e2
  modelCount := W.modelCount
  e2Vanish := W.e2Vanish
  k2 := fun ε γ L => W.Φ * W.m2 ε γ L
  colDefect := fun ε γ L =>
    (SteklovAudit.H5Completeness.defect_le_sup
      (fun j => W.P.φ ((W.D ε γ L).b j - L)) (fun j => ∑ i, (W.D ε γ L).J i j ^ 2) W.Φ
      (fun j => W.profBound ((W.D ε γ L).b j - L)) (W.colBessel ε γ L)).trans
      (mul_le_mul_of_nonneg_left (W.colMiss ε γ L) W.hΦ)
  k2Vanish := vanish_const_mul W.m2 W.Φ W.hΦ W.m2Vanish
  colBessel := W.colBessel
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
  bessel := W.bessel
  count := W.count
  defect := W.defect
  τ := W.τ
  tail := W.tail
  Cτ := W.Cτ
  tailRate := W.tailRate
  ha := W.ha
  hb := W.hb
  c := W.c
  lowCount := W.lowCount

/-- The rebuilt row-completeness bound is the profile bound times the row missing mass. -/
theorem toCounts_k1 {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bMassInputs E Emod) :
    W.toCounts.k1 = fun ε γ L => W.Φ * W.m1 ε γ L := rfl

/-- The rebuilt column-completeness bound is the profile bound times the column missing mass. -/
theorem toCounts_k2 {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bMassInputs E Emod) :
    W.toCounts.k2 = fun ε γ L => W.Φ * W.m2 ε γ L := rfl

/-- **G26.** The missing-mass named inputs give the H5b comparison (7.29). -/
theorem h5b_of_mass {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bMassInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_counts W.toCounts

end SteklovAudit.H5MissingMass
