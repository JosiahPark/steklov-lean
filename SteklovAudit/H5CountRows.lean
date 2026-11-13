import Mathlib
import SteklovAudit.H5SideRows
import SteklovAudit.H5Completeness

/-!
# G23: the H5b side rows reduced to one-spectrum counts plus completeness of `J`

Roadmap item G23. `H5bCountInputs E Emod` is `H5bSideInputs E Emod` (G19) with each side row
replaced by two rows:

* true side: a count row `e1`, `trueCount` (`|E - ∑ i, φ (a i - L)| ≤ e1`, no `J`), `e1Vanish`,
  and a row-completeness row `k1`, `rowDefect` (`∑ i, |φ (a i - L)| * (1 - ∑ j, J i j ^ 2) ≤ k1`),
  `k1Vanish`;
* model side: a count row `e2`, `modelCount` (no `J`), `e2Vanish`, a column-completeness row `k2`,
  `colDefect`, `k2Vanish`, and a column Bessel row `colBessel`.

`H5bCountInputs.toSides` (a `def`, via G22's `side_of_count_and_defect` and G18's
`discVanish_of_sides`) rebuilds `H5bSideInputs` with `d1 = e1 + k1`, `d2 = e2 + k2`, and
`h5b_of_counts` gives `H5bTarget E Emod` through `h5b_of_sides`. F table: each side row becomes
"smoothed count of one spectrum (no `J`)" + "completeness of `J` weighted by the window profile".

What this file does NOT prove: no count row, completeness row or Bessel row is proved for the
Steklov operator of the tetrahedron (or for any concrete operator); no field of `H5bCountInputs` is
proved for the actual operator; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…]
input and Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5CountRows

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5SideRows

/-- **G23.** The side-form H5b inputs with each side row split into a one-spectrum count row and a
completeness row on `J`. -/
structure H5bCountInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  /-- Row: window profile (G7); the test is `F ε γ L x = P.φ (x - L)`. -/
  P : ProfileLipRows
  e1 : ℝ → ℝ → ℝ → ℝ
  /-- Row: smoothed count of the true spectrum (no `J`). -/
  trueCount : ∀ ε γ L : ℝ, |E ε γ L - ∑ i, P.φ ((D ε γ L).a i - L)| ≤ e1 ε γ L
  e1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    e1 ε γ L ≤ η * L
  k1 : ℝ → ℝ → ℝ → ℝ
  /-- Row: completeness of the rows of `J`, weighted by the window profile. -/
  rowDefect : ∀ ε γ L : ℝ, ∑ i, |P.φ ((D ε γ L).a i - L)| *
    (1 - ∑ j, (D ε γ L).J i j ^ 2) ≤ k1 ε γ L
  k1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    k1 ε γ L ≤ η * L
  e2 : ℝ → ℝ → ℝ → ℝ
  /-- Row: smoothed count of the model spectrum (no `J`). -/
  modelCount : ∀ ε γ L : ℝ, |Emod ε γ L - ∑ j, P.φ ((D ε γ L).b j - L)| ≤ e2 ε γ L
  e2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    e2 ε γ L ≤ η * L
  k2 : ℝ → ℝ → ℝ → ℝ
  /-- Row: completeness of the columns of `J`, weighted by the window profile. -/
  colDefect : ∀ ε γ L : ℝ, ∑ j, |P.φ ((D ε γ L).b j - L)| *
    (1 - ∑ i, (D ε γ L).J i j ^ 2) ≤ k2 ε γ L
  k2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    k2 ε γ L ≤ η * L
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

/-- **G23.** Count rows + completeness rows rebuild the side-form inputs of G19, with
`d1 = e1 + k1` and `d2 = e2 + k2`. -/
noncomputable def H5bCountInputs.toSides {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bCountInputs E Emod) : H5bSideInputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  d1 := fun ε γ L => W.e1 ε γ L + W.k1 ε γ L
  trueSide := fun ε γ L =>
    SteklovAudit.H5Completeness.side_of_count_and_defect
      (fun i => W.P.φ ((W.D ε γ L).a i - L)) (fun i => ∑ j, (W.D ε γ L).J i j ^ 2)
      (E ε γ L) (W.e1 ε γ L) (W.k1 ε γ L)
      (W.trueCount ε γ L) (W.rowDefect ε γ L) (W.bessel ε γ L)
  d1Vanish := SteklovAudit.H5CutoffSides.discVanish_of_sides W.e1 W.k1 W.e1Vanish W.k1Vanish
  d2 := fun ε γ L => W.e2 ε γ L + W.k2 ε γ L
  modelSide := fun ε γ L =>
    SteklovAudit.H5Completeness.side_of_count_and_defect
      (fun j => W.P.φ ((W.D ε γ L).b j - L)) (fun j => ∑ i, (W.D ε γ L).J i j ^ 2)
      (Emod ε γ L) (W.e2 ε γ L) (W.k2 ε γ L)
      (W.modelCount ε γ L) (W.colDefect ε γ L) (W.colBessel ε γ L)
  d2Vanish := SteklovAudit.H5CutoffSides.discVanish_of_sides W.e2 W.k2 W.e2Vanish W.k2Vanish
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

/-- The rebuilt true-side discrepancy is count error plus row-completeness defect. -/
theorem toSides_d1 {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bCountInputs E Emod) :
    W.toSides.d1 = fun ε γ L => W.e1 ε γ L + W.k1 ε γ L := rfl

/-- The rebuilt model-side discrepancy is count error plus column-completeness defect. -/
theorem toSides_d2 {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bCountInputs E Emod) :
    W.toSides.d2 = fun ε γ L => W.e2 ε γ L + W.k2 ε γ L := rfl

/-- **G23.** The count-form named inputs give the H5b comparison (7.29). -/
theorem h5b_of_counts {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bCountInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_sides W.toSides

end SteklovAudit.H5CountRows
