import Mathlib
import SteklovAudit.H5PaperRows
import SteklovAudit.H5CutoffSides

/-!
# G19: the H5b inputs with the cutoff row split into a true side and a model side

Roadmap item G19. `H5bSideInputs E Emod` is `H5bPaperInputs E Emod` (G16) with the fields `disc`,
`cutoff`, `discVanish` replaced by two rows, each mentioning only one spectrum:

* true side: `d1`, `trueSide`, `d1Vanish` — the true count `E` against the trace of the true
  eigenvalues `a`, weighted by the row masses `∑ j, J i j ^ 2`;
* model side: `d2`, `modelSide`, `d2Vanish` — the model count `Emod` against the trace of the model
  eigenvalues `b`, weighted by the column masses `∑ i, J i j ^ 2`.

`H5bSideInputs.toPaper` (a `def`, via G18's `cutoff_of_sides` and `discVanish_of_sides`) rebuilds an
`H5bPaperInputs` with `disc = d1 + d2` (`toPaper_disc`), and `h5b_of_sides` gives `H5bTarget E Emod`
through `h5b_of_paper`. F table: the cutoff row becomes the two rows "true side" and "model side".
Whether this two-row form is weaker or stronger than the cutoff row is audited in G20/G21.

What this file does NOT prove: neither side row is proved for the Steklov operator of the
tetrahedron (or for any concrete operator); no field of `H5bSideInputs` is proved for the actual
operator; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and
Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5SideRows

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows

/-- **G19.** The paper-form H5b inputs with the cutoff row split into a true side and a model
side. -/
structure H5bSideInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  /-- Row: window profile (G7); the test is `F ε γ L x = P.φ (x - L)`. -/
  P : ProfileLipRows
  d1 : ℝ → ℝ → ℝ → ℝ
  /-- Row: true side, the true count against the row-weighted trace of the true eigenvalues. -/
  trueSide : ∀ ε γ L : ℝ, |E ε γ L - ∑ i, P.φ ((D ε γ L).a i - L) *
    (∑ j, (D ε γ L).J i j ^ 2)| ≤ d1 ε γ L
  d1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    d1 ε γ L ≤ η * L
  d2 : ℝ → ℝ → ℝ → ℝ
  /-- Row: model side, the model count against the column-weighted trace of the model
  eigenvalues. -/
  modelSide : ∀ ε γ L : ℝ, |Emod ε γ L - ∑ j, P.φ ((D ε γ L).b j - L) *
    (∑ i, (D ε γ L).J i j ^ 2)| ≤ d2 ε γ L
  d2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    d2 ε γ L ≤ η * L
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

/-- **G19.** The two side rows rebuild the paper-form inputs of G16, with `disc = d1 + d2`. -/
noncomputable def H5bSideInputs.toPaper {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bSideInputs E Emod) : H5bPaperInputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  disc := fun ε γ L => W.d1 ε γ L + W.d2 ε γ L
  cutoff := fun ε γ L =>
    SteklovAudit.H5CutoffSides.cutoff_of_sides W.P.φ (W.D ε γ L).a (W.D ε γ L).b
      (W.D ε γ L).J L (E ε γ L) (Emod ε γ L) (W.d1 ε γ L) (W.d2 ε γ L)
      (W.trueSide ε γ L) (W.modelSide ε γ L)
  discVanish := SteklovAudit.H5CutoffSides.discVanish_of_sides W.d1 W.d2 W.d1Vanish W.d2Vanish
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

/-- The rebuilt discrepancy is the sum of the two side discrepancies. -/
theorem toPaper_disc {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bSideInputs E Emod) :
    W.toPaper.disc = fun ε γ L => W.d1 ε γ L + W.d2 ε γ L := rfl

/-- The window profile is unchanged by the rebuild. -/
theorem toPaper_P {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bSideInputs E Emod) :
    W.toPaper.P = W.P := rfl

/-- **G19.** The side-form named inputs give the H5b comparison (7.29). -/
theorem h5b_of_sides {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bSideInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_paper W.toPaper

end SteklovAudit.H5SideRows
