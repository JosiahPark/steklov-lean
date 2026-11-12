import Mathlib
import SteklovAudit.H5WeakRows
import SteklovAudit.H5LowCount
import SteklovAudit.H5WindowProfile

/-!
# G16: the H5b comparison (7.29) with the F table rows in paper form

Roadmap item G16. `H5bPaperInputs E Emod` is `H5bWeakInputs E Emod` (G13) with

* the field `pde` replaced by a Bessel bound on the rows of `J`, a Weyl count
  `(Fintype.card (Fin nA) : ℝ) ≤ Cm * (1 + L) ^ 2` (G12) and the `defect` field of `PDEInputs`
  (Lemma 7.1′) copied verbatim;
* the field `lowMass` replaced by an L-uniform count of eigenvalues `≤ M` (G15), using the same
  Bessel bound;
* the test `F` and the Lipschitz group `Λ0`, `hΛ0`, `lam`, `hlam`, `lipHi`, `lipLo`, `lamVanish`
  replaced by a single window profile `P : ProfileLipRows` with `F ε γ L x = P.φ (x - L)` (G7).

`H5bPaperInputs.toWeak` (a `def`) rebuilds an `H5bWeakInputs`, and `h5b_of_paper` gives
`H5bTarget E Emod` through `h5b_of_weak`. The F table rows are now: cutoff (with `discVanish`),
Lemma 7.1′ defect, Bessel, Weyl count, tail bound with tail rate, nonnegative energies, low count,
window profile.

What this file does NOT prove: no field of `H5bPaperInputs` is proved for the Steklov operator of
the tetrahedron; in particular the cutoff row still carries all of the "target in disguise" content
(G2, G3, G14), and it is not checked here that the paper's smoothed count has the translated form
`φ (x - L)`. No Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and
Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5PaperRows

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile

/-- **G16.** The H5b inputs in paper form: cutoff, Lemma 7.1′ defect, Bessel, Weyl count, tail
rate, nonnegative energies, low count and a window profile. -/
structure H5bPaperInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  /-- Row: window profile (G7); the test is `F ε γ L x = P.φ (x - L)`. -/
  P : ProfileLipRows
  disc : ℝ → ℝ → ℝ → ℝ
  /-- Row: finite cutoff → continuous model spectrum, for the translated profile. -/
  cutoff : ∀ ε γ L : ℝ, |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j,
    (P.φ ((D ε γ L).a i - L) - P.φ ((D ε γ L).b j - L)) * (D ε γ L).J i j ^ 2| ≤ disc ε γ L
  discVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    disc ε γ L ≤ η * L
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

/-- **G16.** The paper-form inputs rebuild the weak inputs of G13. -/
noncomputable def H5bPaperInputs.toWeak {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bPaperInputs E Emod) : H5bWeakInputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  F := fun _ _ L x => W.P.φ (x - L)
  disc := W.disc
  cutoff := W.cutoff
  discVanish := W.discVanish
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
  pde := fun ε γ L => SteklovAudit.H5MassRow.pde_of_bessel_count (W.D ε γ L) L (W.Cm ε γ)
    (W.Ck ε γ) (W.bessel ε γ L) (W.count ε γ L) (W.defect ε γ L)
  τ := W.τ
  tail := W.tail
  Cτ := W.Cτ
  tailRate := W.tailRate
  ha := W.ha
  hb := W.hb
  m := W.c
  lowMass := SteklovAudit.H5LowCount.lowMass_of_bessel_lowCount W.D W.c W.bessel W.lowCount
  Λ0 := fun _ _ => W.P.Λ0
  hΛ0 := (lipGroup_of_profile W.P W.D).1
  lam := fun _ _ M L => profLam W.P.Λ0 W.P.ψ M L
  hlam := (lipGroup_of_profile W.P W.D).2.2.1
  lipHi := (lipGroup_of_profile W.P W.D).2.1
  lipLo := (lipGroup_of_profile W.P W.D).2.2.2.1
  lamVanish := (lipGroup_of_profile W.P W.D).2.2.2.2

/-- The rebuilt test is the translated window profile. -/
theorem toWeak_F {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bPaperInputs E Emod) (ε γ L x : ℝ) :
    W.toWeak.F ε γ L x = W.P.φ (x - L) := rfl

/-- The rebuilt low-energy mass bound is the low count. -/
theorem toWeak_m {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bPaperInputs E Emod) :
    W.toWeak.m = W.c := rfl

/-- The cutoff data are unchanged by the rebuild. -/
theorem toWeak_disc {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bPaperInputs E Emod) :
    W.toWeak.disc = W.disc := rfl

/-- **G16.** The paper-form named inputs give the H5b comparison (7.29). -/
theorem h5b_of_paper {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bPaperInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_weak W.toWeak

end SteklovAudit.H5PaperRows
