import Mathlib
import SteklovAudit.H5LowMass

/-!
# G13: the H5b comparison (7.29) with two rows replaced by weaker named inputs

Roadmap item G13. `H5bWeakInputs E Emod` is `H5bInputs E Emod` (F1) with

* the field `tailVanish` replaced by a decay rate `TailRate τ Cτ` on `τ` alone (G9), and
* the fields `κ2`, `lowDefect` replaced by nonnegative energies plus an L-uniform low-energy mass
  bound `LowMass D m` on the identification `J` (G10/G11).

`H5bWeakInputs.toInputs` (a `def`) rebuilds an `H5bInputs` with `κ2 ε γ M := M ^ 2 * m ε γ M`,
and `h5b_of_weak` gives `H5bTarget E Emod` through `h5b_of_inputs`. The `cutoff`, `discVanish`,
`pde`, `tail` and Lipschitz rows are copied unchanged.

What this file does NOT prove: no field of `H5bWeakInputs` is proved for the Steklov operator of
the tetrahedron (in particular neither the tail rate nor the low-energy mass bound); no
Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1
remain conditional on the named inputs.
-/

namespace SteklovAudit.H5WeakRows

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- **G13.** `H5bInputs` with the tail row as a decay rate and the low-energy defect row as a
low-energy mass bound on `J` plus nonnegative energies. -/
structure H5bWeakInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  F : ℝ → ℝ → ℝ → ℝ → ℝ
  disc : ℝ → ℝ → ℝ → ℝ
  /-- Row: finite cutoff → continuous model spectrum (unchanged). -/
  cutoff : ∀ ε γ L : ℝ, |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j,
    (F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)) * (D ε γ L).J i j ^ 2| ≤ disc ε γ L
  discVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    disc ε γ L ≤ η * L
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  /-- Rows: localized spectral mass (2.2) and uniform localized HS defect (unchanged). -/
  pde : ∀ ε γ L : ℝ, PDEInputs (D ε γ L) L (Cm ε γ) (Ck ε γ)
  τ : ℝ → ℝ → ℝ → ℝ
  /-- Row: high-energy defect tail (unchanged). -/
  tail : ∀ ε γ M L : ℝ, hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M
  /-- Weaker row (G9): power-type decay of the tail, replacing `tailVanish`. -/
  Cτ : ℝ → ℝ → ℝ
  tailRate : SteklovAudit.H5TailRate.TailRate τ Cτ
  /-- Weaker row (G10/G11): nonnegative energies and low-energy mass, replacing `lowDefect`. -/
  ha : ∀ ε γ L i, 0 ≤ (D ε γ L).a i
  hb : ∀ ε γ L j, 0 ≤ (D ε γ L).b j
  m : ℝ → ℝ → ℝ → ℝ
  lowMass : SteklovAudit.H5LowMass.LowMass D m
  Λ0 : ℝ → ℝ → ℝ
  hΛ0 : ∀ ε γ, 0 ≤ Λ0 ε γ
  lam : ℝ → ℝ → ℝ → ℝ → ℝ
  hlam : ∀ ε γ M L, 0 ≤ lam ε γ M L
  /-- Row: Lipschitz-type bounds for the smoothed counting test (unchanged). -/
  lipHi : ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), hiE (D ε γ L) M i j →
    |F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)|
      ≤ Λ0 ε γ * |(D ε γ L).a i - (D ε γ L).b j|
  lipLo : ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), ¬ hiE (D ε γ L) M i j →
    |F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)|
      ≤ lam ε γ M L * |(D ε γ L).a i - (D ε γ L).b j|
  lamVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    lam ε γ M L ≤ η

/-- **G13.** The weak inputs rebuild the F1 inputs, with `κ2 ε γ M := M ^ 2 * m ε γ M`. -/
noncomputable def H5bWeakInputs.toInputs {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bWeakInputs E Emod) : H5bInputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  F := W.F
  disc := W.disc
  cutoff := W.cutoff
  discVanish := W.discVanish
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
  pde := W.pde
  τ := W.τ
  tail := W.tail
  tailVanish := SteklovAudit.H5TailRate.tailVanish_of_power W.tailRate
  κ2 := fun ε γ M => M ^ 2 * W.m ε γ M
  lowDefect := SteklovAudit.H5LowMass.lowDefect_of_LowMass W.D W.ha W.hb W.m W.lowMass
  Λ0 := W.Λ0
  hΛ0 := W.hΛ0
  lam := W.lam
  hlam := W.hlam
  lipHi := W.lipHi
  lipLo := W.lipLo
  lamVanish := W.lamVanish

/-- The rebuilt low-energy defect bound is `M ^ 2 * m`. -/
theorem toInputs_κ2 {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bWeakInputs E Emod) (ε γ M : ℝ) :
    W.toInputs.κ2 ε γ M = M ^ 2 * W.m ε γ M := rfl

/-- The cutoff data are unchanged by the rebuild. -/
theorem toInputs_disc {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bWeakInputs E Emod) :
    W.toInputs.disc = W.disc := rfl

/-- **G13.** The weak named inputs give the H5b comparison (7.29). -/
theorem h5b_of_weak {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bWeakInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_inputs W.toInputs

end SteklovAudit.H5WeakRows
