import Mathlib
import SteklovAudit.H5DiffCount
import SteklovAudit.H5ColMassSplit

/-!
# G38: the difference row together with the high-energy missing-mass rows

Roadmap item G38.

* `vanish_of_split`: if `m L ≤ c M + hm M L` for every cutoff `M` and every `L`, and for each
  `η > 0` some `M` makes `hm M L ≤ η L` eventually, then `m L ≤ η L` eventually for every `η > 0`.
* `H5bDiffHigh2Inputs E Emod`: `H5bDiffInputs` (G35) with the full missing-mass rows
  `m1`/`rowMiss`/`m1Vanish`, `m2`/`colMiss`/`m2Vanish` replaced by the high-energy rows of
  `H5bHighMass2Inputs` (G31): `hm1`, `rowMissHigh`, `hm1Vanish`, `hm2`, `colMissHigh`, `hm2Vanish`,
  plus the named model low-count row `cB`, `modelLowCount`.
* `H5bDiffHigh2Inputs.toDiff` rebuilds `H5bDiffInputs` (the missing-mass rates are the exact
  missing-mass sums), and `h5b_of_diffHigh2` gives `H5bTarget E Emod`.

The weakening direction `H5bHighMass2Inputs.toDiffHigh2` is deferred to G39 (line budget).

What this file does NOT prove: no difference, missing-mass, high-energy, low-count, Bessel or
tail row is proved for the Dirichlet-to-Neumann operator of the regular tetrahedron or for the
model operator; no field of `H5bDiffHigh2Inputs` is proved for the actual operator; (7.29),
every ledger input [H1]–[H6] and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5DiffHighMass

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5MissingMass

/-- **G38.** A low/high split with an `M`-dependent constant and a vanishing high part vanishes. -/
theorem vanish_of_split (m : ℝ → ℝ) (c : ℝ → ℝ) (hm : ℝ → ℝ → ℝ)
    (hsplit : ∀ M L : ℝ, m L ≤ c M + hm M L)
    (hv : ∀ η : ℝ, 0 < η → ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → hm M L ≤ η * L) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → m L ≤ η * L := by
  intro η hη
  obtain ⟨M, Lhm, hhm⟩ := hv (η / 2) (half_pos hη)
  refine ⟨max Lhm (max 1 (2 * (c M + 1) / η)), fun L hL => ?_⟩
  have hLhm : Lhm ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLc : 2 * (c M + 1) / η ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hhmL : hm M L ≤ (η / 2) * L := hhm L hLhm
  have hmul : 2 * (c M + 1) ≤ L * η := (div_le_iff₀ hη).mp hLc
  have hcl : c M ≤ (η / 2) * L := by nlinarith
  have hs := hsplit M L
  linarith

/-- **G38.** One difference row plus the high-energy missing-mass rows and both low counts. -/
structure H5bDiffHigh2Inputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  e12 : ℝ → ℝ → ℝ → ℝ
  diffCount : ∀ ε γ L : ℝ, |(E ε γ L - Emod ε γ L) -
    (∑ i, P.φ ((D ε γ L).a i - L) - ∑ j, P.φ ((D ε γ L).b j - L))| ≤ e12 ε γ L
  e12Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    e12 ε γ L ≤ η * L
  hm1 : ℝ → ℝ → ℝ → ℝ → ℝ
  rowMissHigh : ∀ ε γ M L : ℝ,
    ∑ i ∈ Finset.univ.filter fun i => M < (D ε γ L).a i,
      (1 - ∑ j, (D ε γ L).J i j ^ 2) ≤ hm1 ε γ M L
  hm1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η →
    ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → hm1 ε γ M L ≤ η * L
  hm2 : ℝ → ℝ → ℝ → ℝ → ℝ
  colMissHigh : ∀ ε γ M L : ℝ,
    ∑ j ∈ Finset.univ.filter fun j => M < (D ε γ L).b j,
      (1 - ∑ i, (D ε γ L).J i j ^ 2) ≤ hm2 ε γ M L
  hm2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η →
    ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → hm2 ε γ M L ≤ η * L
  colBessel : ∀ ε γ L j, ∑ i, (D ε γ L).J i j ^ 2 ≤ 1
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  bessel : ∀ ε γ L i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1
  count : ∀ ε γ L : ℝ, (Fintype.card (Fin (nA ε γ L)) : ℝ) ≤ Cm ε γ * (1 + L) ^ 2
  defect : ∀ ε γ L : ℝ, hs2 (D ε γ L).K ≤ Ck ε γ ^ 2 * (1 + L) ^ 2
  τ : ℝ → ℝ → ℝ → ℝ
  tail : ∀ ε γ M L : ℝ, hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M
  Cτ : ℝ → ℝ → ℝ
  tailRate : SteklovAudit.H5TailRate.TailRate τ Cτ
  ha : ∀ ε γ L i, 0 ≤ (D ε γ L).a i
  hb : ∀ ε γ L j, 0 ≤ (D ε γ L).b j
  c : ℝ → ℝ → ℝ → ℝ
  lowCount : ∀ ε γ M L : ℝ,
    ((Finset.univ.filter fun i => (D ε γ L).a i ≤ M).card : ℝ) ≤ c ε γ M
  cB : ℝ → ℝ → ℝ → ℝ
  modelLowCount : ∀ ε γ M L : ℝ,
    ((Finset.univ.filter fun j => (D ε γ L).b j ≤ M).card : ℝ) ≤ cB ε γ M

/-- **G38.** Rebuild `H5bDiffInputs`: the missing-mass rates are the exact missing masses. -/
noncomputable def H5bDiffHigh2Inputs.toDiff {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bDiffHigh2Inputs E Emod) : SteklovAudit.H5DiffCount.H5bDiffInputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  e12 := W.e12
  diffCount := W.diffCount
  e12Vanish := W.e12Vanish
  m1 := fun ε γ L => ∑ i, (1 - ∑ j, (W.D ε γ L).J i j ^ 2)
  rowMiss := fun ε γ L => le_refl _
  m1Vanish := fun ε γ hε hγ =>
    vanish_of_split (fun L => ∑ i, (1 - ∑ j, (W.D ε γ L).J i j ^ 2)) (W.c ε γ) (W.hm1 ε γ)
      (fun M L => le_trans
        (SteklovAudit.H5MassSplit.missing_split (W.D ε γ L).a (W.D ε γ L).J M (W.bessel ε γ L))
        (add_le_add (W.lowCount ε γ M L) (W.rowMissHigh ε γ M L)))
      (W.hm1Vanish ε γ hε hγ)
  m2 := fun ε γ L => ∑ j, (1 - ∑ i, (W.D ε γ L).J i j ^ 2)
  colMiss := fun ε γ L => le_refl _
  m2Vanish := fun ε γ hε hγ =>
    vanish_of_split (fun L => ∑ j, (1 - ∑ i, (W.D ε γ L).J i j ^ 2)) (W.cB ε γ) (W.hm2 ε γ)
      (fun M L => le_trans
        (SteklovAudit.H5ColMassSplit.col_missing_split (W.D ε γ L).b (W.D ε γ L).J M
          (W.colBessel ε γ L))
        (add_le_add (W.modelLowCount ε γ M L) (W.colMissHigh ε γ M L)))
      (W.hm2Vanish ε γ hε hγ)
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

/-- **G38.** The difference row with high-energy missing-mass rows gives the H5b target (7.29). -/
theorem h5b_of_diffHigh2 {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bDiffHigh2Inputs E Emod) :
    H5bTarget E Emod :=
  SteklovAudit.H5DiffCount.h5b_of_diff W.toDiff

end SteklovAudit.H5DiffHighMass
