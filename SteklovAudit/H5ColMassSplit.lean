import Mathlib
import SteklovAudit.H5MassSplit

/-!
# G31: column mirror of the low/high missing-mass split for H5b

Roadmap item G31.

* `col_missing_split`: under the column Bessel bound `∀ j, ∑ i, J i j ^ 2 ≤ 1`, the total
  column missing mass splits into a model low-energy count plus the high-energy column
  missing mass (G28's `missing_split` applied to the transpose).

* `H5bHighMass2Inputs`: `H5bHighMassInputs` (G29) with the full column rate `m2` replaced by a
  high-energy column rate `hm2`, plus a NEW named row `modelLowCount` (an L-uniform count of
  the model eigenvalues `b j ≤ M`). `toHigh` rebuilds `H5bHighMassInputs`, hence `H5bTarget`.

What this file does NOT prove: no missing-mass, high-energy tail, low-count or growth
estimate for the Dirichlet-to-Neumann operator of the regular tetrahedron or for the model
operator; no Sobolev trace or partition of unity is constructed; (7.2), (7.29),
(7.38)/(7.45), (9.1) and every ledger hypothesis [H1]–[H6] remain open for the actual
operator. `modelLowCount` is a new named hypothesis, not a theorem.
-/

namespace SteklovAudit.H5ColMassSplit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5SideRows SteklovAudit.H5MissingMass SteklovAudit.H5CountRows
open SteklovAudit.H5MassSplit

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- G31. Low/high split of the total column missing mass (transpose of G28). -/
theorem col_missing_split (b : κ → ℝ) (J : ι → κ → ℝ) (M : ℝ)
    (hB : ∀ j, ∑ i, J i j ^ 2 ≤ 1) :
    ∑ j, (1 - ∑ i, J i j ^ 2) ≤
      ((Finset.univ.filter fun j => b j ≤ M).card : ℝ) +
      ∑ j ∈ Finset.univ.filter fun j => M < b j, (1 - ∑ i, J i j ^ 2) := by
  first
    | exact missing_split b (fun j i => J i j) M hB
    | simpa using missing_split b (fun j i => J i j) M hB

/-- G31. High-energy form of both missing-mass rows, with a named model low-count row. -/
structure H5bHighMass2Inputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  e1 : ℝ → ℝ → ℝ → ℝ
  trueCount : ∀ ε γ L : ℝ, |E ε γ L - ∑ i, P.φ ((D ε γ L).a i - L)| ≤ e1 ε γ L
  e1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    e1 ε γ L ≤ η * L
  hm1 : ℝ → ℝ → ℝ → ℝ → ℝ
  rowMissHigh : ∀ ε γ M L : ℝ,
    ∑ i ∈ Finset.univ.filter fun i => M < (D ε γ L).a i,
      (1 - ∑ j, (D ε γ L).J i j ^ 2) ≤ hm1 ε γ M L
  hm1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η →
    ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → hm1 ε γ M L ≤ η * L
  e2 : ℝ → ℝ → ℝ → ℝ
  modelCount : ∀ ε γ L : ℝ, |Emod ε γ L - ∑ j, P.φ ((D ε γ L).b j - L)| ≤ e2 ε γ L
  e2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    e2 ε γ L ≤ η * L
  hm2 : ℝ → ℝ → ℝ → ℝ → ℝ
  /-- High-energy column missing mass. -/
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
  /-- NEW row: L-uniform model low count. -/
  modelLowCount : ∀ ε γ M L : ℝ,
    ((Finset.univ.filter fun j => (D ε γ L).b j ≤ M).card : ℝ) ≤ cB ε γ M

/-- G31. Rebuild G29's structure: the full column rate is the column missing mass itself. -/
noncomputable def H5bHighMass2Inputs.toHigh {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bHighMass2Inputs E Emod) : H5bHighMassInputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  e1 := W.e1
  trueCount := W.trueCount
  e1Vanish := W.e1Vanish
  hm1 := W.hm1
  rowMissHigh := W.rowMissHigh
  hm1Vanish := W.hm1Vanish
  e2 := W.e2
  modelCount := W.modelCount
  e2Vanish := W.e2Vanish
  m2 := fun ε γ L => ∑ j, (1 - ∑ i, (W.D ε γ L).J i j ^ 2)
  colMiss := fun ε γ L => le_refl _
  m2Vanish := by
    intro ε γ hε hγ η hη
    obtain ⟨M, Lhm, hhm⟩ := W.hm2Vanish ε γ hε hγ (η / 2) (half_pos hη)
    let c0 := W.cB ε γ M
    refine ⟨max Lhm (max 1 (2 * (c0 + 1) / η)), fun L hL => ?_⟩
    have hLhm : Lhm ≤ L := le_trans (le_max_left _ _) hL
    have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
    have hLc : 2 * (c0 + 1) / η ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    have hsplit := col_missing_split (W.D ε γ L).b (W.D ε γ L).J M (W.colBessel ε γ L)
    have hhigh := W.colMissHigh ε γ M L
    have hlow := W.modelLowCount ε γ M L
    have hhmL : W.hm2 ε γ M L ≤ (η / 2) * L := hhm L hLhm
    have htot : ∑ j, (1 - ∑ i, (W.D ε γ L).J i j ^ 2) ≤ c0 + W.hm2 ε γ M L := by
      calc
        _ ≤ ((Finset.univ.filter fun j => (W.D ε γ L).b j ≤ M).card : ℝ) +
            ∑ j ∈ Finset.univ.filter fun j => M < (W.D ε γ L).b j,
              (1 - ∑ i, (W.D ε γ L).J i j ^ 2) := hsplit
        _ ≤ c0 + W.hm2 ε γ M L := add_le_add hlow hhigh
    have hcl : c0 ≤ (η / 2) * L := by
      have hmul : 2 * (c0 + 1) ≤ L * η := (div_le_iff₀ hη).mp hLc
      nlinarith
    calc
      ∑ j, (1 - ∑ i, (W.D ε γ L).J i j ^ 2) ≤ c0 + W.hm2 ε γ M L := htot
      _ ≤ (η / 2) * L + (η / 2) * L := add_le_add hcl hhmL
      _ = η * L := by ring
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

/-- G31. Both high-energy missing-mass rows plus both low counts give the H5b target. -/
theorem h5b_of_high_mass2 {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bHighMass2Inputs E Emod) : H5bTarget E Emod :=
  h5b_of_high_mass W.toHigh

end SteklovAudit.H5ColMassSplit
