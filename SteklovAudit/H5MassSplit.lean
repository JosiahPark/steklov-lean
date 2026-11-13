import Mathlib
import SteklovAudit.H5MissingMass
import SteklovAudit.H5CountRows

/-!
# G28–G29: low/high split of the row missing mass for H5b

Roadmap items G28 and G29.

* G28: over a `Fintype ι`, for a coefficient array `J` with the Bessel row bound
  `∀ i, ∑ j, J i j ^ 2 ≤ 1`, the row missing masses `1 - ∑ j J i j ^ 2` are nonnegative
  and at most 1. Their total splits into a low-energy count plus the high-energy missing
  mass: `∑ i (1 - r i) ≤ (filter (a i ≤ M)).card + ∑_{i : M < a i} (1 - r i)`.

* G29: `H5bHighMassInputs` replaces the full row missing-mass rate `m1` by a high-energy
  rate `hm1`. Given the already-present L-uniform low-count row, the full missing mass is
  recovered by the split, so the structure rebuilds `H5bMassInputs` and therefore
  `H5bTarget`. The high-energy row is strictly weaker than the full missing-mass row
  whenever a vanishing low count is available.

What this file does NOT prove: no missing-mass, high-energy tail, or low-count estimate
for the Dirichlet-to-Neumann operator of the regular tetrahedron; no Sobolev trace or
partition of unity is constructed; (7.2), (7.29), (7.38)/(7.45), (9.1) and every ledger
hypothesis [H1]–[H6] remain open for the actual operator. The statements are abstract
spectral-coordinate reductions only.
-/

namespace SteklovAudit.H5MassSplit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5SideRows SteklovAudit.H5MissingMass SteklovAudit.H5CountRows

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- G28. Nonnegativity of each row missing mass under the Bessel row bound. -/
theorem missing_nonneg (J : ι → κ → ℝ) (hB : ∀ i, ∑ j, J i j ^ 2 ≤ 1) (i : ι) :
    0 ≤ 1 - ∑ j, J i j ^ 2 := by
  exact sub_nonneg.mpr (hB i)

/-- G28. Each row missing mass is at most 1 (since the squared mass is nonnegative). -/
theorem missing_le_one (J : ι → κ → ℝ) (i : ι) :
    1 - ∑ j, J i j ^ 2 ≤ 1 := by
  have hnon : 0 ≤ ∑ j, J i j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (J i j)
  linarith

/-- G28. Low/high split of the total row missing mass.
The low-energy contribution is bounded by the number of low eigenvalues; the high-energy
contribution is kept as an explicit sum. -/
theorem missing_split (a : ι → ℝ) (J : ι → κ → ℝ) (M : ℝ)
    (hB : ∀ i, ∑ j, J i j ^ 2 ≤ 1) :
    ∑ i, (1 - ∑ j, J i j ^ 2) ≤
      ((Finset.univ.filter fun i => a i ≤ M).card : ℝ) +
      ∑ i ∈ Finset.univ.filter fun i => M < a i, (1 - ∑ j, J i j ^ 2) := by
  let r (i : ι) := ∑ j, J i j ^ 2
  have hle1 : ∀ i, 1 - r i ≤ 1 := fun i => missing_le_one J i
  have hsplit := Finset.sum_filter_add_sum_filter_not (p := fun i => a i ≤ M)
    (s := Finset.univ) (f := fun i => 1 - r i)
  have hlow : ∑ i ∈ Finset.univ.filter fun i => a i ≤ M, (1 - r i) ≤
      ((Finset.univ.filter fun i => a i ≤ M).card : ℝ) := by
    calc
      ∑ i ∈ Finset.univ.filter fun i => a i ≤ M, (1 - r i)
          ≤ ∑ i ∈ Finset.univ.filter fun i => a i ≤ M, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hle1 i
      _ = ((Finset.univ.filter fun i => a i ≤ M).card : ℝ) := by
        simp
  have hhigh : ∑ i ∈ Finset.univ.filter fun i => ¬ (a i ≤ M), (1 - r i) =
      ∑ i ∈ Finset.univ.filter fun i => M < a i, (1 - r i) :=
    Finset.sum_congr (Finset.filter_congr fun i _ => not_le) fun _ _ => rfl
  calc
    ∑ i, (1 - r i) = ∑ i ∈ Finset.univ.filter fun i => a i ≤ M, (1 - r i) +
                      ∑ i ∈ Finset.univ.filter fun i => ¬ (a i ≤ M), (1 - r i) := hsplit
    _ ≤ ((Finset.univ.filter fun i => a i ≤ M).card : ℝ) +
        ∑ i ∈ Finset.univ.filter fun i => M < a i, (1 - r i) := by
      rw [hhigh]
      exact add_le_add hlow le_rfl

/-- G29. High-energy form of the missing-mass inputs.
Replaces the full row rate `m1` by a high-energy rate `hm1`; the low-energy contribution
is controlled by the existing `lowCount` row. -/
structure H5bHighMassInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
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
  /-- High-energy row missing mass. -/
  rowMissHigh : ∀ ε γ M L : ℝ,
    ∑ i ∈ Finset.univ.filter fun i => M < (D ε γ L).a i,
      (1 - ∑ j, (D ε γ L).J i j ^ 2) ≤ hm1 ε γ M L
  hm1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η →
    ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → hm1 ε γ M L ≤ η * L
  e2 : ℝ → ℝ → ℝ → ℝ
  modelCount : ∀ ε γ L : ℝ, |Emod ε γ L - ∑ j, P.φ ((D ε γ L).b j - L)| ≤ e2 ε γ L
  e2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    e2 ε γ L ≤ η * L
  m2 : ℝ → ℝ → ℝ → ℝ
  colMiss : ∀ ε γ L : ℝ, ∑ j, (1 - ∑ i, (D ε γ L).J i j ^ 2) ≤ m2 ε γ L
  m2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m2 ε γ L ≤ η * L
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

/-- G29. Rebuild the full missing-mass structure from the high-energy form.
The full rate is the total missing mass itself (so `rowMiss` is reflexivity);
vanishing follows from the split, the low-count bound, and high-energy vanishing. -/
noncomputable def H5bHighMassInputs.toMass {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bHighMassInputs E Emod) : H5bMassInputs E Emod where
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
  m1 := fun ε γ L => ∑ i, (1 - ∑ j, (W.D ε γ L).J i j ^ 2)
  rowMiss := fun ε γ L => le_refl _
  m1Vanish := by
    intro ε γ hε hγ η hη
    obtain ⟨M, Lhm, hhm⟩ := W.hm1Vanish ε γ hε hγ (η / 2) (half_pos hη)
    -- Low-count bound c ε γ M is independent of L; enlarge threshold to absorb it.
    let c0 := W.c ε γ M
    refine ⟨max Lhm (max 1 (2 * (c0 + 1) / η)), fun L hL => ?_⟩
    have hLhm : Lhm ≤ L := le_trans (le_max_left _ _) hL
    have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
    have hLc : 2 * (c0 + 1) / η ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    have hsplit := missing_split (W.D ε γ L).a (W.D ε γ L).J M (W.bessel ε γ L)
    have hhigh := W.rowMissHigh ε γ M L
    have hlow := W.lowCount ε γ M L
    have hhmL : W.hm1 ε γ M L ≤ (η / 2) * L := hhm L hLhm
    have htot : ∑ i, (1 - ∑ j, (W.D ε γ L).J i j ^ 2) ≤ c0 + W.hm1 ε γ M L := by
      calc
        _ ≤ ((Finset.univ.filter fun i => (W.D ε γ L).a i ≤ M).card : ℝ) +
            ∑ i ∈ Finset.univ.filter fun i => M < (W.D ε γ L).a i,
              (1 - ∑ j, (W.D ε γ L).J i j ^ 2) := hsplit
        _ ≤ c0 + W.hm1 ε γ M L := add_le_add hlow hhigh
    have hcl : c0 ≤ (η / 2) * L := by
      have hmul : 2 * (c0 + 1) ≤ L * η := (div_le_iff₀ hη).mp hLc
      nlinarith
    calc
      ∑ i, (1 - ∑ j, (W.D ε γ L).J i j ^ 2) ≤ c0 + W.hm1 ε γ M L := htot
      _ ≤ (η / 2) * L + (η / 2) * L := add_le_add hcl hhmL
      _ = η * L := by ring
  e2 := W.e2
  modelCount := W.modelCount
  e2Vanish := W.e2Vanish
  m2 := W.m2
  colMiss := W.colMiss
  m2Vanish := W.m2Vanish
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

/-- G29. The high-energy form yields the H5b target through the missing-mass reduction. -/
theorem h5b_of_high_mass {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bHighMassInputs E Emod) : H5bTarget E Emod :=
  h5b_of_mass W.toMass

end SteklovAudit.H5MassSplit
