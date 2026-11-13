import Mathlib
import SteklovAudit.H5MassAudit
import SteklovAudit.H5MassSplit

/-!
# G30: audit of the high-energy missing-mass H5b inputs `H5bHighMassInputs` (G29)

Roadmap item G30.

* `highMassWitness : H5bHighMassInputs 0 0`, `highMassWitness_nonempty`: the structure is not vacuous
  (G24's empty family `zData`, profile `arctan`, `Φ = 2`, `hm1 = 0`, `m2 = 0`; the low-count rate is
  `c = 1`, reusing G24's `z_lowCount`).
* Example: `⌈L⌉₊` true eigenvalues all at `0`, `J = 0` (`Fin 1` columns). `zero_rowMissHigh`: the
  high-energy row holds with `hm1 = 0` for every `M ≥ 0` (the filter `M < 0` is empty).
  `zero_rowMass`: the full missing row mass is `⌈L⌉₊`, so (G27's `atL_rowMiss_fails`) no vanishing `m1`
  meets G26's `rowMiss`. `zero_not_lowCount`: the same family violates every L-uniform `lowCount`.
  So the high-energy row alone is strictly weaker than the full missing-mass row; the gap is exactly the
  low count.

What this file does NOT prove: no missing-mass, high-energy, low-count or Bessel row is proved for the
Steklov operator of the tetrahedron (or for any concrete operator); the empty family and the `⌈L⌉₊`
example are consistency checks, not models of the spectrum; no Dirichlet-to-Neumann operator is
constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5HighMassAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows SteklovAudit.H5CountAudit SteklovAudit.H5MissingMass
open SteklovAudit.H5MassAudit SteklovAudit.H5MassSplit

theorem z_rowMissHigh (M : ℝ) :
    ∑ i ∈ Finset.univ.filter fun i => M < zData.a i, (1 - ∑ j, zData.J i j ^ 2) ≤ 0 := by
  first
    | exact (Finset.sum_eq_zero fun i _ => Fin.elim0 i).le
    | (simp; done)

/-- **G30.** An explicit witness of the high-energy missing-mass inputs with `E = Emod = 0`. -/
noncomputable def highMassWitness :
    H5bHighMassInputs (fun _ _ _ => 0) (fun _ _ _ => 0) where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => zData
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  e1 := fun _ _ _ => 0
  trueCount := z_trueCount (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound
  e1Vanish := zeroDisc_vanish
  hm1 := fun _ _ _ _ => 0
  rowMissHigh := fun _ _ M _ => z_rowMissHigh M
  hm1Vanish := fun _ _ _ _ η hη =>
    ⟨0, 0, fun L hL => show (0 : ℝ) ≤ η * L from mul_nonneg hη.le hL⟩
  e2 := fun _ _ _ => 0
  modelCount := z_modelCount (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound
  e2Vanish := zeroDisc_vanish
  m2 := fun _ _ _ => 0
  colMiss := fun _ _ _ => z_colMiss
  m2Vanish := zeroDisc_vanish
  colBessel := fun _ _ _ j => z_colBessel j
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  bessel := fun _ _ _ i => z_bessel i
  count := fun _ _ L => z_count L
  defect := fun _ _ L => z_defect L
  τ := fun _ _ _ => 0
  tail := fun _ _ M _ => z_tail M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 1
  lowCount := fun _ _ M _ => z_lowCount M

theorem highMassWitness_nonempty :
    Nonempty (H5bHighMassInputs (fun _ _ _ => 0) (fun _ _ _ => 0)) :=
  ⟨highMassWitness⟩

/-- G30 example: eigenvalues at `0`, `J = 0`; for `M ≥ 0` no eigenvalue exceeds `M`, so the
high-energy missing mass is `0` and `rowMissHigh` holds with `hm1 = 0`. -/
theorem zero_rowMissHigh (M L : ℝ) (hM : 0 ≤ M) :
    ∑ i ∈ Finset.univ.filter fun i : Fin ⌈L⌉₊ => M < (fun _ : Fin ⌈L⌉₊ => (0 : ℝ)) i,
      (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) ≤ 0 := by
  apply le_of_eq
  refine Finset.sum_eq_zero fun i hi => ?_
  have h2 : M < 0 := (Finset.mem_filter.mp hi).2
  exact absurd h2 (not_lt.mpr hM)

/-- G30 example: the full missing row mass is `⌈L⌉₊` (same `J = 0` as G27). -/
theorem zero_rowMass (L : ℝ) :
    ∑ i : Fin ⌈L⌉₊,
      (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) = (⌈L⌉₊ : ℝ) :=
  atL_rowMass L

/-- G30 example: no L-uniform low count `c M` bounds the number of eigenvalues `≤ M`. -/
theorem zero_not_lowCount :
    ¬ ∃ c : ℝ → ℝ, ∀ M L : ℝ,
      ((Finset.univ.filter fun i : Fin ⌈L⌉₊ => (fun _ : Fin ⌈L⌉₊ => (0 : ℝ)) i ≤ M).card : ℝ)
        ≤ c M := by
  rintro ⟨c, hc⟩
  have h := hc 0 (c 0 + 1)
  have hf : (Finset.univ.filter fun i : Fin ⌈c 0 + 1⌉₊ =>
      (fun _ : Fin ⌈c 0 + 1⌉₊ => (0 : ℝ)) i ≤ 0) = Finset.univ := by
    first
      | exact Finset.filter_true_of_mem fun i _ => le_refl (0 : ℝ)
      | exact Finset.filter_eq_self.mpr fun i _ => le_refl (0 : ℝ)
      | (ext i; simp)
  have hcard : ((Finset.univ.filter fun i : Fin ⌈c 0 + 1⌉₊ =>
      (fun _ : Fin ⌈c 0 + 1⌉₊ => (0 : ℝ)) i ≤ 0).card : ℝ) = (⌈c 0 + 1⌉₊ : ℝ) := by
    rw [hf, Finset.card_univ, Fintype.card_fin]
  have h' : (⌈c 0 + 1⌉₊ : ℝ) ≤ c 0 := le_trans hcard.symm.le h
  have hceil : c 0 + 1 ≤ (⌈c 0 + 1⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-- **G30.** The high-energy row is strictly weaker than G26's full missing-mass row: in the example
(`⌈L⌉₊` eigenvalues at `0`, `J = 0`) `rowMissHigh` holds with `hm1 = 0` for every `M ≥ 0`, the full
missing row mass is `⌈L⌉₊`, and no vanishing `m1` meets `rowMiss`. The gap is the low count
(`zero_not_lowCount`). -/
theorem zero_rowMissHigh_not_mass :
    (∀ M L : ℝ, 0 ≤ M →
      ∑ i ∈ Finset.univ.filter fun i : Fin ⌈L⌉₊ => M < (fun _ : Fin ⌈L⌉₊ => (0 : ℝ)) i,
        (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) ≤ 0) ∧
    (∀ L : ℝ, ∑ i : Fin ⌈L⌉₊,
      (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) = (⌈L⌉₊ : ℝ)) ∧
    ¬ ∃ m1 : ℝ → ℝ → ℝ → ℝ,
      (∀ ε γ L : ℝ, ∑ i : Fin ⌈L⌉₊,
        (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) ≤ m1 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        m1 ε γ L ≤ η * L) :=
  ⟨zero_rowMissHigh, zero_rowMass, atL_rowMiss_fails⟩

end SteklovAudit.H5HighMassAudit
