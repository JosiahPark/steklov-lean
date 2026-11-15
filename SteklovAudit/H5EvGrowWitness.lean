import Mathlib
import SteklovAudit.H5EvPaperScale
import SteklovAudit.H5ColNormEvAudit

/-!
# G60: the paper-scale count row exercised on unbounded truncations

Roadmap item G60. Every earlier witness of the smoothed route had truncation sizes bounded in `L`, so
the count row was only tested on bounded data. Here:

* `growD n`: `n` true and `n` model eigenvalues at `0, 1, …, n - 1`, identity coupling; row and
  column normalization hold (`growD_rowNorm`, `growD_colNorm`) and the defect vanishes (`growD_K`);
* `growD_count`: `⌊L⌋₊ ≤ 1 · L²` for `1 ≤ L`; `growD_lowCount`: at most `|M| + 1` eigenvalues `≤ M`;
* `growWitness`: an `H5bPaperScaleInputs` (G58) with `nA = nB = ⌊L⌋₊`, `Cm = 1`, `Ck = 0`, `τ = 0`,
  zero missing-mass rates, `c M = |M| + 1`, profile `arctanProfile`;
* `growWitness_unbounded`: its truncation sizes are unbounded; `growWitness_target`: `H5bTarget`
  for its smoothed counts (from `h5b_of_paperScale`).

What this file does NOT prove: the witness is a test family, not a model of the Steklov spectrum;
the count, defect, tail, low-count and normalization rows are not proved for any actual coupling or
for the Steklov operator of the tetrahedron; that the paper's `E`, `Emod` are the smoothed counts is
not proved; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and
Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5EvGrowWitness

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5EvPaperScale

/-- Eigenvalues `0, 1, …, n - 1` on both sides, identity coupling. -/
def growD (n : ℕ) : Data (Fin n) (Fin n) where
  a := fun i => ((i.val : ℕ) : ℝ)
  b := fun j => ((j.val : ℕ) : ℝ)
  J := fun i j => if i = j then (1 : ℝ) else 0

theorem growD_rowNorm (n : ℕ) (i : Fin n) : ∑ j, (growD n).J i j ^ 2 = 1 := by
  have h : ∀ j : Fin n, (growD n).J i j ^ 2 = if i = j then 1 else 0 := by
    intro j
    show (if i = j then (1 : ℝ) else 0) ^ 2 = _
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  first | simp | exact (Finset.sum_ite_eq _ _ _).trans (if_pos (Finset.mem_univ _))

theorem growD_colNorm (n : ℕ) (j : Fin n) : ∑ i, (growD n).J i j ^ 2 = 1 := by
  have h : ∀ i : Fin n, (growD n).J i j ^ 2 = if i = j then 1 else 0 := by
    intro i
    show (if i = j then (1 : ℝ) else 0) ^ 2 = _
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  first | simp | exact (Finset.sum_ite_eq' _ _ _).trans (if_pos (Finset.mem_univ _))

theorem growD_K (n : ℕ) (i j : Fin n) : (growD n).K i j = 0 := by
  show (((i.val : ℕ) : ℝ) - ((j.val : ℕ) : ℝ)) * (if i = j then (1 : ℝ) else 0) = 0
  split_ifs with h
  · subst h; ring
  · ring

theorem growD_hs2K (n : ℕ) : hs2 (growD n).K = 0 := by
  first | simp [hs2, growD_K] | (unfold hs2; simp [growD_K])

theorem growD_rowMiss (n : ℕ) : ∑ i, (1 - ∑ j, (growD n).J i j ^ 2) ≤ 0 := by
  first
    | simp only [growD_rowNorm, sub_self, Finset.sum_const_zero, le_refl]
    | simp [growD_rowNorm]

theorem growD_colMiss (n : ℕ) : ∑ j, (1 - ∑ i, (growD n).J i j ^ 2) ≤ 0 := by
  first
    | simp only [growD_colNorm, sub_self, Finset.sum_const_zero, le_refl]
    | simp [growD_colNorm]

theorem growD_count (L : ℝ) (h : 1 ≤ L) : (Fintype.card (Fin ⌊L⌋₊) : ℝ) ≤ 1 * L ^ 2 := by
  rw [Fintype.card_fin, one_mul]
  have h1 : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ L)]

theorem growD_lowCount (n : ℕ) (M : ℝ) :
    ((Finset.univ.filter fun i => (growD n).a i ≤ M).card : ℝ) ≤ |M| + 1 := by
  have hinj : (Finset.univ.filter fun i => (growD n).a i ≤ M).card ≤
      (Finset.range (⌊|M|⌋₊ + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val)
    · intro i hi
      have hi' : ((i.val : ℕ) : ℝ) ≤ M := by
        first
          | exact (Finset.mem_filter.mp hi).2
          | exact (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
          | simpa [growD] using hi
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.le_floor (hi'.trans (le_abs_self M)))
    · intro i _ j _ hij
      exact Fin.ext hij
  rw [Finset.card_range] at hinj
  have h2 : (⌊|M|⌋₊ : ℝ) ≤ |M| := Nat.floor_le (abs_nonneg M)
  have h3 : ((Finset.univ.filter fun i => (growD n).a i ≤ M).card : ℝ) ≤ (⌊|M|⌋₊ : ℝ) + 1 := by
    exact_mod_cast hinj
  linarith

/-- **G60.** A G58 input set whose truncation sizes `⌊L⌋₊` grow without bound. -/
noncomputable def growWitness : H5bPaperScaleInputs where
  nA := fun _ _ L => ⌊L⌋₊
  nB := fun _ _ L => ⌊L⌋₊
  D := fun _ _ L => growD ⌊L⌋₊
  P := SteklovAudit.H5WindowWitness.arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := SteklovAudit.H5SideAudit.arctan_abs_le_two
  m1 := fun _ _ _ => 0
  rowMiss := fun _ _ L _ => growD_rowMiss ⌊L⌋₊
  m1Vanish := SteklovAudit.H5Parseval.zero_vanish
  m2 := fun _ _ _ => 0
  colMiss := fun _ _ L _ => growD_colMiss ⌊L⌋₊
  m2Vanish := SteklovAudit.H5Parseval.zero_vanish
  colBessel := fun _ _ L _ j => (growD_colNorm ⌊L⌋₊ j).le
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  bessel := fun _ _ L _ i => (growD_rowNorm ⌊L⌋₊ i).le
  count := fun _ _ L h => growD_count L h
  defect := fun _ _ L _ => by
    show hs2 (growD ⌊L⌋₊).K ≤ (0 : ℝ) ^ 2 * L ^ 2
    rw [growD_hs2K]; norm_num
  τ := fun _ _ _ => 0
  tail := fun _ _ _ L _ => (hs2_mask_le _ _).trans (growD_hs2K ⌊L⌋₊).le
  Cτ := fun _ _ => 0
  tailRate := SteklovAudit.H5WeakAudit.zeroRate
  ha := fun _ _ _ _ i => by show (0 : ℝ) ≤ ((i.val : ℕ) : ℝ); exact Nat.cast_nonneg _
  hb := fun _ _ _ _ j => by show (0 : ℝ) ≤ ((j.val : ℕ) : ℝ); exact Nat.cast_nonneg _
  c := fun _ _ M => |M| + 1
  lowCount := fun _ _ M L _ => growD_lowCount ⌊L⌋₊ M

/-- **G60.** The count row is exercised on truncations of every size. -/
theorem growWitness_unbounded : ∀ N : ℕ, ∃ L : ℝ, 1 ≤ L ∧ N ≤ growWitness.nA 0 0 L := by
  intro N
  refine ⟨(N : ℝ) + 1, by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)], ?_⟩
  show N ≤ ⌊((N : ℝ) + 1)⌋₊
  exact Nat.le_floor (by linarith)

/-- **G60.** The witness gives (7.29) for its smoothed counts (from `h5b_of_paperScale`). -/
theorem growWitness_target :
    H5bTarget (fun ε γ L => ∑ i, growWitness.P.φ ((growWitness.D ε γ L).a i - L))
      (fun ε γ L => ∑ j, growWitness.P.φ ((growWitness.D ε γ L).b j - L)) :=
  h5b_of_paperScale growWitness

end SteklovAudit.H5EvGrowWitness
