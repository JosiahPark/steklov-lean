import Mathlib
import SteklovAudit.H5EvPaperScale
import SteklovAudit.H5ColNormEvAudit

/-!
# G61: the low-energy count row is independent of the Weyl-type count row

Roadmap item G61. `flatD n` has `n` true and `n` model eigenvalues all equal to `0`, with identity
coupling. With `n = ⌊L⌋₊` it satisfies row and column normalization (`flatD_rowNorm`,
`flatD_colNorm`), the paper-scale count row with `Cm = 1` (`flatD_count`), a vanishing defect
(`flatD_K`, `flatD_hs2K`, so the defect row holds with `Ck = 0` and the tail row with `τ = 0`), and
nonnegativity (`flatD_ha`, `flatD_hb`). Yet `flatD_not_lowCount`: no constant bounds the number of
eigenvalues `≤ 0` uniformly in `L`. So the `lowCount` field of `H5bPaperScaleInputs` is an
independent input, not a consequence of the count row.

What this file does NOT prove: `flatD` is a test family, not a model of the Steklov spectrum; no row
(count, defect, tail, low-count, normalization) is proved for any actual coupling or for the Steklov
operator of the tetrahedron; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…]
input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5EvLowCountIndep

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5EvPaperScale

/-- All eigenvalues `0` on both sides, identity coupling. -/
def flatD (n : ℕ) : Data (Fin n) (Fin n) where
  a := fun _ => (0 : ℝ)
  b := fun _ => (0 : ℝ)
  J := fun i j => if i = j then (1 : ℝ) else 0

theorem flatD_rowNorm (n : ℕ) (i : Fin n) : ∑ j, (flatD n).J i j ^ 2 = 1 := by
  have h : ∀ j : Fin n, (flatD n).J i j ^ 2 = if i = j then 1 else 0 := by
    intro j
    show (if i = j then (1 : ℝ) else 0) ^ 2 = _
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  first | simp | exact (Finset.sum_ite_eq _ _ _).trans (if_pos (Finset.mem_univ _))

theorem flatD_colNorm (n : ℕ) (j : Fin n) : ∑ i, (flatD n).J i j ^ 2 = 1 := by
  have h : ∀ i : Fin n, (flatD n).J i j ^ 2 = if i = j then 1 else 0 := by
    intro i
    show (if i = j then (1 : ℝ) else 0) ^ 2 = _
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  first | simp | exact (Finset.sum_ite_eq' _ _ _).trans (if_pos (Finset.mem_univ _))

theorem flatD_K (n : ℕ) (i j : Fin n) : (flatD n).K i j = 0 := by
  show ((0 : ℝ) - 0) * (if i = j then (1 : ℝ) else 0) = 0
  first | ring | simp

theorem flatD_hs2K (n : ℕ) : hs2 (flatD n).K = 0 := by
  first | simp [hs2, flatD_K] | (unfold hs2; simp [flatD_K])

theorem flatD_count (L : ℝ) (h : 1 ≤ L) : (Fintype.card (Fin ⌊L⌋₊) : ℝ) ≤ 1 * L ^ 2 := by
  rw [Fintype.card_fin, one_mul]
  have h1 : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ L)]

theorem flatD_ha (n : ℕ) (i : Fin n) : 0 ≤ (flatD n).a i := le_refl (0 : ℝ)

theorem flatD_hb (n : ℕ) (j : Fin n) : 0 ≤ (flatD n).b j := le_refl (0 : ℝ)

/-- Every eigenvalue of `flatD n` lies at or below `0`. -/
theorem flatD_filter_univ (n : ℕ) :
    (Finset.univ.filter fun i => (flatD n).a i ≤ 0) = Finset.univ := by
  first
    | exact Finset.filter_true_of_mem (fun i _ => (le_refl (0 : ℝ)))
    | (ext i; simp [flatD])

/-- **G61.** No constant bounds the low-energy count of `flatD ⌊L⌋₊` uniformly in `L`, although the
count, defect, tail and normalization rows all hold for it. -/
theorem flatD_not_lowCount : ¬ ∃ c : ℝ, ∀ L : ℝ, 1 ≤ L →
    ((Finset.univ.filter fun i => (flatD ⌊L⌋₊).a i ≤ 0).card : ℝ) ≤ c := by
  rintro ⟨c, hc⟩
  have hL : (1 : ℝ) ≤ ((⌈c⌉₊ + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌈c⌉₊ + 2 by omega)
  have h := hc ((⌈c⌉₊ + 2 : ℕ) : ℝ) hL
  rw [flatD_filter_univ, Finset.card_univ, Fintype.card_fin] at h
  have hf : ⌊((⌈c⌉₊ + 2 : ℕ) : ℝ)⌋₊ = ⌈c⌉₊ + 2 := by
    first | exact Nat.floor_natCast _ | exact Nat.floor_coe _ | simp
  rw [hf] at h
  have hc' : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
  push_cast at h
  linarith

end SteklovAudit.H5EvLowCountIndep
