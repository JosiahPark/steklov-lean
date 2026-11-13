import Mathlib

/-!
# G22: weighted-sum reduction for the H5b side rows

Roadmap item G22. Over an arbitrary finite index type `ι`, with values `f : ι → ℝ` and weights
`w : ι → ℝ` (for the H5b side rows: `f i = φ (a i - L)` and `w i = ∑ j, J i j ^ 2`, a row or column
mass of the coupling `J`):

* `weighted_sum_split`: `∑ f i * w i = ∑ f i - ∑ f i * (1 - w i)`.
* `defect_abs_le`: if every `w i ≤ 1` (Bessel), `|∑ f i * (1 - w i)| ≤ ∑ |f i| * (1 - w i)`.
* `side_of_count_and_defect`: a one-spectrum count bound `|E - ∑ f i| ≤ e` plus a completeness
  defect bound `∑ |f i| * (1 - w i) ≤ k` give the weighted side bound `|E - ∑ f i * w i| ≤ e + k`.
* `defect_le_sup`: with `|f i| ≤ Φ`, the defect is at most `Φ * ∑ (1 - w i)`.
* `side_of_count_and_sup`: the combination of the last two.
* `side_of_count_and_defect_nonvacuous`: the hypotheses are jointly satisfiable with `w ≠ 1`.

What this file does NOT prove: no count bound, completeness bound or Bessel bound is proved for the
Steklov operator of the tetrahedron or for any actual coupling matrix; no Dirichlet-to-Neumann operator
is constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
This is pure finite-sum algebra.
-/

namespace SteklovAudit.H5Completeness

open Finset

variable {ι : Type*} [Fintype ι]

/-- Split a weighted sum into the unweighted sum minus the defect. -/
theorem weighted_sum_split (f w : ι → ℝ) :
    ∑ i, f i * w i = ∑ i, f i - ∑ i, f i * (1 - w i) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- With Bessel weights `w i ≤ 1`, the defect is bounded by its absolute-value form. -/
theorem defect_abs_le (f w : ι → ℝ) (hw : ∀ i, w i ≤ 1) :
    |∑ i, f i * (1 - w i)| ≤ ∑ i, |f i| * (1 - w i) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hw i))]

/-- Count row + completeness defect row ⇒ weighted side row. -/
theorem side_of_count_and_defect (f w : ι → ℝ) (E e k : ℝ)
    (hcount : |E - ∑ i, f i| ≤ e) (hdef : ∑ i, |f i| * (1 - w i) ≤ k)
    (hw : ∀ i, w i ≤ 1) :
    |E - ∑ i, f i * w i| ≤ e + k := by
  rw [weighted_sum_split]
  have h1 := defect_abs_le f w hw
  have hrw : E - (∑ i, f i - ∑ i, f i * (1 - w i))
      = (E - ∑ i, f i) + ∑ i, f i * (1 - w i) := by ring
  rw [hrw]
  have h2 : |(E - ∑ i, f i) + ∑ i, f i * (1 - w i)|
      ≤ |E - ∑ i, f i| + |∑ i, f i * (1 - w i)| := abs_add_le _ _
  linarith

/-- Crude form of the defect: sup of `|f|` times the total missing mass. -/
theorem defect_le_sup (f w : ι → ℝ) (Φ : ℝ) (hf : ∀ i, |f i| ≤ Φ) (hw : ∀ i, w i ≤ 1) :
    ∑ i, |f i| * (1 - w i) ≤ Φ * ∑ i, (1 - w i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hf i) (sub_nonneg.mpr (hw i))

/-- Count row + crude completeness (sup times missing mass) ⇒ weighted side row. -/
theorem side_of_count_and_sup (f w : ι → ℝ) (E e Φ k : ℝ)
    (hcount : |E - ∑ i, f i| ≤ e) (hf : ∀ i, |f i| ≤ Φ) (hw : ∀ i, w i ≤ 1)
    (hmass : Φ * ∑ i, (1 - w i) ≤ k) :
    |E - ∑ i, f i * w i| ≤ e + k :=
  side_of_count_and_defect f w E e k hcount ((defect_le_sup f w Φ hf hw).trans hmass) hw

/-- Non-vacuity: on `Fin 1` with `f = 1`, `w = 1/2`, `E = 1`, the hypotheses of
`side_of_count_and_defect` hold with `e = 0`, `k = 1/2`, and the conclusion is sharp. -/
theorem side_of_count_and_defect_nonvacuous :
    |(1 : ℝ) - ∑ _i : Fin 1, (1 : ℝ)| ≤ 0 ∧
    ∑ _i : Fin 1, |(1 : ℝ)| * (1 - 1 / 2) ≤ 1 / 2 ∧
    (∀ _i : Fin 1, (1 / 2 : ℝ) ≤ 1) ∧
    |(1 : ℝ) - ∑ _i : Fin 1, (1 : ℝ) * (1 / 2)| = 0 + 1 / 2 := by
  refine ⟨?_, ?_, fun _ => by norm_num, ?_⟩
  · simp only [Fin.sum_univ_one, sub_self, abs_zero, le_refl]
  · simp only [Fin.sum_univ_one, abs_one]
    norm_num
  · simp only [Fin.sum_univ_one]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 - 1 * (1 / 2) by norm_num)]
    norm_num

end SteklovAudit.H5Completeness
