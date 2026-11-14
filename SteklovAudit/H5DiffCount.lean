import Mathlib
import SteklovAudit.H5CutoffSides
import SteklovAudit.H5Completeness

/-!
# G34: the cutoff row from one smoothed-count difference row

Roadmap item G34. Over arbitrary finite index types `ι`, `κ`, with values `f : ι → ℝ`, `g : κ → ℝ`
and a coupling `J : ι → κ → ℝ`:

* `diff_of_counts`: two one-spectrum count bounds `|X1 - S1| ≤ e1`, `|X2 - S2| ≤ e2` give the
  difference bound `|(X1 - X2) - (S1 - S2)| ≤ e1 + e2` (so the pair of count rows implies the single
  difference row).
* `cutoff_of_diff_count`: a single difference row `|X - (∑ f - ∑ g)| ≤ e`, sup bounds `|f|, |g| ≤ Φ`,
  row and column Bessel bounds and missing-mass bounds `m1`, `m2` give the cutoff inequality
  `|X - ∑ i, ∑ j, (f i - g j) * J i j ^ 2| ≤ e + Φ * m1 + Φ * m2`.

What this file does NOT prove: no count, difference, missing-mass or Bessel row is proved for the
Steklov operator of the tetrahedron or for any actual coupling matrix; no Dirichlet-to-Neumann operator
is constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
This is pure finite-sum algebra.
-/

namespace SteklovAudit.H5DiffCount

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G34.** Two count bounds give a bound on the difference. -/
theorem diff_of_counts (X1 X2 S1 S2 e1 e2 : ℝ)
    (h1 : |X1 - S1| ≤ e1) (h2 : |X2 - S2| ≤ e2) :
    |(X1 - X2) - (S1 - S2)| ≤ e1 + e2 := by
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

/-- Helper: the completeness defect of a Bessel-weighted sum is at most `Φ * m`. -/
theorem defect_abs_le_mass (f w : ι → ℝ) (Φ m : ℝ) (hΦ : 0 ≤ Φ) (hf : ∀ i, |f i| ≤ Φ)
    (hw : ∀ i, w i ≤ 1) (hm : ∑ i, (1 - w i) ≤ m) :
    |∑ i, f i * (1 - w i)| ≤ Φ * m := by
  have h1 := SteklovAudit.H5Completeness.defect_abs_le f w hw
  have h2 := SteklovAudit.H5Completeness.defect_le_sup f w Φ hf hw
  have h3 : Φ * ∑ i, (1 - w i) ≤ Φ * m := mul_le_mul_of_nonneg_left hm hΦ
  linarith

/-- **G34.** One smoothed-count difference row, sup bounds, Bessel bounds and missing-mass
bounds give the cutoff inequality. -/
theorem cutoff_of_diff_count (f : ι → ℝ) (g : κ → ℝ) (J : ι → κ → ℝ) (X e Φ m1 m2 : ℝ)
    (hdiff : |X - (∑ i, f i - ∑ j, g j)| ≤ e)
    (hf : ∀ i, |f i| ≤ Φ) (hg : ∀ j, |g j| ≤ Φ)
    (hrow : ∀ i, ∑ j, J i j ^ 2 ≤ 1) (hcol : ∀ j, ∑ i, J i j ^ 2 ≤ 1)
    (hm1 : ∑ i, (1 - ∑ j, J i j ^ 2) ≤ m1) (hm2 : ∑ j, (1 - ∑ i, J i j ^ 2) ≤ m2)
    (hΦ : 0 ≤ Φ) :
    |X - ∑ i, ∑ j, (f i - g j) * J i j ^ 2| ≤ e + Φ * m1 + Φ * m2 := by
  have hsplit : ∑ i, ∑ j, (f i - g j) * J i j ^ 2
      = ∑ i, f i * (∑ j, J i j ^ 2) - ∑ j, g j * (∑ i, J i j ^ 2) :=
    SteklovAudit.H5CutoffSides.double_sum_split f g J
  have hwf : ∑ i, f i * (∑ j, J i j ^ 2)
      = ∑ i, f i - ∑ i, f i * (1 - ∑ j, J i j ^ 2) :=
    SteklovAudit.H5Completeness.weighted_sum_split f (fun i => ∑ j, J i j ^ 2)
  have hwg : ∑ j, g j * (∑ i, J i j ^ 2)
      = ∑ j, g j - ∑ j, g j * (1 - ∑ i, J i j ^ 2) :=
    SteklovAudit.H5Completeness.weighted_sum_split g (fun j => ∑ i, J i j ^ 2)
  rw [hsplit, hwf, hwg]
  have hD1 : |∑ i, f i * (1 - ∑ j, J i j ^ 2)| ≤ Φ * m1 :=
    defect_abs_le_mass f (fun i => ∑ j, J i j ^ 2) Φ m1 hΦ hf hrow hm1
  have hD2 : |∑ j, g j * (1 - ∑ i, J i j ^ 2)| ≤ Φ * m2 :=
    defect_abs_le_mass g (fun j => ∑ i, J i j ^ 2) Φ m2 hΦ hg hcol hm2
  obtain ⟨hdl, hdr⟩ := abs_le.mp hdiff
  obtain ⟨h1l, h1r⟩ := abs_le.mp hD1
  obtain ⟨h2l, h2r⟩ := abs_le.mp hD2
  rw [abs_le]
  constructor <;> linarith

/-- Non-vacuity: on `Fin 1 × Fin 1` with `f = 1`, `g = 0`, `J = 0`, `X = 0`, the hypotheses of
`cutoff_of_diff_count` hold with `e = 1`, `Φ = 1`, `m1 = m2 = 1`, and the double sum is `0`. -/
theorem cutoff_of_diff_count_nonvacuous :
    |(0 : ℝ) - (∑ _i : Fin 1, (1 : ℝ) - ∑ _j : Fin 1, (0 : ℝ))| ≤ 1 ∧
    |(0 : ℝ) - ∑ _i : Fin 1, ∑ _j : Fin 1, ((1 : ℝ) - 0) * (0 : ℝ) ^ 2| ≤ 1 + 1 * 1 + 1 * 1 := by
  constructor
  · norm_num [Fin.sum_univ_one]
  · norm_num [Fin.sum_univ_one]

end SteklovAudit.H5DiffCount
