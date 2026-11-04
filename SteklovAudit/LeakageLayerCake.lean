import Mathlib
import SteklovAudit.AbstractTransfer

/-!
# R2: spectral leakage past a gap and the layer-cake identity (R42.1(ii)–(iii))

Spectral coordinates of `SteklovAudit.AbstractTransfer`: eigenvalues `a i` of `A`, `b j` of `B`,
identification coefficients `J i j`, defect `K i j = (a i - b j) J i j`.

* `leakage_gap` (R42.1(ii)): for `s > 0`,
  `Σ_{a_i ≤ L} Σ_{b_j ≥ L+s} J_ij² ≤ s⁻² Σ_{a_i ≤ L} Σ_j K_ij²`
  (the gap step of `window_gap_leakage`, followed by enlarging the inner sum to all `j`).
* `layer_cake_sq` (R42.1(iii), pointwise): `∫₀^∞ 2t · 1[t < x] dt = max(x, 0)²` for real `x`.
* `layer_cake_sum` (R42.1(iii), summed): with
  `H(t) = Σ_{a_i ≤ L} Σ_{b_j - L > t} J_ij²`,
  `∫₀^∞ 2t H(t) dt = Σ_{a_i ≤ L} Σ_j (b_j - L)₊² J_ij²`.

What this module does NOT prove: anything about the tetrahedral Steklov operator. The spectral
data are arbitrary finite arrays; no Dirichlet-to-Neumann operator, identification or defect bound
is constructed, and the passage to infinite dimensions is not formalized. None of `[H1]`–`[H6]`
and not the main theorem.
-/

namespace SteklovAudit.LeakageLayerCake

open Finset MeasureTheory SteklovAudit.AbstractTransfer

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- R42.1(ii): leakage of the low `A`-window past the gap `s` into the high `B`-window. -/
theorem leakage_gap (D : Data ι κ) (L s : ℝ) (hs : 0 < s) :
    ∑ i ∈ univ.filter (fun i => D.a i ≤ L), ∑ j ∈ univ.filter (fun j => L + s ≤ D.b j),
        D.J i j ^ 2
      ≤ (∑ i ∈ univ.filter (fun i => D.a i ≤ L), ∑ j, D.K i j ^ 2) / s ^ 2 := by
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  rw [le_div_iff₀ hs2, sum_mul]
  apply sum_le_sum
  intro i hi
  have ha : D.a i ≤ L := (mem_filter.mp hi).2
  rw [sum_mul]
  calc ∑ j ∈ univ.filter (fun j => L + s ≤ D.b j), D.J i j ^ 2 * s ^ 2
      ≤ ∑ j ∈ univ.filter (fun j => L + s ≤ D.b j), D.K i j ^ 2 := by
        apply sum_le_sum
        intro j hj
        have hb : L + s ≤ D.b j := (mem_filter.mp hj).2
        have h1 : s ≤ D.b j - D.a i := by linarith
        have hsq : s ^ 2 ≤ (D.a i - D.b j) ^ 2 := by nlinarith
        unfold Data.K
        rw [mul_pow, mul_comm (D.J i j ^ 2)]
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ ≤ ∑ j, D.K i j ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => sq_nonneg _)

/-- Pointwise layer cake: `∫₀^∞ 2t · 1[t < x] dt = max(x, 0)²`. -/
theorem layer_cake_sq (x : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), (Set.Iio x).indicator (fun t => 2 * t) t = (max x 0) ^ 2 := by
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  first
    | rw [Set.Iio_inter_Ioi]
    | rw [Set.inter_comm, Set.Ioi_inter_Iio]
  by_cases hx : x ≤ 0
  · rw [max_eq_right hx]
    first
      | (rw [Set.Ioo_eq_empty_of_le hx]; simp)
      | simp [Set.Ioo_eq_empty_of_le hx]
      | simp [hx]
  · push_neg at hx
    rw [max_eq_left hx.le, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hx.le]
    first
      | (rw [intervalIntegral.integral_const_mul, integral_id]; ring)
      | (simp [integral_id]; ring)
      | simp

/-- The layer-cake integrand is integrable on `(0, ∞)`. -/
theorem indicator_integrable (x : ℝ) :
    Integrable ((Set.Iio x).indicator (fun t : ℝ => 2 * t)) (volume.restrict (Set.Ioi 0)) := by
  rw [integrable_indicator_iff measurableSet_Iio]
  unfold IntegrableOn
  rw [Measure.restrict_restrict measurableSet_Iio]
  have hc : Continuous (fun t : ℝ => 2 * t) := by fun_prop
  exact (hc.integrableOn_Icc (a := (0 : ℝ)) (b := max x 0)).mono_set
    (fun t ht => ⟨le_of_lt ht.2, (le_of_lt ht.1).trans (le_max_left _ _)⟩)

/-- R42.1(iii), summed: `∫₀^∞ 2t H(t) dt = Σ_{a_i ≤ L} Σ_j (b_j - L)₊² J_ij²`. -/
theorem layer_cake_sum (D : Data ι κ) (L : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), 2 * t * ∑ i ∈ univ.filter (fun i => D.a i ≤ L),
        ∑ j ∈ univ.filter (fun j => t < D.b j - L), D.J i j ^ 2
      = ∑ i ∈ univ.filter (fun i => D.a i ≤ L), ∑ j, (max (D.b j - L) 0) ^ 2 * D.J i j ^ 2 := by
  have hpt : ∀ t : ℝ, 2 * t * ∑ i ∈ univ.filter (fun i => D.a i ≤ L),
        ∑ j ∈ univ.filter (fun j => t < D.b j - L), D.J i j ^ 2
      = ∑ i ∈ univ.filter (fun i => D.a i ≤ L),
        ∑ j, D.J i j ^ 2 * (Set.Iio (D.b j - L)).indicator (fun t => 2 * t) t := by
    intro t
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro j _
    by_cases h : t < D.b j - L
    · simp only [Set.indicator, Set.mem_Iio, if_pos h]
      try ring
    · simp only [Set.indicator, Set.mem_Iio, if_neg h]
      try ring
  have hfun : (fun t : ℝ => 2 * t * ∑ i ∈ univ.filter (fun i => D.a i ≤ L),
        ∑ j ∈ univ.filter (fun j => t < D.b j - L), D.J i j ^ 2)
      = (fun t : ℝ => ∑ i ∈ univ.filter (fun i => D.a i ≤ L),
        ∑ j, D.J i j ^ 2 * (Set.Iio (D.b j - L)).indicator (fun t => 2 * t) t) := funext hpt
  have hint : ∀ c x : ℝ, Integrable (fun t => c * (Set.Iio x).indicator (fun t : ℝ => 2 * t) t)
      (volume.restrict (Set.Ioi 0)) := fun c x => (indicator_integrable x).const_mul c
  first
    | rw [hfun]
    | simp only [hpt]
  rw [integral_finset_sum]
  · apply sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · apply sum_congr rfl
      intro j _
      rw [integral_const_mul, layer_cake_sq]
      ring
    · intro j _
      exact hint _ _
  · intro i _
    exact integrable_finset_sum _ (fun j _ => hint _ _)

end SteklovAudit.LeakageLayerCake
