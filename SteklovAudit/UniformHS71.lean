import Mathlib

/-!
# Lemma 7.1' checklist: elementary inequalities (`UniformHS71`)

Concrete real inequalities used in the written proof of the uniform localized
Hilbert–Schmidt bound (7.2'). Items are appended one per run, following ROADMAP.md §A.

This file does NOT prove Lemma 7.1' itself, any Hilbert–Schmidt estimate for the
Dirichlet-to-Neumann operator, or the main theorem (Theorem 1.3 / 11.1). It contains only
scalar inequalities, finite-dimensional matrix trace inequalities and two elementary
integrals of real powers; no analytic
hypotheses are introduced.
-/

namespace SteklovAudit.UniformHS71

/-- A1. For `λ ≥ 1` and `L ≥ 0`: `(λ⁻¹ + L)² ≤ (1 + L)²`. -/
theorem inv_add_sq_le_one_add_sq (lam L : ℝ) (hlam : 1 ≤ lam) (hL : 0 ≤ L) :
    (lam⁻¹ + L) ^ 2 ≤ (1 + L) ^ 2 := by
  have hpos : 0 < lam := by linarith
  have h0 : 0 < lam⁻¹ := inv_pos.mpr hpos
  have hmul : lam⁻¹ * lam = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have h1 : lam⁻¹ ≤ 1 := by nlinarith
  have hsub : 0 ≤ 1 - lam⁻¹ := by linarith
  have hsum : 0 ≤ 1 + lam⁻¹ + 2 * L := by linarith
  have key : (1 + L) ^ 2 - (lam⁻¹ + L) ^ 2 = (1 - lam⁻¹) * (1 + lam⁻¹ + 2 * L) := by ring
  nlinarith [mul_nonneg hsub hsum]

/-- A2. For `λ > 0`: `C (1 + λL)² · λ⁻² = C (λ⁻¹ + L)²`. -/
theorem scaled_sq_mul_inv_sq (C lam L : ℝ) (hlam : 0 < lam) :
    C * (1 + lam * L) ^ 2 * lam⁻¹ ^ 2 = C * (lam⁻¹ + L) ^ 2 := by
  have h : lam ≠ 0 := ne_of_gt hlam
  have e : lam⁻¹ + L = (1 + lam * L) * lam⁻¹ := by
    rw [add_mul, one_mul, mul_comm lam L, mul_assoc, mul_inv_cancel₀ h, mul_one]
  rw [e]
  ring

/-- A2, division form: `C (1 + λL)² / λ² = C (λ⁻¹ + L)²` for `λ > 0`. -/
theorem scaled_sq_div_sq (C lam L : ℝ) (hlam : 0 < lam) :
    C * (1 + lam * L) ^ 2 / lam ^ 2 = C * (lam⁻¹ + L) ^ 2 := by
  rw [div_eq_mul_inv, ← inv_pow]
  exact scaled_sq_mul_inv_sq C lam L hlam

/-- A3. For `λ > 0`: `t / λ ≤ L ↔ t ≤ λ L`. -/
theorem div_le_iff_le_scaled (lam t L : ℝ) (hlam : 0 < lam) :
    t / lam ≤ L ↔ t ≤ lam * L := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hinv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hne
  have e : lam * (t / lam) = t := by
    rw [div_eq_mul_inv, mul_comm t, ← mul_assoc, hinv, one_mul]
  constructor
  · intro h
    calc t = lam * (t / lam) := e.symm
      _ ≤ lam * L := mul_le_mul_of_nonneg_left h hlam.le
  · intro h
    have h2 : lam * (t / lam) ≤ lam * L := by rw [e]; exact h
    first
      | exact le_of_mul_le_mul_left h2 hlam
      | nlinarith

/-- A3, spectral form. Over a finite spectrum `T` (indexed by `s`) and any weights `g`,
the indicator sums agree: `1_[0,L](λ⁻¹T) = 1_[0,λL](T)`. Only the upper cut changes; the
lower cut `0 ≤ ·` is invariant since `λ > 0`. -/
theorem indicator_sum_scaled {ι : Type*} (s : Finset ι) (T g : ι → ℝ) (lam L : ℝ)
    (hlam : 0 < lam) :
    (∑ i ∈ s, if 0 ≤ T i / lam ∧ T i / lam ≤ L then g i else 0) =
      ∑ i ∈ s, if 0 ≤ T i ∧ T i ≤ lam * L then g i else 0 := by
  refine Finset.sum_congr rfl ?_
  intro i _
  have hu := div_le_iff_le_scaled lam (T i) L hlam
  have hl : 0 ≤ T i / lam ↔ 0 ≤ T i := by
    have := div_le_iff_le_scaled lam (T i) 0 hlam
    constructor
    · intro h0
      by_contra hneg
      push_neg at hneg
      have h1 : T i ≤ lam * 0 := by rw [mul_zero]; exact hneg.le
      have h2 : T i / lam ≤ 0 := this.mpr h1
      have h3 : T i / lam = 0 := le_antisymm h2 h0
      have h4 : T i = lam * (T i / lam) := by
        rw [div_eq_mul_inv, mul_comm (T i), ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlam),
          one_mul]
      rw [h3, mul_zero] at h4
      linarith
    · intro h0
      rw [div_eq_mul_inv]
      exact mul_nonneg h0 (inv_nonneg.mpr hlam.le)
  by_cases h : 0 ≤ T i ∧ T i ≤ lam * L
  · rw [if_pos ⟨hl.mpr h.1, hu.mpr h.2⟩, if_pos h]
  · have h' : ¬ (0 ≤ T i / lam ∧ T i / lam ≤ L) := fun h' => h ⟨hl.mp h'.1, hu.mp h'.2⟩
    rw [if_neg h', if_neg h]

/-- A5. Gradient-scaling cancellation: for `λ > 0`, `λ⁻¹ · C · (λ · G) = C · G`. -/
theorem gradient_scaling_cancel (C G lam : ℝ) (hlam : 0 < lam) :
    lam⁻¹ * C * (lam * G) = C * G := by
  have h : lam ≠ 0 := ne_of_gt hlam
  calc lam⁻¹ * C * (lam * G) = (lam⁻¹ * lam) * (C * G) := by ring
    _ = C * G := by rw [inv_mul_cancel₀ h, one_mul]

/-- A5, division form: `C · (λ · G) / λ = C · G` for `λ > 0`. -/
theorem gradient_scaling_div (C G lam : ℝ) (hlam : 0 < lam) :
    C * (lam * G) / lam = C * G := by
  have h : lam ≠ 0 := ne_of_gt hlam
  rw [div_eq_mul_inv]
  calc C * (lam * G) * lam⁻¹ = (lam * lam⁻¹) * (C * G) := by ring
    _ = C * G := by rw [mul_inv_cancel₀ h, one_mul]

/-- A5, inequality form: if a gradient quantity `g` satisfies `g ≤ λ G` (the rescaled
gradient bound, supplied as a hypothesis), then `λ⁻¹ · C · g ≤ C · G` for `C ≥ 0`, `λ > 0`. -/
theorem scaled_gradient_bound (C G g lam : ℝ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hg : g ≤ lam * G) :
    lam⁻¹ * C * g ≤ C * G := by
  have hk : 0 ≤ lam⁻¹ * C := mul_nonneg (inv_nonneg.mpr hlam.le) hC
  calc lam⁻¹ * C * g ≤ lam⁻¹ * C * (lam * G) := mul_le_mul_of_nonneg_left hg hk
    _ = C * G := gradient_scaling_cancel C G lam hlam

/-! ### A6. Localized trace of a projection (finite-dimensional) -/

section A6

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A symmetric idempotent real matrix has nonnegative diagonal:
`P i i = ∑ k, (P i k)²`. -/
theorem proj_diag_nonneg (P : Matrix n n ℝ) (hsym : P.transpose = P) (hidem : P * P = P)
    (i : n) : 0 ≤ P i i := by
  have h : (P * P) i i = ∑ k, P i k * P k i := Matrix.mul_apply
  rw [hidem] at h
  have hs : ∀ k, P k i = P i k := by
    intro k
    have e := congrFun (congrFun hsym i) k
    rw [Matrix.transpose_apply] at e
    exact e
  rw [h]
  exact Finset.sum_nonneg (fun k _ => by rw [hs k]; exact mul_self_nonneg _)

/-- Trace of a diagonal conjugation: `Tr(η P η) = ∑ i, η i ² · P i i`. -/
theorem trace_diagonal_conj (η : n → ℝ) (P : Matrix n n ℝ) :
    Matrix.trace (Matrix.diagonal η * P * Matrix.diagonal η) = ∑ i, η i ^ 2 * P i i := by
  unfold Matrix.trace
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
    | (simp only [Matrix.diag, Matrix.mul_diagonal, Matrix.diagonal_mul]; ring)
    | (simp [Matrix.diag, Matrix.mul_diagonal, Matrix.diagonal_mul]; ring)
    | simp [Matrix.diag, Matrix.mul_diagonal, Matrix.diagonal_mul, sq, mul_comm, mul_left_comm]

/-- A6, spectral coordinates: if `0 ≤ η ≤ 1_F` pointwise and `p ≥ 0`, then
`∑ η i ² p i ≤ ∑ (1_F i)² p i`. -/
theorem weighted_diag_sum_le (F : Finset n) (η p : n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hη0 : ∀ i, 0 ≤ η i) (hη1 : ∀ i, η i ≤ if i ∈ F then 1 else 0) :
    ∑ i, η i ^ 2 * p i ≤ ∑ i, (if i ∈ F then (1 : ℝ) else 0) ^ 2 * p i := by
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h0 := hη0 i
  have h1 := hη1 i
  have hsq : η i ^ 2 ≤ (if i ∈ F then (1 : ℝ) else 0) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right hsq (hp i)

/-- A6. For a symmetric projection matrix `P` and a diagonal cutoff `0 ≤ η ≤ 1_F`,
`Tr(η P η) ≤ Tr(1_F P 1_F)`. -/
theorem trace_proj_cutoff_le (P : Matrix n n ℝ) (hsym : P.transpose = P) (hidem : P * P = P)
    (F : Finset n) (η : n → ℝ) (hη0 : ∀ i, 0 ≤ η i)
    (hη1 : ∀ i, η i ≤ if i ∈ F then 1 else 0) :
    Matrix.trace (Matrix.diagonal η * P * Matrix.diagonal η) ≤
      Matrix.trace (Matrix.diagonal (fun i => if i ∈ F then (1 : ℝ) else 0) * P *
        Matrix.diagonal (fun i => if i ∈ F then (1 : ℝ) else 0)) := by
  rw [trace_diagonal_conj, trace_diagonal_conj]
  exact weighted_diag_sum_le F η (fun i => P i i) (proj_diag_nonneg P hsym hidem) hη0 hη1

end A6

/-! ### A7. Hilbert–Schmidt norm of `X · diag(y)` (finite-dimensional) -/

section A7

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A7, spectral coordinates: if `|y j| ≤ B` for all `j`, then
`∑ᵢⱼ (X i j · y j)² ≤ (∑ᵢⱼ (X i j)²) · B²`. -/
theorem hs2_mul_diag_le (X : ι → κ → ℝ) (y : κ → ℝ) (B : ℝ) (hy : ∀ j, |y j| ≤ B) :
    ∑ i, ∑ j, (X i j * y j) ^ 2 ≤ (∑ i, ∑ j, X i j ^ 2) * B ^ 2 := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hB : y j ^ 2 ≤ B ^ 2 := by
    have h1 := mul_nonneg (sub_nonneg.mpr (hy j)) (abs_nonneg (y j))
    nlinarith [sq_abs (y j), sq_nonneg (B - |y j|)]
  calc (X i j * y j) ^ 2 = X i j ^ 2 * y j ^ 2 := by ring
    _ ≤ X i j ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hB (sq_nonneg _)

/-- A7, matrix form: `‖X · diagonal y‖²_F ≤ ‖X‖²_F · B²` when `|y j| ≤ B`
(for diagonal `Y`, the operator norm is `sup |y j|`, bounded here by `B`). -/
theorem frobenius_sq_mul_diagonal_le [DecidableEq κ] (X : Matrix ι κ ℝ) (y : κ → ℝ) (B : ℝ)
    (hy : ∀ j, |y j| ≤ B) :
    ∑ i, ∑ j, (X * Matrix.diagonal y) i j ^ 2 ≤ (∑ i, ∑ j, X i j ^ 2) * B ^ 2 := by
  simp only [Matrix.mul_diagonal]
  exact hs2_mul_diag_le X y B hy

/-- A7, unsquared form: `‖X · diag(y)‖_F ≤ ‖X‖_F · B` for `B ≥ 0` and `|y j| ≤ B`. -/
theorem frobenius_mul_diag_le (X : ι → κ → ℝ) (y : κ → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hy : ∀ j, |y j| ≤ B) :
    Real.sqrt (∑ i, ∑ j, (X i j * y j) ^ 2) ≤ Real.sqrt (∑ i, ∑ j, X i j ^ 2) * B := by
  have h := hs2_mul_diag_le X y B hy
  have hS : 0 ≤ ∑ i, ∑ j, X i j ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (X i j)))
  have hmono : Real.sqrt (∑ i, ∑ j, (X i j * y j) ^ 2) ≤
      Real.sqrt ((∑ i, ∑ j, X i j ^ 2) * B ^ 2) := by
    first | exact Real.sqrt_le_sqrt h | gcongr
  calc Real.sqrt (∑ i, ∑ j, (X i j * y j) ^ 2)
      ≤ Real.sqrt ((∑ i, ∑ j, X i j ^ 2) * B ^ 2) := hmono
    _ = Real.sqrt (∑ i, ∑ j, X i j ^ 2) * Real.sqrt (B ^ 2) := Real.sqrt_mul hS _
    _ = Real.sqrt (∑ i, ∑ j, X i j ^ 2) * B := by rw [Real.sqrt_sq hB0]

end A7

/-! ### A8. Two elementary interval integrals -/

section A8

/-- A8. For `β > 1/2`: `∫₀¹ s^(2β−2) ds = 1/(2β−1)` (real power). -/
theorem integral_rpow_two_beta_sub_two (β : ℝ) (hβ : 1 / 2 < β) :
    ∫ s in (0 : ℝ)..1, s ^ (2 * β - 2) = 1 / (2 * β - 1) := by
  have hr : (-1 : ℝ) < 2 * β - 2 := by linarith
  have h1 : 2 * β - 2 + 1 = 2 * β - 1 := by ring
  have hne : 2 * β - 1 ≠ 0 := by
    have : 0 < 2 * β - 1 := by linarith
    exact ne_of_gt this
  first
    | rw [integral_rpow (Or.inl hr)]
    | rw [intervalIntegral.integral_rpow (Or.inl hr)]
  rw [h1]
  first
    | (rw [Real.one_rpow, Real.zero_rpow hne, sub_zero])
    | simp [Real.zero_rpow hne]

/-- A8. For `μ > 0`: `∫₀¹ s^(2μ−1) ds = 1/(2μ)` (real power). -/
theorem integral_rpow_two_mu_sub_one (μ : ℝ) (hμ : 0 < μ) :
    ∫ s in (0 : ℝ)..1, s ^ (2 * μ - 1) = 1 / (2 * μ) := by
  have hr : (-1 : ℝ) < 2 * μ - 1 := by linarith
  have h1 : 2 * μ - 1 + 1 = 2 * μ := by ring
  have hne : 2 * μ ≠ 0 := by
    have : 0 < 2 * μ := by linarith
    exact ne_of_gt this
  first
    | rw [integral_rpow (Or.inl hr)]
    | rw [intervalIntegral.integral_rpow (Or.inl hr)]
  rw [h1]
  first
    | (rw [Real.one_rpow, Real.zero_rpow hne, sub_zero])
    | simp [Real.zero_rpow hne]

end A8

/-! ### A9. The dyadic sum `∑_{j≥1} 2^(−4j) = 1/15` -/

section A9

/-- A9, closed form of the finite partial sums:
`∑_{j<n} (1/16)^(j+1) = (1 − (1/16)^n)/15`. -/
theorem quarter_sq_partial_sum_eq (n : ℕ) :
    ∑ j ∈ Finset.range n, ((1 : ℝ) / 16) ^ (j + 1) = (1 - ((1 : ℝ) / 16) ^ n) / 15 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- A9, finite form: every partial sum of `∑_{j≥1} 2^(−4j)` is at most `1/15`. -/
theorem quarter_sq_partial_sum_le (n : ℕ) :
    ∑ j ∈ Finset.range n, ((1 : ℝ) / 16) ^ (j + 1) ≤ 1 / 15 := by
  rw [quarter_sq_partial_sum_eq]
  have h : 0 ≤ ((1 : ℝ) / 16) ^ n := by positivity
  linarith

/-- A9, infinite form: `∑'_{j≥0} (1/16)^(j+1) = 1/15`. -/
theorem tsum_sixteenth_pow_succ :
    ∑' j : ℕ, ((1 : ℝ) / 16) ^ (j + 1) = 1 / 15 := by
  have hg : ∑' j : ℕ, ((1 : ℝ) / 16) ^ j = (1 - (1 : ℝ) / 16)⁻¹ := by
    first
      | exact tsum_geometric_of_lt_one (by norm_num) (by norm_num)
      | exact (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).tsum_eq
  rw [show (∑' j : ℕ, ((1 : ℝ) / 16) ^ (j + 1)) = ∑' j : ℕ, ((1 : ℝ) / 16) ^ j * (1 / 16) from
    tsum_congr (fun j => by ring)]
  rw [tsum_mul_right, hg]
  norm_num

/-- A9, as written in the paper: `∑_{j≥1} 2^(−4j) = 1/15`, indexing `j + 1` for `j ≥ 0`. -/
theorem tsum_two_pow_neg_four :
    ∑' j : ℕ, ((2 : ℝ)⁻¹) ^ (4 * (j + 1)) = 1 / 15 := by
  rw [show (∑' j : ℕ, ((2 : ℝ)⁻¹) ^ (4 * (j + 1))) = ∑' j : ℕ, ((1 : ℝ) / 16) ^ (j + 1) from
    tsum_congr (fun j => by
      rw [pow_mul]
      congr 1
      norm_num)]
  exact tsum_sixteenth_pow_succ

end A9

/-! ### A10. Pointwise criterion for the Hilbert–Schmidt norm (finite-dimensional) -/

section A10

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A10, one row: if `|∑ₖ r k · r k| ≤ c · ‖r‖` (testing the row against itself), then
`∑ₖ (r k)² ≤ c²`. -/
theorem row_sq_le_of_self_test (r : κ → ℝ) (c : ℝ)
    (h : |∑ k, r k * r k| ≤ c * Real.sqrt (∑ k, r k ^ 2)) :
    ∑ k, r k ^ 2 ≤ c ^ 2 := by
  have hS0 : 0 ≤ ∑ k, r k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg (r k))
  have hrr : ∑ k, r k * r k = ∑ k, r k ^ 2 := Finset.sum_congr rfl (fun k _ => by ring)
  rw [hrr, abs_of_nonneg hS0] at h
  have hsq : Real.sqrt (∑ k, r k ^ 2) ^ 2 = ∑ k, r k ^ 2 := Real.sq_sqrt hS0
  have hq0 : 0 ≤ Real.sqrt (∑ k, r k ^ 2) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hq0 with hq | hq
  · rw [← hq] at hsq
    nlinarith [sq_nonneg c]
  · have hqc : Real.sqrt (∑ k, r k ^ 2) ≤ c := by
      by_contra hlt
      push_neg at hlt
      nlinarith [mul_pos hq (sub_pos.mpr hlt)]
    nlinarith [mul_self_le_mul_self hq0 hqc]

/-- A10. Finite-dimensional pointwise criterion: if `|∑ₖ T i k · f k| ≤ w i · ‖f‖` for every
`f` and every row `i` (with `‖f‖ = √(∑ₖ (f k)²)`), then `∑ᵢₖ (T i k)² ≤ ∑ᵢ (w i)²`. -/
theorem hs2_le_of_pointwise (T : ι → κ → ℝ) (w : ι → ℝ)
    (h : ∀ i (f : κ → ℝ), |∑ k, T i k * f k| ≤ w i * Real.sqrt (∑ k, f k ^ 2)) :
    ∑ i, ∑ k, T i k ^ 2 ≤ ∑ i, w i ^ 2 :=
  Finset.sum_le_sum (fun i _ => row_sq_le_of_self_test (T i) (w i) (h i (T i)))

/-- A10, unsquared form: `‖T‖_HS ≤ √(∑ᵢ (w i)²)` under the same pointwise hypothesis. -/
theorem hs_le_of_pointwise (T : ι → κ → ℝ) (w : ι → ℝ)
    (h : ∀ i (f : κ → ℝ), |∑ k, T i k * f k| ≤ w i * Real.sqrt (∑ k, f k ^ 2)) :
    Real.sqrt (∑ i, ∑ k, T i k ^ 2) ≤ Real.sqrt (∑ i, w i ^ 2) := by
  have h2 := hs2_le_of_pointwise T w h
  first | exact Real.sqrt_le_sqrt h2 | gcongr

end A10

end SteklovAudit.UniformHS71
