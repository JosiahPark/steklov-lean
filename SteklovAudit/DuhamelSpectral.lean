import Mathlib

/-!
# Hilbert–Schmidt Duhamel bound in spectral coordinates (roadmap item G129)

In spectral coordinates an overlap matrix `J i j` between eigenvectors with eigenvalues `lam i`, `mu j`
propagates to `J i j · (e^{−it·lam i} − e^{−it·mu j})`. `duhamel_entry_le` bounds one phase difference by
`|t| · |lam i − mu j|`, and `duhamel_hs_le` sums it: the squared HS norm of the propagated difference is at
most `t²` times the squared HS norm of the commutator defect `J i j · (lam i − mu j)`. The factor `|t|`
is kept, so that the `1/t` of the cumulative Fourier integral (G130) cancels.

What this file does NOT prove: anything about unbounded operators, domains, or the Steklov / DtN
operator; the bound `ε(h)` on the commutator defect (the HS defect row of the F table); (7.29), H5, or
Theorem 1.3 / 11.1. Everything is finite-dimensional.
-/

namespace SteklovAudit.DuhamelSpectral

open Complex

/-- `‖e^{iθ} − 1‖ ≤ |θ|` for real `θ`. -/
theorem exp_sub_one_le (θ : ℝ) : ‖exp ((θ : ℂ) * I) - 1‖ ≤ |θ| := by
  have hre : (exp ((θ : ℂ) * I) - 1).re = Real.cos θ - 1 := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (exp ((θ : ℂ) * I) - 1).im = Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_im]
  have hn : ‖exp ((θ : ℂ) * I) - 1‖ ^ 2 = (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 := by
    first
      | (rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring)
      | (rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]; ring)
      | (rw [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply, hre, him]; ring)
  have hcos : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  have hpy := Real.sin_sq_add_cos_sq θ
  have h2 : ‖exp ((θ : ℂ) * I) - 1‖ ^ 2 ≤ |θ| ^ 2 := by
    rw [sq_abs, hn]
    nlinarith
  have h0 : 0 ≤ ‖exp ((θ : ℂ) * I) - 1‖ := norm_nonneg _
  have h1 : 0 ≤ |θ| := abs_nonneg θ
  nlinarith

/-- **G129.** One phase difference is at most `|t| · |a − b|`. -/
theorem duhamel_entry_le (t a b : ℝ) :
    ‖exp (((-(t * a) : ℝ) : ℂ) * I) - exp (((-(t * b) : ℝ) : ℂ) * I)‖ ≤ |t| * |a - b| := by
  have hA : (((-(t * a) : ℝ) : ℂ) * I) = ((-(t * b) : ℝ) : ℂ) * I + ((t * (b - a) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have e : exp (((-(t * a) : ℝ) : ℂ) * I) - exp (((-(t * b) : ℝ) : ℂ) * I) =
      exp (((-(t * b) : ℝ) : ℂ) * I) * (exp (((t * (b - a) : ℝ) : ℂ) * I) - 1) := by
    rw [hA, Complex.exp_add]
    ring
  have hu : ‖exp (((-(t * b) : ℝ) : ℂ) * I)‖ = 1 := by
    first
      | exact Complex.norm_exp_ofReal_mul_I _
      | (rw [Complex.norm_eq_abs]; exact Complex.abs_exp_ofReal_mul_I _)
  rw [e, norm_mul, hu, one_mul]
  calc ‖exp (((t * (b - a) : ℝ) : ℂ) * I) - 1‖ ≤ |t * (b - a)| := exp_sub_one_le _
    _ = |t| * |a - b| := by rw [abs_mul, abs_sub_comm]

/-- **G129.** Summed over a finite overlap matrix: squared HS norm of the propagated difference
`≤ t²` × squared HS norm of the commutator defect. -/
theorem duhamel_hs_le {m n : ℕ} (J : Fin m → Fin n → ℂ) (lam : Fin m → ℝ) (mu : Fin n → ℝ) (t : ℝ) :
    ∑ i, ∑ j, ‖J i j‖ ^ 2 *
        ‖exp (((-(t * lam i) : ℝ) : ℂ) * I) - exp (((-(t * mu j) : ℝ) : ℂ) * I)‖ ^ 2 ≤
      t ^ 2 * ∑ i, ∑ j, ‖J i j‖ ^ 2 * (lam i - mu j) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := duhamel_entry_le t (lam i) (mu j)
  have h0 : 0 ≤ ‖exp (((-(t * lam i) : ℝ) : ℂ) * I) - exp (((-(t * mu j) : ℝ) : ℂ) * I)‖ :=
    norm_nonneg _
  have hsq : ‖exp (((-(t * lam i) : ℝ) : ℂ) * I) - exp (((-(t * mu j) : ℝ) : ℂ) * I)‖ ^ 2 ≤
      t ^ 2 * (lam i - mu j) ^ 2 := by
    have hr : (|t| * |lam i - mu j|) ^ 2 = t ^ 2 * (lam i - mu j) ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs]
    rw [← hr]
    first
      | exact pow_le_pow_left h0 h 2
      | exact pow_le_pow_left₀ h0 h 2
      | nlinarith
  have hJ : 0 ≤ ‖J i j‖ ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hsq hJ
  nlinarith

end SteklovAudit.DuhamelSpectral
