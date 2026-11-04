import Mathlib
import SteklovAudit.AbstractTransfer

/-!
# Abstract transfer layer, step B2: Duhamel with the time factor

In spectral coordinates at a finite cutoff, the operator e^{itA} J - J e^{itB} has
coefficients (exp(i t a_i) - exp(i t b_j)) J_ij. This file proves the entrywise bound
|exp(i t x) - exp(i t y)| ≤ |t| |x - y| (complex exponential, real t, x, y) and the
resulting Hilbert–Schmidt bound
  ‖e^{itA} J - J e^{itB}‖²_HS ≤ t² ‖K‖²_HS,   K = A J - J B,
which is the spectral-coordinate form of the Duhamel estimate with its time factor.

What this file does NOT prove:
* It does not construct the Dirichlet-to-Neumann operator or the unitary groups e^{itA},
  e^{itB} on a Hilbert space; eigenvalues and coefficients are arbitrary finite data.
* It does not pass from the finite cutoff to the continuous spectrum of the model operator.
* It gives no bound on ‖K‖_HS: that is Lemma 7.1', which enters only as the named
  hypothesis PDEInputs.defect from AbstractTransfer.lean.
* It does not prove the trace comparison (7.29) or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.AbstractTransfer

/-- B2, scalar form: for real t, x, y,
‖exp(i t x) - exp(i t y)‖ ≤ |t| · |x - y|. -/
theorem norm_cexp_sub_le (t x y : ℝ) :
    ‖Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) - Complex.exp (Complex.I * ((t * y : ℝ) : ℂ))‖
      ≤ |t| * |x - y| := by
  have hu : Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((t * y : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((t * (x - y) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hf : Complex.exp (Complex.I * ((t * y : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((t * (x - y) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * y : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((t * y : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * ((t * (x - y) : ℝ) : ℂ)) - 1) := by ring
  rw [hu, hf, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  calc ‖Complex.exp (Complex.I * ((t * (x - y) : ℝ) : ℂ)) - 1‖ ≤ ‖t * (x - y)‖ :=
        Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |t| * |x - y| := by rw [Real.norm_eq_abs, abs_mul]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- B2, entrywise: the (i, j) coefficient of e^{itA} J - J e^{itB} is bounded by |t| |K i j|. -/
theorem duhamel_entry (D : Data ι κ) (t : ℝ) (i : ι) (j : κ) :
    ‖(Complex.exp (Complex.I * ((t * D.a i : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * D.b j : ℝ) : ℂ))) * ((D.J i j : ℝ) : ℂ)‖
      ≤ |t| * |D.K i j| := by
  have hJ : ‖((D.J i j : ℝ) : ℂ)‖ = |D.J i j| := by simp
  rw [norm_mul, hJ]
  unfold Data.K
  rw [abs_mul]
  calc ‖Complex.exp (Complex.I * ((t * D.a i : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((t * D.b j : ℝ) : ℂ))‖ * |D.J i j|
      ≤ (|t| * |D.a i - D.b j|) * |D.J i j| :=
        mul_le_mul_of_nonneg_right (norm_cexp_sub_le t (D.a i) (D.b j)) (abs_nonneg _)
    _ = |t| * (|D.a i - D.b j| * |D.J i j|) := by ring

/-- B2, squared entrywise form: ‖coefficient‖² ≤ t² (K i j)². -/
theorem duhamel_entry_sq (D : Data ι κ) (t : ℝ) (i : ι) (j : κ) :
    ‖(Complex.exp (Complex.I * ((t * D.a i : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * D.b j : ℝ) : ℂ))) * ((D.J i j : ℝ) : ℂ)‖ ^ 2
      ≤ t ^ 2 * D.K i j ^ 2 := by
  have h := duhamel_entry D t i j
  have h0 := norm_nonneg ((Complex.exp (Complex.I * ((t * D.a i : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * D.b j : ℝ) : ℂ))) * ((D.J i j : ℝ) : ℂ))
  have hsq : ‖(Complex.exp (Complex.I * ((t * D.a i : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * D.b j : ℝ) : ℂ))) * ((D.J i j : ℝ) : ℂ)‖ ^ 2
      ≤ (|t| * |D.K i j|) ^ 2 := by nlinarith
  calc _ ≤ (|t| * |D.K i j|) ^ 2 := hsq
    _ = t ^ 2 * D.K i j ^ 2 := by rw [mul_pow, sq_abs, sq_abs]

/-- B2, Hilbert–Schmidt form (Duhamel with the time factor, spectral coordinates):
‖e^{itA} J - J e^{itB}‖²_HS ≤ t² ‖K‖²_HS. -/
theorem duhamel_hs (D : Data ι κ) (t : ℝ) :
    ∑ i, ∑ j, ‖(Complex.exp (Complex.I * ((t * D.a i : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * D.b j : ℝ) : ℂ))) * ((D.J i j : ℝ) : ℂ)‖ ^ 2
      ≤ t ^ 2 * hs2 D.K := by
  unfold hs2
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact duhamel_entry_sq D t i j

/-- B2 combined with the named Lemma 7.1' input: under PDEInputs at cutoff L,
‖e^{itA} J - J e^{itB}‖²_HS ≤ t² Ck² (1 + L)². The defect bound is a hypothesis. -/
theorem duhamel_hs_of_inputs (D : Data ι κ) (t L Cm Ck : ℝ) (H : PDEInputs D L Cm Ck) :
    ∑ i, ∑ j, ‖(Complex.exp (Complex.I * ((t * D.a i : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * D.b j : ℝ) : ℂ))) * ((D.J i j : ℝ) : ℂ)‖ ^ 2
      ≤ t ^ 2 * (Ck ^ 2 * (1 + L) ^ 2) :=
  le_trans (duhamel_hs D t) (mul_le_mul_of_nonneg_left H.defect (sq_nonneg t))

end SteklovAudit.AbstractTransfer
