import Mathlib

/-!
# F1.1 One-dimensional trace inequality (toy model for (G1) Sobolev traces)

Proved, for real-valued `f : ℝ → ℝ` with `HasDerivAt f (f' x) x` at every `x : ℝ` and `f'` continuous:

* `trace_identity`: `f 0 ^ 2 = ∫₀¹ (f x ^ 2 - 2 (1 - x) f x f' x) dx`
  (fundamental theorem of calculus applied to `(x - 1) * f x ^ 2`);
* `integrand_le`: for `x ∈ [0, 1]`, `a ^ 2 - 2 (1 - x) a b ≤ 2 (a ^ 2 + b ^ 2)`;
* `trace_1d`: `f 0 ^ 2 ≤ 2 * ∫₀¹ (f x ^ 2 + f' x ^ 2) dx`;
* `trace_1d_abs`: the same with `|f 0| ^ 2`, `|f x| ^ 2`, `|f' x| ^ 2`;
* `trace_1d_contDiff`: the same for `ContDiff ℝ 1 f`, with `deriv f`.

NOT proved: anything about the Sobolev space `H¹`, a trace operator, density of smooth functions,
complex-valued `f`, functions that are `C¹` only on `[0, 1]` (the hypotheses ask for a derivative on
all of `ℝ`; the extension from `[0, 1]` is not proved), sharpness of the constant `2`, or any trace
inequality on a domain in `ℝ²` or `ℝ³`. This is a one-dimensional toy model for roadmap item F1.1.
It is not the paper's trace map or Dirichlet-to-Neumann operator, and it proves none of
`[H1]`–`[H6]` and not the main theorem.
-/

namespace SteklovAudit.Foundations.Trace1D

/-- `f 0 ^ 2 = ∫₀¹ (f² - 2 (1 - x) f f')`, from the FTC for `(x - 1) * f x ^ 2`. -/
theorem trace_identity {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') :
    f 0 ^ 2 = ∫ x in (0:ℝ)..1, (f x ^ 2 - 2 * (1 - x) * f x * f' x) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hg : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun y => (y - 1) * (f y * f y))
      (f x ^ 2 - 2 * (1 - x) * f x * f' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
    exact (h1.mul ((hf x).mul (hf x))).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun x => f x ^ 2 - 2 * (1 - x) * f x * f' x)
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun x => f x ^ 2 - 2 * (1 - x) * f x * f' x).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hg hint]
  ring

/-- Pointwise bound on the integrand of `trace_identity` for `x ∈ [0, 1]`. -/
theorem integrand_le (x a b : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    a ^ 2 - 2 * (1 - x) * a * b ≤ 2 * (a ^ 2 + b ^ 2) := by
  obtain ⟨h0, h1⟩ := hx
  have h2 : 0 ≤ x * (2 - x) * a ^ 2 :=
    mul_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg a)
  nlinarith [sq_nonneg ((1 - x) * a + b), sq_nonneg b, h2]

/-- F1.1: the one-dimensional trace inequality `f(0)² ≤ 2 ∫₀¹ (f² + f'²)`. -/
theorem trace_1d {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    f 0 ^ 2 ≤ 2 * ∫ x in (0:ℝ)..1, (f x ^ 2 + f' x ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  rw [trace_identity hf hf', ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact (by fun_prop : Continuous fun x => f x ^ 2 - 2 * (1 - x) * f x * f' x).intervalIntegrable 0 1
  · exact (by fun_prop : Continuous fun x => 2 * (f x ^ 2 + f' x ^ 2)).intervalIntegrable 0 1
  · intro x hx
    exact integrand_le x (f x) (f' x) hx

/-- F1.1 with absolute values, as stated in the roadmap: `|f(0)|² ≤ 2 ∫₀¹ (|f|² + |f'|²)`. -/
theorem trace_1d_abs {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    |f 0| ^ 2 ≤ 2 * ∫ x in (0:ℝ)..1, (|f x| ^ 2 + |f' x| ^ 2) := by
  simp only [sq_abs]
  exact trace_1d hf hf'

/-- F1.1 for a `C¹` function on `ℝ`, with `deriv f`. -/
theorem trace_1d_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    f 0 ^ 2 ≤ 2 * ∫ x in (0:ℝ)..1, (f x ^ 2 + deriv f x ^ 2) :=
  trace_1d (fun x => ((hf.differentiable (by first | exact le_rfl | exact one_ne_zero | norm_num)) x).hasDerivAt)
    (hf.continuous_deriv (by first | exact le_rfl | norm_num))

/-- Non-vacuity: the constant function `1` (derivative `0`) satisfies the hypotheses, and the
inequality reads `1 ≤ 2`. -/
theorem trace_1d_const_one : (fun _ : ℝ => (1:ℝ)) 0 ^ 2 ≤
    2 * ∫ x in (0:ℝ)..1, ((fun _ : ℝ => (1:ℝ)) x ^ 2 + (fun _ : ℝ => (0:ℝ)) x ^ 2) :=
  trace_1d (fun x => hasDerivAt_const x 1) continuous_const

end SteklovAudit.Foundations.Trace1D
