import Mathlib

/-!
# F1.1 One-dimensional trace inequality (toy model for (G1) Sobolev traces)

Proved, for real-valued `f f' : ℝ → ℝ` with `HasDerivAt f (f' x) x` at every `x ∈ [0, 1]` and
`f'` continuous on `[0, 1]`:

* `trace_identity_on`: `f 0 ^ 2 = ∫₀¹ (f x ^ 2 - 2 (1 - x) f x f' x) dx`
  (fundamental theorem of calculus for `g y = (y - 1) * (f y * f y)`, with `g 1 = 0`, `g 0 = -f 0 ^ 2`);
* `integrand_le`: for `x ∈ [0, 1]`, `a ^ 2 - 2 (1 - x) a b ≤ 2 (a ^ 2 + b ^ 2)`;
* `trace_1d_on`: `f 0 ^ 2 ≤ 2 * ∫₀¹ (f x ^ 2 + f' x ^ 2) dx`;
* corollaries: `trace_inequality` (same with `deriv f`), `trace_1d` (derivative on all of `ℝ`),
  `trace_1d_abs` (absolute values, as stated in the roadmap), `trace_1d_contDiff` (`ContDiff ℝ 1 f`),
  and the non-vacuity check `trace_1d_const_one`.

The derivative at the endpoints `0` and `1` is two-sided (`HasDerivAt`), so `f` must be defined and
differentiable slightly beyond `[0, 1]`; one-sided derivatives are not treated.

NOT proved: anything about the Sobolev space `H¹`, a trace operator, density of smooth functions,
complex-valued `f`, sharpness of the constant `2`, or any trace inequality on a domain in `ℝ²` or
`ℝ³`. This is a one-dimensional toy model for roadmap item F1.1. It is not the paper's trace map or
Dirichlet-to-Neumann operator, and it proves none of (7.2), (7.29), (7.38)/(7.45), (9.1),
`[H1]`–`[H6]`, and not the main theorem (Theorem 1.3 / 11.1).

History: attempts 9891351 and 47f99e7 failed at the derivative step (`ring` inside `congr_deriv`
facing an unreduced `(fun y => y - 1) x`). Here the derivative of `g` is stated in exactly the shape
`HasDerivAt.mul` produces, so it is closed by `exact` (definitional unfolding), and the conversion
to the readable integrand is a separate `funext`/`ring1` step that involves no beta-redex.
-/

namespace SteklovAudit.Foundations.Trace1D

/-- Pointwise bound on the integrand of `trace_identity_on` for `x ∈ [0, 1]`. -/
theorem integrand_le (x a b : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    a ^ 2 - 2 * (1 - x) * a * b ≤ 2 * (a ^ 2 + b ^ 2) := by
  obtain ⟨h0, h1⟩ := hx
  have h2 : 0 ≤ x * (2 - x) * a ^ 2 :=
    mul_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg a)
  have h3 : 0 ≤ x * (2 - x) * b ^ 2 :=
    mul_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg b)
  nlinarith [sq_nonneg ((1 - x) * a + b), sq_nonneg (a + (1 - x) * b), sq_nonneg a, sq_nonneg b,
    h2, h3]

/-- `f 0 ^ 2 = ∫₀¹ (f² - 2 (1 - x) f f')`, from the FTC for `(x - 1) * (f x * f x)`. -/
theorem trace_identity_on {f f' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Set.Icc (0:ℝ) 1)) :
    f 0 ^ 2 = ∫ x in (0:ℝ)..1, (f x ^ 2 - 2 * (1 - x) * f x * f' x) := by
  have hu : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f (f' x) x := by
    rw [hu]; exact hderiv
  have hf'u : ContinuousOn f' (Set.uIcc (0:ℝ) 1) := by
    rw [hu]; exact hf'
  have hfc : ContinuousOn f (Set.uIcc (0:ℝ) 1) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  -- derivative of `g y = (y - 1) * (f y * f y)`, in the shape produced by `HasDerivAt.mul`
  have hg : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun y => (y - 1) * (f y * f y))
      (1 * (f x * f x) + (x - 1) * (f' x * f x + f x * f' x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id' x).sub_const 1
    have h2 : HasDerivAt (fun y => f y * f y) (f' x * f x + f x * f' x) x :=
      (hd x hx).mul (hd x hx)
    first
      | exact h1.mul h2
      | exact (h1.mul h2).congr_deriv (by beta_reduce; ring1)
      | exact (h1.mul h2).congr_deriv (by simp only []; ring1)
  have hcont : ContinuousOn
      (fun x => 1 * (f x * f x) + (x - 1) * (f' x * f x + f x * f' x)) (Set.uIcc (0:ℝ) 1) := by
    first
      | exact (continuousOn_const.mul (hfc.mul hfc)).add
          ((continuousOn_id.sub continuousOn_const).mul ((hf'u.mul hfc).add (hfc.mul hf'u)))
      | fun_prop
  have hint : IntervalIntegrable
      (fun x => 1 * (f x * f x) + (x - 1) * (f' x * f x + f x * f' x))
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable
  have hEq : ∫ x in (0:ℝ)..1, (f x ^ 2 - 2 * (1 - x) * f x * f' x) =
      ∫ x in (0:ℝ)..1, (1 * (f x * f x) + (x - 1) * (f' x * f x + f x * f' x)) := by
    first
      | (congr 1; funext x; ring1)
      | exact intervalIntegral.integral_congr (fun x _ => by ring1)
  rw [hEq, intervalIntegral.integral_eq_sub_of_hasDerivAt hg hint]
  first
    | ring1
    | (show f 0 ^ 2 = (1 - 1) * (f 1 * f 1) - (0 - 1) * (f 0 * f 0); ring1)
    | (beta_reduce; ring1)
    | (norm_num; ring1)

/-- F1.1: `f(0)² ≤ 2 ∫₀¹ (f² + f'²)` for `f` with derivative `f'` on `[0, 1]`, `f'` continuous there. -/
theorem trace_1d_on {f f' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Set.Icc (0:ℝ) 1)) :
    f 0 ^ 2 ≤ 2 * ∫ x in (0:ℝ)..1, (f x ^ 2 + f' x ^ 2) := by
  have hu : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hf'u : ContinuousOn f' (Set.uIcc (0:ℝ) 1) := by
    rw [hu]; exact hf'
  have hfc : ContinuousOn f (Set.uIcc (0:ℝ) 1) := by
    rw [hu]; exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hL : ContinuousOn (fun x => f x ^ 2 - 2 * (1 - x) * f x * f' x) (Set.uIcc (0:ℝ) 1) := by
    first
      | exact (hfc.pow 2).sub
          (((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).mul hfc).mul hf'u)
      | fun_prop
  have hR : ContinuousOn (fun x => 2 * (f x ^ 2 + f' x ^ 2)) (Set.uIcc (0:ℝ) 1) := by
    first
      | exact continuousOn_const.mul ((hfc.pow 2).add (hf'u.pow 2))
      | fun_prop
  rw [trace_identity_on hderiv hf', ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one hL.intervalIntegrable hR.intervalIntegrable
  intro x hx
  exact integrand_le x (f x) (f' x) hx

/-- F1.1 with `deriv f`: if `f` has derivative `deriv f x` at each `x ∈ [0, 1]` and `deriv f` is
continuous on `[0, 1]`, then `f(0)² ≤ 2 ∫₀¹ (f² + (deriv f)²)`. -/
theorem trace_inequality (f : ℝ → ℝ)
    (hf' : ContinuousOn (deriv f) (Set.Icc (0:ℝ) 1))
    (hderiv : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (deriv f x) x) :
    f 0 ^ 2 ≤ 2 * ∫ x in (0:ℝ)..1, (f x ^ 2 + deriv f x ^ 2) :=
  trace_1d_on hderiv hf'

/-- F1.1 for `f` with a derivative `f'` on all of `ℝ`, `f'` continuous. -/
theorem trace_1d {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    f 0 ^ 2 ≤ 2 * ∫ x in (0:ℝ)..1, (f x ^ 2 + f' x ^ 2) :=
  trace_1d_on (fun x _ => hf x) hf'.continuousOn

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
