import Mathlib

/-!
# F1.1 One-dimensional trace inequality

Roadmap item F1.1 (Foundations). For a real function `f` on `ℝ` that is differentiable everywhere
with continuous derivative `f'`,

  `f 0 ^ 2 ≤ 2 * ∫ x in (0:ℝ)..1, (f x ^ 2 + f' x ^ 2)`.

Proof: the fundamental theorem of calculus for `g y = (y - 1) * (f y * f y)` on `[0, 1]` gives
`f 0 ^ 2 = ∫₀¹ (f² + 2 (x - 1) f f')`, and pointwise on `[0, 1]`,
`a² + 2 (x - 1) a b ≤ 2 (a² + b²)` because `(x - 1)² ≤ 1`.

Hypotheses are stated on all of `ℝ` (a `C¹` function on `ℝ`), not on `[0, 1]` only.

What this file does NOT prove: nothing about Sobolev spaces `H¹`, trace operators, Lipschitz
domains, or any multi-dimensional trace theorem; nothing about the paper's Dirichlet-to-Neumann
operator, `[H1]`–`[H6]`, or Theorem 1.3 / 11.1. It is a one-dimensional toy model of a trace bound.
-/

namespace SteklovAudit.Foundations.Trace1D

/-- Pointwise inequality used under the integral. -/
theorem pointwise_bound (a b x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    a * a + 2 * (x - 1) * a * b ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h1 : 0 ≤ (a - (x - 1) * b) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ x * (2 - x) * b ^ 2 :=
    mul_nonneg (mul_nonneg hx0 (by linarith)) (sq_nonneg b)
  nlinarith [h1, h2, sq_nonneg a, sq_nonneg b]

/-- **F1.1.** One-dimensional trace inequality on `[0, 1]` with constant 2. -/
theorem trace_1d (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    f 0 ^ 2 ≤ 2 * ∫ x in (0:ℝ)..1, (f x ^ 2 + f' x ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  -- derivative of g y = (y - 1) * (f y * f y)
  have hg : ∀ x, HasDerivAt (fun y => (y - 1) * (f y * f y))
      (f x * f x + 2 * (x - 1) * f x * f' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id' x).sub_const 1
    have h3 := h1.mul ((hf x).mul (hf x))
    have e : (1 : ℝ) * (f x * f x) + (x - 1) * (f' x * f x + f x * f' x)
        = f x * f x + 2 * (x - 1) * f x * f' x := by ring
    exact h3.congr_deriv e
  have hcont : Continuous fun x => f x * f x + 2 * (x - 1) * f x * f' x := by
    fun_prop
  have hcont2 : Continuous fun x => 2 * (f x ^ 2 + f' x ^ 2) := by
    fun_prop
  have hint : IntervalIntegrable (fun x => f x * f x + 2 * (x - 1) * f x * f' x)
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun x => 2 * (f x ^ 2 + f' x ^ 2))
      MeasureTheory.volume 0 1 := hcont2.intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x) hint
  have hval : ∫ x in (0:ℝ)..1, (f x * f x + 2 * (x - 1) * f x * f' x) = f 0 ^ 2 := by
    rw [hftc]
    ring
  have hmono : ∫ x in (0:ℝ)..1, (f x * f x + 2 * (x - 1) * f x * f' x)
      ≤ ∫ x in (0:ℝ)..1, 2 * (f x ^ 2 + f' x ^ 2) :=
    intervalIntegral.integral_mono_on (by norm_num) hint hint2
      (fun x hx => pointwise_bound (f x) (f' x) x hx.1 hx.2)
  have hconst : ∫ x in (0:ℝ)..1, 2 * (f x ^ 2 + f' x ^ 2)
      = 2 * ∫ x in (0:ℝ)..1, (f x ^ 2 + f' x ^ 2) :=
    intervalIntegral.integral_const_mul 2 _
  linarith [hval, hmono, hconst]

end SteklovAudit.Foundations.Trace1D
