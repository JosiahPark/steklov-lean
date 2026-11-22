import Mathlib

/-!
# F1.2 Half-line trace inequality with constant 1

Roadmap item F1.2 (Foundations). For a real function `f` on `ℝ`, differentiable everywhere with
continuous derivative `f'`, such that `f x → 0` as `x → ∞` and `f ^ 2`, `f' ^ 2` are integrable on
`(0, ∞)`,

  `f 0 ^ 2 ≤ ∫ x in Ioi 0, (f x ^ 2 + f' x ^ 2)`.

Proof: `f 0 ^ 2 = -∫₀^∞ (f · f)' = -∫₀^∞ 2 f f'` (improper FTC,
`integral_Ioi_of_hasDerivAt_of_tendsto`), and `-2 a b ≤ a ^ 2 + b ^ 2` pointwise.
The decay `f → 0` and the two integrability conditions are explicit hypotheses.

What this file does NOT prove: nothing about `H¹(0, ∞)` as a space, density of such `f`, trace
operators, or traces on Lipschitz domains; nothing about the paper's Dirichlet-to-Neumann operator,
`[H1]`–`[H6]`, or Theorem 1.3 / 11.1. It is a one-dimensional toy model of a trace bound.
-/

namespace SteklovAudit.Foundations.TraceHalfLine

open MeasureTheory Set Filter

/-- Pointwise bound `|2 a b| ≤ a ^ 2 + b ^ 2`, in the form used below. -/
theorem cross_abs_le (a b : ℝ) : |b * a + a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]

/-- **F1.2.** Half-line trace inequality with constant 1. -/
theorem trace_halfLine (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (hlim : Tendsto f atTop (nhds 0))
    (hsq : IntegrableOn (fun x => f x ^ 2) (Ioi 0))
    (hsq' : IntegrableOn (fun x => f' x ^ 2) (Ioi 0)) :
    f 0 ^ 2 ≤ ∫ x in Ioi (0:ℝ), (f x ^ 2 + f' x ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hsum : IntegrableOn (fun x => f x ^ 2 + f' x ^ 2) (Ioi 0) := hsq.add hsq'
  have hpt : ∀ x, ‖f' x * f x + f x * f' x‖ ≤ f x ^ 2 + f' x ^ 2 := fun x => by
    rw [Real.norm_eq_abs]
    exact cross_abs_le (f x) (f' x)
  have hcm : Continuous fun x => f' x * f x + f x * f' x := by fun_prop
  have hcross : IntegrableOn (fun x => f' x * f x + f x * f' x) (Ioi 0) := by
    refine Integrable.mono' hsum hcm.aestronglyMeasurable ?_
    first
      | exact Filter.Eventually.of_forall hpt
      | exact Filter.eventually_of_forall hpt
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun y => f y * f y)
      (f' x * f x + f x * f' x) x := fun x _ => (hf x).mul (hf x)
  have hcw : ContinuousWithinAt (fun y => f y * f y) (Ici 0) 0 :=
    (hfc.mul hfc).continuousWithinAt
  have hlim2 : Tendsto (fun y => f y * f y) atTop (nhds 0) := by
    have h := hlim.mul hlim
    rwa [mul_zero] at h
  have hftc : ∫ x in Ioi (0:ℝ), (f' x * f x + f x * f' x) = 0 - f 0 * f 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto hcw hderiv hcross hlim2
  have hneg : ∫ x in Ioi (0:ℝ), -(f' x * f x + f x * f' x)
      = -∫ x in Ioi (0:ℝ), (f' x * f x + f x * f' x) := by
    first
      | exact integral_neg _
      | rw [integral_neg]
  have hle : ∀ x, -(f' x * f x + f x * f' x) ≤ f x ^ 2 + f' x ^ 2 := fun x =>
    le_trans (neg_le_abs _) (cross_abs_le (f x) (f' x))
  have hmono : ∫ x in Ioi (0:ℝ), -(f' x * f x + f x * f' x)
      ≤ ∫ x in Ioi (0:ℝ), (f x ^ 2 + f' x ^ 2) := by
    first
      | exact setIntegral_mono hcross.neg hsum hle
      | exact integral_mono hcross.neg hsum hle
      | exact integral_mono (Integrable.neg hcross) hsum hle
  nlinarith [hftc, hneg, hmono]

end SteklovAudit.Foundations.TraceHalfLine
