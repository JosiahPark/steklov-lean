import Mathlib

/-!
# Section 4: the scalar steps of Lemma 4.1, (4.7), (4.10) and (4.11)

Section 4 bounds the heat-fiber difference `e^{−uD_α} − e^{−uD_0}` in trace norm and localizes it.
The operator inequalities (Loewner–Heinz, the weighted ideal (4.4), the Duhamel identity (4.6)) are not
formalized. This module proves the real-analysis steps the proofs rely on:

* `beta_scaling`, `heat_convolution`: in Lemma 4.1 the two functional-calculus factors
  `C(u−v)^(q−1)e^{−c(u−v)}` and `C'v^(q−1)e^{−cv}` convolve to exactly `C C' B(q,q) u^(2q−1) e^{−cu}`
  ("their product is integrable in v, with integral u^(2q−1) B(q,q)");
* `beta_integrable`: `B(q,q)` is a genuine (convergent) integral for `0 < q ≤ 1`;
* `time_integral`, `heat_trace_integrable`: the bound (4.5) makes the trace norm integrable over
  `u ∈ (0, ∞)`, with `∫₀^∞ ≤ K (1/c)^(2q) Γ(2q)`; hence `M_α < ∞` in (4.7);
* `fiber_scaling`: (4.7), `(1/2π) ∫_ℝ f(t|k|) dk = M_α / t` with `M_α = π⁻¹ ∫₀^∞ f`;
* `edge_heat_limit`: (4.9) ⇒ the edge term of (4.10) by dominated convergence: for `q ∈ L¹` and a
  bounded measurable cutoff mass `G` continuous at the edge,
  `t ∫ t⁻² q(s/t) G(s) ds → (∫ q) G(0)` as `t → 0⁺`;
* `integral_inv_one_add_exp`, `cosh_integral_log_bound`: the integral in (4.11),
  `∫₀^∞ dv/(1 + k cosh v) ≤ log(1 + 2/k) ≤ 2 log(2/k)` for `0 < k ≤ 1/2`.

What this module does NOT prove: (4.1)–(4.4), the operator bound (4.5) itself (taken as the hypothesis
of `heat_trace_integrable`), (4.8), the identification of the diagonal density `q_α` in (4.9), or (4.12)–(4.14).
-/

namespace SteklovAudit.HeatFiber

open MeasureTheory Set Filter Topology intervalIntegral

/-- `B(q, q) = ∫₀¹ x^(q−1) (1 − x)^(q−1) dx`. -/
noncomputable def betaQ (q : ℝ) : ℝ := ∫ x in (0:ℝ)..1, x ^ (q - 1) * (1 - x) ^ (q - 1)

/-- Scaling of the Beta integral: `∫₀^u (u − v)^(q−1) v^(q−1) dv = u^(2q−1) B(q, q)`. -/
theorem beta_scaling (q u : ℝ) (hu : 0 < u) :
    ∫ v in (0:ℝ)..u, (u - v) ^ (q - 1) * v ^ (q - 1) = u ^ (2 * q - 1) * betaQ q := by
  have hs := intervalIntegral.integral_comp_mul_left
    (fun v => (u - v) ^ (q - 1) * v ^ (q - 1)) (a := 0) (b := 1) hu.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at hs
  have hc : ∫ x in (0:ℝ)..1, (u - u * x) ^ (q - 1) * (u * x) ^ (q - 1) =
      ∫ x in (0:ℝ)..1, u ^ (2 * q - 2) * (x ^ (q - 1) * (1 - x) ^ (q - 1)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    rw [show u - u * x = u * (1 - x) by ring, Real.mul_rpow hu.le (by linarith [hx.2]),
      Real.mul_rpow hu.le hx.1, show 2 * q - 2 = (q - 1) + (q - 1) by ring, Real.rpow_add hu]
    ring
  rw [hc, intervalIntegral.integral_const_mul] at hs
  rw [betaQ]
  have : ∫ v in (0:ℝ)..u, (u - v) ^ (q - 1) * v ^ (q - 1) =
      u * (u⁻¹ * ∫ v in (0:ℝ)..u, (u - v) ^ (q - 1) * v ^ (q - 1)) := by
    field_simp
  rw [this, ← hs, show 2 * q - 1 = (2 * q - 2) + 1 by ring, Real.rpow_add_one hu.ne']
  ring

/-- Lemma 4.1, scalar part: the convolution of the two functional-calculus factors
`C (u−v)^(q−1) e^{−c(u−v)}` and `C' v^(q−1) e^{−cv}` is `C C' B(q,q) u^(2q−1) e^{−cu}`. -/
theorem heat_convolution (C C' c q u : ℝ) (hu : 0 < u) :
    ∫ v in (0:ℝ)..u, (C * (u - v) ^ (q - 1) * Real.exp (-(c * (u - v)))) *
        (C' * v ^ (q - 1) * Real.exp (-(c * v))) =
      C * C' * betaQ q * u ^ (2 * q - 1) * Real.exp (-(c * u)) := by
  have e : ∀ v : ℝ, (C * (u - v) ^ (q - 1) * Real.exp (-(c * (u - v)))) *
      (C' * v ^ (q - 1) * Real.exp (-(c * v))) =
      (C * C' * Real.exp (-(c * u))) * ((u - v) ^ (q - 1) * v ^ (q - 1)) := by
    intro v
    rw [show -(c * u) = -(c * (u - v)) + -(c * v) by ring, Real.exp_add]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, beta_scaling q u hu]
  ring

/-- `∫₀^∞ u^(2q−1) e^{−cu} du = (1/c)^(2q) Γ(2q)`. -/
theorem time_integral (q c : ℝ) (hq : 0 < q) (hc : 0 < c) :
    ∫ u in Ioi (0:ℝ), u ^ (2 * q - 1) * Real.exp (-(c * u)) = (1 / c) ^ (2 * q) * Real.Gamma (2 * q) :=
  Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hc

theorem time_integrable (q c : ℝ) (hq : 0 < q) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => u ^ (2 * q - 1) * Real.exp (-(c * u))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2 * q - 1) (p := 1) (b := c)
    (by linarith) one_pos hc
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]


/-- The Beta integrand is integrable on `[0, 1]` for `q > 0`, so `B(q, q)` is a genuine integral
(`0 < q ≤ 1`, which covers the paper's `0 < q < 1/2`). -/
theorem beta_integrable (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    IntervalIntegrable (fun x : ℝ => x ^ (q - 1) * (1 - x) ^ (q - 1)) volume 0 1 := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (q - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h2 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (q - 1)) volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := 0) (r := q - 1)
      (by linarith)).comp_sub_left 1
    simpa using this
  have hg : IntervalIntegrable (fun x : ℝ => (1 / 2 : ℝ) ^ (q - 1) * (x ^ (q - 1) + (1 - x) ^ (q - 1)))
      volume 0 1 := (h1.add h2).const_mul _
  refine hg.mono_fun ?_ ?_
  · exact ((measurable_id.pow_const _).mul ((measurable_const.sub measurable_id).pow_const _))
      |>.aestronglyMeasurable
  · rw [Set.uIoc_of_le zero_le_one]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
    have hx0 : 0 < x := hx.1
    have a0 : 0 ≤ x ^ (q - 1) := Real.rpow_nonneg hx0.le _
    have b0 : 0 ≤ (1 - x) ^ (q - 1) := Real.rpow_nonneg (by linarith [hx.2]) _
    have c0 : 0 < (1 / 2 : ℝ) ^ (q - 1) := Real.rpow_pos_of_pos (by norm_num) _
    show ‖x ^ (q - 1) * (1 - x) ^ (q - 1)‖ ≤ ‖(1 / 2 : ℝ) ^ (q - 1) * (x ^ (q - 1) + (1 - x) ^ (q - 1))‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg a0 b0),
      abs_of_nonneg (mul_nonneg c0.le (add_nonneg a0 b0))]
    have hneg : q - 1 ≤ 0 := by linarith
    rcases le_or_gt x (1 / 2) with hle | hgt
    · have : (1 - x) ^ (q - 1) ≤ (1 / 2 : ℝ) ^ (q - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) hneg
      nlinarith
    · have : x ^ (q - 1) ≤ (1 / 2 : ℝ) ^ (q - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hgt.le hneg
      nlinarith


/-- (4.5) ⇒ integrability in `u`: a measurable `f ≥ 0` with `f(u) ≤ K u^(2q−1) e^{−cu}` is integrable
on `(0, ∞)` and `∫₀^∞ f ≤ K (1/c)^(2q) Γ(2q)`. -/
theorem heat_trace_integrable (f : ℝ → ℝ) (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (K q c : ℝ) (hq : 0 < q) (hc : 0 < c) (hf0 : ∀ u, 0 < u → 0 ≤ f u)
    (hfK : ∀ u, 0 < u → f u ≤ K * (u ^ (2 * q - 1) * Real.exp (-(c * u)))) :
    IntegrableOn f (Ioi 0) ∧
      ∫ u in Ioi (0:ℝ), f u ≤ K * ((1 / c) ^ (2 * q) * Real.Gamma (2 * q)) := by
  have hg := (time_integrable q c hq hc).const_mul K
  have hint : IntegrableOn f (Ioi 0) := by
    refine Integrable.mono' hg hfm (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 u hu)]
    exact hfK u hu
  refine ⟨hint, ?_⟩
  rw [← time_integral q c hq hc, ← MeasureTheory.integral_const_mul]
  exact setIntegral_mono_on hint hg measurableSet_Ioi fun u hu => hfK u hu

/-- (4.7): the edge-Fourier fibers `(e^{−tD_α} − e^{−tD_π})_k` have trace norm `f(t|k|)` with
`f(u) = ‖e^{−uD_α} − e^{−uD_0}‖₁`; then `(1/2π) ∫_ℝ f(t|k|) dk = M_α / t`, `M_α = π⁻¹ ∫₀^∞ f`. -/
theorem fiber_scaling (f : ℝ → ℝ) (t : ℝ) (ht : 0 < t) :
    1 / (2 * Real.pi) * ∫ k : ℝ, f (t * |k|) =
      (1 / Real.pi * ∫ u in Ioi (0:ℝ), f u) / t := by
  have h := integral_comp_abs (f := fun x => f (t * x))
  rw [h, integral_comp_mul_left_Ioi f 0 ht, mul_zero, smul_eq_mul]
  have := Real.pi_pos
  field_simp

/-- (4.9) ⇒ (4.10), edge term: if `q ∈ L¹(ℝ)` and the cutoff mass `G` is bounded, measurable and
continuous at the edge `s = 0`, then `t ∫ t^{−2} q(s/t) G(s) ds → (∫ q) G(0)` as `t → 0⁺`. -/
theorem edge_heat_limit (q G : ℝ → ℝ) (hq : Integrable q) (hG : Measurable G) (M : ℝ)
    (hGM : ∀ s, |G s| ≤ M) (hG0 : ContinuousAt G 0) :
    Tendsto (fun t : ℝ => t * ∫ s, t⁻¹ ^ 2 * q (s / t) * G s) (𝓝[>] 0)
      (𝓝 ((∫ σ, q σ) * G 0)) := by
  have hsub : ∀ t : ℝ, 0 < t →
      t * ∫ s, t⁻¹ ^ 2 * q (s / t) * G s = ∫ σ, q σ * G (t * σ) := by
    intro t ht
    have h := MeasureTheory.Measure.integral_comp_mul_left
      (fun s => t⁻¹ ^ 2 * q (s / t) * G s) t
    have e : ∀ σ : ℝ, t * σ / t = σ := fun σ => by field_simp
    simp only [e, smul_eq_mul, abs_inv, abs_of_pos ht] at h
    have e2 : (fun σ => t⁻¹ ^ 2 * q σ * G (t * σ)) = fun σ => t⁻¹ ^ 2 * (q σ * G (t * σ)) := by
      funext σ; ring
    rw [e2, MeasureTheory.integral_const_mul] at h
    have h2 : ∫ σ, q σ * G (t * σ) = t ^ 2 * (t⁻¹ * ∫ s, t⁻¹ ^ 2 * q (s / t) * G s) := by
      rw [← h]; field_simp
    rw [h2]; field_simp
  have hlim : Tendsto (fun t : ℝ => ∫ σ, q σ * G (t * σ)) (𝓝[>] 0) (𝓝 (∫ σ, q σ * G 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun σ => M * |q σ|) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t =>
        hq.aestronglyMeasurable.mul (hG.comp (measurable_const_mul t)).aestronglyMeasurable
    · refine Eventually.of_forall fun t => Eventually.of_forall fun σ => ?_
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hGM _) (abs_nonneg _)
    · exact hq.abs.const_mul M
    · refine Eventually.of_forall fun σ => ?_
      have ht : Tendsto (fun t : ℝ => t * σ) (𝓝[>] 0) (𝓝 0) := by
        have hc : Continuous fun t : ℝ => t * σ := continuous_id.mul continuous_const
        have := (hc.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
        simpa using this
      exact (hG0.tendsto.comp ht).const_mul (q σ)
  rw [MeasureTheory.integral_mul_const] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact (hsub t ht).symm


/-- `∫₀^∞ dv / (1 + a e^v) = log(1 + 1/a)` for `a > 0`. -/
theorem integral_inv_one_add_exp (a : ℝ) (ha : 0 < a) :
    ∫ v in Ioi (0:ℝ), 1 / (1 + a * Real.exp v) = Real.log (1 + 1 / a) := by
  have hF : ∀ v, HasDerivAt (fun v => -Real.log (a + Real.exp (-v))) (1 / (1 + a * Real.exp v)) v := by
    intro v
    have hpos : 0 < a + Real.exp (-v) := by positivity
    have h1 : HasDerivAt (fun v => a + Real.exp (-v)) (-Real.exp (-v)) v := by
      simpa using ((hasDerivAt_neg v).exp).const_add a
    have h2 := (h1.log hpos.ne').neg
    convert h2 using 1
    rw [Real.exp_neg]
    have := Real.exp_pos v
    field_simp
    ring
  have hlim : Tendsto (fun v => -Real.log (a + Real.exp (-v))) atTop (𝓝 (-Real.log a)) := by
    have h : Tendsto (fun v => a + Real.exp (-v)) atTop (𝓝 (a + 0)) :=
      tendsto_const_nhds.add (Real.tendsto_exp_neg_atTop_nhds_zero)
    rw [add_zero] at h
    exact ((Real.continuousAt_log ha.ne').tendsto.comp h).neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (hF 0).continuousAt.continuousWithinAt
    (fun v _ => hF v) (fun v _ => by positivity) hlim]
  rw [neg_zero, Real.exp_zero, show -Real.log a - -Real.log (a + 1) = Real.log (a + 1) - Real.log a
    by ring, ← Real.log_div (by positivity) ha.ne']
  congr 1; field_simp

/-- (4.11), the integral after the substitution `p = sinh v`: for `0 < k ≤ 1/2`,
`∫₀^∞ dv/(1 + k cosh v) ≤ log(1 + 2/k) ≤ 2 log(2/k)`. -/
theorem cosh_integral_log_bound (k : ℝ) (hk : 0 < k) (hk2 : k ≤ 1 / 2) :
    ∫ v in Ioi (0:ℝ), 1 / (1 + k * Real.cosh v) ≤ 2 * Real.log (2 / k) := by
  have ha : 0 < k / 2 := by positivity
  have hle : ∀ v, 1 / (1 + k * Real.cosh v) ≤ 1 / (1 + k / 2 * Real.exp v) := by
    intro v
    have h1 : Real.exp v / 2 ≤ Real.cosh v := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-v)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hint2 : IntegrableOn (fun v : ℝ => 1 / (1 + k / 2 * Real.exp v)) (Ioi 0) := by
    have hF : ∀ v, HasDerivAt (fun v => -Real.log (k / 2 + Real.exp (-v)))
        (1 / (1 + k / 2 * Real.exp v)) v := by
      intro v
      have hpos : 0 < k / 2 + Real.exp (-v) := by positivity
      have h1 : HasDerivAt (fun v => k / 2 + Real.exp (-v)) (-Real.exp (-v)) v := by
        simpa using ((hasDerivAt_neg v).exp).const_add (k / 2)
      have h2 := (h1.log hpos.ne').neg
      convert h2 using 1
      rw [Real.exp_neg]
      have := Real.exp_pos v
      field_simp
      ring
    have hlim : Tendsto (fun v => -Real.log (k / 2 + Real.exp (-v))) atTop (𝓝 (-Real.log (k / 2))) := by
      have h : Tendsto (fun v => k / 2 + Real.exp (-v)) atTop (𝓝 (k / 2 + 0)) :=
        tendsto_const_nhds.add (Real.tendsto_exp_neg_atTop_nhds_zero)
      rw [add_zero] at h
      exact ((Real.continuousAt_log ha.ne').tendsto.comp h).neg
    exact integrableOn_Ioi_deriv_of_nonneg (hF 0).continuousAt.continuousWithinAt
      (fun v _ => hF v) (fun v _ => by positivity) hlim
  have hint1 : IntegrableOn (fun v : ℝ => 1 / (1 + k * Real.cosh v)) (Ioi 0) := by
    refine Integrable.mono' hint2 ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun v _ => ?_)
    · exact (Continuous.aestronglyMeasurable (by fun_prop (disch := intro x; positivity)))
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hle v
  calc ∫ v in Ioi (0:ℝ), 1 / (1 + k * Real.cosh v)
      ≤ ∫ v in Ioi (0:ℝ), 1 / (1 + k / 2 * Real.exp v) :=
        setIntegral_mono_on hint1 hint2 measurableSet_Ioi fun v _ => hle v
    _ = Real.log (1 + 2 / k) := by
        rw [integral_inv_one_add_exp _ ha]; congr 1; field_simp
    _ ≤ 2 * Real.log (2 / k) := by
        have h4 : 4 ≤ 2 / k := by rw [le_div_iff₀ hk]; linarith
        have hl : Real.log 2 ≤ Real.log (2 / k) := Real.log_le_log (by norm_num) (by linarith)
        calc Real.log (1 + 2 / k) ≤ Real.log (2 * (2 / k)) :=
              Real.log_le_log (by positivity) (by linarith)
          _ = Real.log 2 + Real.log (2 / k) := Real.log_mul (by norm_num) (by positivity)
          _ ≤ 2 * Real.log (2 / k) := by linarith

end SteklovAudit.HeatFiber
