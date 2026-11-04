import Mathlib

/-!
# Section 3.3: from the spectral-shift formula to the edge-momentum identity (3.13)

Section 3.3 applies the spectral-shift formula (3.10), `Tr(f(B_α) − f(B_π)) = ∫ f'(b) ξ_α(b) db`, to
`f_k(b) = φ(k/b)` for each momentum `k > 0` (so `f_k(B_α) = φ(k D_α)`), justifies Fubini by (3.12) and
"integrates in `k` first" to get (3.13):
`(1/2π) ∫_ℝ Tr(φ(|k| D_α) − φ(|k| D_π)) dk = c_α ∫₀^∞ φ(u) du`, with `c_α = I_α/π`, `I_α = ∫ ξ_α`.

This module proves that computation for any `ξ` integrable on `(0, ∞)` and any compactly supported
`C¹` test `φ` (the paper uses `φ ∈ C_c^∞((0, ∞))`):

* `deriv_test`: `(d/db) φ(k/b) = φ'(k/b)·(−k/b²)`;
* `neg_moment_deriv`: `∫₀^∞ −u φ'(u) du = ∫₀^∞ φ` (integration by parts);
* `inner_k`, `inner_k_abs`: the substitution `k = b u` in the inner integral;
* `edge_momentum`: Fubini, `∫₀^∞ dk ∫₀^∞ (d/db)φ(k/b) ξ(b) db = (∫ ξ)(∫ φ)`, with the product
  integrability that (3.12) asserts;
* `formula_3_13`: (3.13), with (3.10) for each `k` as a named hypothesis `hT`.

What this module does NOT prove: the spectral-shift theorem (3.10) (Krein's theorem for the trace-class
difference `B_α − B_π`), the existence and integrability of `ξ_α`, (3.11), or that `B_α − B_π` is trace
class. Those are taken as the inputs `hT` and `hξ`.
-/

namespace SteklovAudit.EdgeMomentum

open MeasureTheory Set

theorem zero_beyond (φ : ℝ → ℝ) (hcs : HasCompactSupport φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ u, R ≤ u → φ u = 0 ∧ deriv φ u = 0 := by
  obtain ⟨R, hR⟩ := hcs.isCompact.bddAbove
  refine ⟨max R 0 + 1, by positivity, fun u hu => ?_⟩
  have hu' : u ∉ tsupport φ := fun h => by
    have := hR h; linarith [le_max_left R 0]
  refine ⟨image_eq_zero_of_notMem_tsupport hu', ?_⟩
  by_contra hne
  exact hu' (support_deriv_subset (Function.mem_support.mpr hne))

theorem neg_moment_deriv (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hcs : HasCompactSupport φ) :
    ∫ u in Ioi (0:ℝ), -(u * deriv φ u) = ∫ u in Ioi (0:ℝ), φ u := by
  obtain ⟨R, hR0, hz⟩ := zero_beyond φ hcs
  have e1 : ∫ u in Ioi (0:ℝ), -(u * deriv φ u) = ∫ u in Ioc (0:ℝ) R, -(u * deriv φ u) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      (fun u hu => by
        have : R < u := by
          by_contra h; exact hu.2 ⟨hu.1, not_lt.mp h⟩
        simp [(hz u this.le).2])
  have e2 : ∫ u in Ioi (0:ℝ), φ u = ∫ u in Ioc (0:ℝ) R, φ u :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      (fun u hu => by
        have : R < u := by
          by_contra h; exact hu.2 ⟨hu.1, not_lt.mp h⟩
        exact (hz u this.le).1)
  rw [e1, e2, ← intervalIntegral.integral_of_le hR0.le, ← intervalIntegral.integral_of_le hR0.le]
  have hd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x => ((hφ.differentiable one_ne_zero) x).hasDerivAt
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := R)
    (u := fun x => x) (u' := fun _ => 1) (v := φ) (v' := deriv φ)
    (fun x _ => hasDerivAt_id' x) (fun x _ => hd x) intervalIntegrable_const
    ((hφ.continuous_deriv le_rfl).intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg, ibp, (hz R le_rfl).1]
  simp


/-- `d/db φ(k/b) = φ'(k/b) · (−k/b²)` for `b ≠ 0`. -/
theorem deriv_test (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (k b : ℝ) (hb : b ≠ 0) :
    deriv (fun b => φ (k / b)) b = deriv φ (k / b) * (-(k / b ^ 2)) := by
  have hd : HasDerivAt φ (deriv φ (k / b)) (k / b) :=
    ((hφ.differentiable one_ne_zero) _).hasDerivAt
  have hi : HasDerivAt (fun y : ℝ => k / y) (k * (-(b ^ 2)⁻¹)) b := by
    have := (hasDerivAt_inv hb).const_mul k
    convert this using 1
    funext y; exact div_eq_mul_inv k y
  have hc := hd.comp b hi
  rw [show (fun b => φ (k / b)) = φ ∘ fun y => k / y from rfl, hc.deriv]
  field_simp

/-- Inner integral over the momentum `k`: `∫₀^∞ φ'(k/b)(−k/b²) dk = ∫₀^∞ φ` for `b > 0`. -/
theorem inner_k (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hcs : HasCompactSupport φ) (b : ℝ) (hb : 0 < b) :
    ∫ k in Ioi (0:ℝ), deriv φ (k / b) * (-(k / b ^ 2)) = ∫ u in Ioi (0:ℝ), φ u := by
  have e : ∀ k : ℝ, deriv φ (k / b) * (-(k / b ^ 2)) =
      b⁻¹ * (fun u => -(u * deriv φ u)) (b⁻¹ * k) := by
    intro k
    simp only [div_eq_inv_mul]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun u => -(u * deriv φ u)) 0 (inv_pos.mpr hb),
    mul_zero, smul_eq_mul, neg_moment_deriv φ hφ hcs]
  field_simp

/-- Same with absolute values. -/
theorem inner_k_abs (φ : ℝ → ℝ) (b : ℝ) (hb : 0 < b) :
    ∫ k in Ioi (0:ℝ), ‖deriv φ (k / b) * (-(k / b ^ 2))‖ = ∫ u in Ioi (0:ℝ), ‖u * deriv φ u‖ := by
  have e : ∀ k : ℝ, ‖deriv φ (k / b) * (-(k / b ^ 2))‖ =
      b⁻¹ * (fun u => ‖u * deriv φ u‖) (b⁻¹ * k) := by
    intro k
    simp only [Real.norm_eq_abs, div_eq_inv_mul, abs_mul, abs_neg, abs_inv, abs_of_pos hb,
      abs_of_pos (pow_pos hb 2)]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun u => ‖u * deriv φ u‖) 0 (inv_pos.mpr hb),
    mul_zero, smul_eq_mul]
  field_simp


/-- The kernel `G(k, b) = φ'(k/b)(−k/b²)` is integrable in `k` on `(0, ∞)` for `b > 0`. -/
theorem kernel_integrable (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hcs : HasCompactSupport φ) (b : ℝ)
    (hb : 0 < b) :
    Integrable (fun k : ℝ => deriv φ (k / b) * (-(k / b ^ 2))) (volume.restrict (Ioi 0)) := by
  have hcont : Continuous fun k : ℝ => deriv φ (k / b) * (-(k / b ^ 2)) :=
    ((hφ.continuous_deriv le_rfl).comp (continuous_id.div_const b)).mul
      ((continuous_id.div_const _).neg)
  have hsupp : HasCompactSupport fun k : ℝ => deriv φ (k / b) * (-(k / b ^ 2)) := by
    have h1 : HasCompactSupport fun k : ℝ => deriv φ (b⁻¹ • k) :=
      hcs.deriv.comp_smul (inv_ne_zero hb.ne')
    have h2 : HasCompactSupport fun k : ℝ => deriv φ (k / b) := by
      convert h1 using 2 with k; rw [smul_eq_mul, div_eq_inv_mul]
    exact h2.mul_right
  exact (hcont.integrable_of_hasCompactSupport hsupp).integrableOn

/-- Fubini step (3.12)–(3.13): `∫₀^∞ dk ∫₀^∞ (d/db) φ(k/b) ξ(b) db = (∫₀^∞ ξ)(∫₀^∞ φ)`. -/
theorem edge_momentum (ξ : ℝ → ℝ) (hξ : IntegrableOn ξ (Ioi 0)) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcs : HasCompactSupport φ) :
    ∫ k in Ioi (0:ℝ), ∫ b in Ioi (0:ℝ), deriv (fun b => φ (k / b)) b * ξ b =
      (∫ b in Ioi (0:ℝ), ξ b) * ∫ u in Ioi (0:ℝ), φ u := by
  set F : ℝ → ℝ → ℝ := fun k b => deriv φ (k / b) * (-(k / b ^ 2)) * ξ b with hF
  have h1 : ∀ k, ∫ b in Ioi (0:ℝ), deriv (fun b => φ (k / b)) b * ξ b =
      ∫ b in Ioi (0:ℝ), F k b := fun k =>
    setIntegral_congr_fun measurableSet_Ioi fun b (hb : 0 < b) => by
      simp only [hF, deriv_test φ hφ k b hb.ne']
  have hmeasG : Measurable fun p : ℝ × ℝ => deriv φ (p.1 / p.2) * (-(p.1 / p.2 ^ 2)) :=
    ((hφ.continuous_deriv le_rfl).measurable.comp (measurable_fst.div measurable_snd)).mul
      ((measurable_fst.div (measurable_snd.pow_const 2)).neg)
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hξ' : AEStronglyMeasurable (fun p : ℝ × ℝ => ξ p.2)
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
      hξ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    exact hmeasG.aestronglyMeasurable.mul hξ'
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun b (hb : 0 < b) => ?_
      exact (kernel_integrable φ hφ hcs b hb).mul_const (ξ b)
    · have hc : Integrable (fun b => (∫ u in Ioi (0:ℝ), ‖u * deriv φ u‖) * ‖ξ b‖)
          (volume.restrict (Ioi 0)) := hξ.norm.const_mul _
      refine hc.congr ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun b (hb : 0 < b) => ?_
      show (∫ u in Ioi (0:ℝ), ‖u * deriv φ u‖) * ‖ξ b‖ =
        ∫ k in Ioi (0:ℝ), ‖deriv φ (k / b) * -(k / b ^ 2) * ξ b‖
      rw [show (fun k => ‖deriv φ (k / b) * -(k / b ^ 2) * ξ b‖) =
          fun k => ‖deriv φ (k / b) * -(k / b ^ 2)‖ * ‖ξ b‖ from funext fun k => norm_mul _ _,
        integral_mul_const, inner_k_abs φ b hb]
  calc ∫ k in Ioi (0:ℝ), ∫ b in Ioi (0:ℝ), deriv (fun b => φ (k / b)) b * ξ b
      = ∫ k in Ioi (0:ℝ), ∫ b in Ioi (0:ℝ), F k b := integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∫ b in Ioi (0:ℝ), ∫ k in Ioi (0:ℝ), F k b := integral_integral_swap hint
    _ = ∫ b in Ioi (0:ℝ), (∫ u in Ioi (0:ℝ), φ u) * ξ b :=
        setIntegral_congr_fun measurableSet_Ioi fun b (hb : 0 < b) => by
          simp only [hF]
          rw [integral_mul_const, inner_k φ hφ hcs b hb]
    _ = (∫ b in Ioi (0:ℝ), ξ b) * ∫ u in Ioi (0:ℝ), φ u := by
        rw [integral_const_mul, mul_comm]


/-- (3.13) from the spectral-shift formula (3.10), taken as a hypothesis for each momentum:
if `T(k) = ∫₀^∞ (d/db) φ(k/b) ξ(b) db` for `k > 0` (this is (3.10) for `f_k(b) = φ(k/b)`,
with `T(k) = Tr(φ(k D_α) − φ(k D_π))`), `I = ∫₀^∞ ξ` and `c = I/π`, then
`(1/2π) ∫_ℝ T(|k|) dk = c ∫₀^∞ φ`. -/
theorem formula_3_13 (T ξ : ℝ → ℝ) (hξ : IntegrableOn ξ (Ioi 0)) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hcs : HasCompactSupport φ) (I c : ℝ)
    (hI : I = ∫ b in Ioi (0:ℝ), ξ b) (hc : c = I / Real.pi)
    (hT : ∀ k : ℝ, 0 < k → T k = ∫ b in Ioi (0:ℝ), deriv (fun b => φ (k / b)) b * ξ b) :
    1 / (2 * Real.pi) * ∫ k, T |k| = c * ∫ u in Ioi (0:ℝ), φ u := by
  rw [integral_comp_abs, setIntegral_congr_fun measurableSet_Ioi fun k (hk : 0 < k) => hT k hk,
    edge_momentum ξ hξ φ hφ hcs, ← hI, hc]
  have := Real.pi_pos
  field_simp

end SteklovAudit.EdgeMomentum
