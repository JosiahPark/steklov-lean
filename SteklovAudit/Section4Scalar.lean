import Mathlib

/-!
# Section 4: scalar parts of (4.1), (4.3) and (4.12)

* `stretch_energy_bounds`, `stretch_inverse_bounds`: the scalar side of (4.1). Angular stretching
  multiplies the radial and mass energies by `α/π` and the angular energy by `π/α`; for
  `0 < α < π` the total lies between `α/π` and `π/α` times the flat energy, and the bounds invert.
* `weighted_diag_integrable`: the integral in (4.3), `∫ (1 + p²)^(q-1) dp`, is finite for `q < 1/2`.
* `dyadic_shell_sum`, `inv_le_mul_div_sq`, `resolvent_dyadic_bookkeeping`: the dyadic division
  behind (4.12). Shell masses `≤ M 2^(j+1) k` at distance `≥ 2^j k / 2`, plus a near mass
  `≤ 2 M k` at distance `≥ |y|`, sum to at most `(2 + 16 C₁²) M k / y²` when `|y| ≤ C₁ k`.

What this file does NOT prove: no operator inequality (the infimum over extensions and the
operator monotonicity behind (4.1) are not formalized), no trace bound for `T`, no spectral
measure, and not the bound `μ_θ([0,k]) ≤ C k log(2/k)` of (4.11) for the actual operator.
Everything here is scalar bookkeeping.
-/

namespace SteklovAudit.Section4Scalar

open MeasureTheory

/-- (4.1), energy side: stretched energy `(α/π)(a+b) + (π/α)c` lies between `α/π` and `π/α`
times the flat energy `a+b+c` (radial `a`, mass `b`, angular `c`). -/
theorem stretch_energy_bounds {α a b c : ℝ} (hα : 0 < α) (hαπ : α < Real.pi)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    α / Real.pi * (a + b + c) ≤ α / Real.pi * (a + b) + Real.pi / α * c ∧
      α / Real.pi * (a + b) + Real.pi / α * c ≤ Real.pi / α * (a + b + c) := by
  have h1 : α / Real.pi ≤ 1 := by
    first
      | exact (div_le_one Real.pi_pos).2 hαπ.le
      | exact (div_le_one₀ Real.pi_pos).2 hαπ.le
      | (rw [div_le_iff₀ Real.pi_pos]; linarith)
  have h2 : 1 ≤ Real.pi / α := by
    first
      | exact (one_le_div hα).2 hαπ.le
      | exact (one_le_div₀ hα).2 hαπ.le
      | (rw [le_div_iff₀ hα]; linarith)
  have hle : α / Real.pi ≤ Real.pi / α := h1.trans h2
  have e1 : α / Real.pi * (a + b + c) = α / Real.pi * (a + b) + α / Real.pi * c := by ring
  have e2 : Real.pi / α * (a + b + c) = Real.pi / α * (a + b) + Real.pi / α * c := by ring
  have k1 := mul_le_mul_of_nonneg_right hle hc
  have k2 := mul_le_mul_of_nonneg_right hle (add_nonneg ha hb)
  constructor <;> linarith

/-- (4.1), inverse side: `(α/π) x ≤ y ≤ (π/α) x` with `x > 0` gives the same bounds for `1/y`
against `1/x` (scalar shadow of `(α/π) B₀ ≤ B_α ≤ (π/α) B₀`). -/
theorem stretch_inverse_bounds {α x y : ℝ} (hα : 0 < α) (hαπ : α < Real.pi) (hx : 0 < x)
    (hlo : α / Real.pi * x ≤ y) (hhi : y ≤ Real.pi / α * x) :
    α / Real.pi * (1 / x) ≤ 1 / y ∧ 1 / y ≤ Real.pi / α * (1 / x) := by
  have hpi := Real.pi_pos
  have hpi0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hα0 : α ≠ 0 := hα.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hlo0 : 0 < α / Real.pi * x := by positivity
  have hy : 0 < y := lt_of_lt_of_le hlo0 hlo
  have hhi0 : 0 < Real.pi / α * x := by positivity
  have i1 : 1 / (Real.pi / α * x) ≤ 1 / y := one_div_le_one_div_of_le hy hhi
  have i2 : 1 / y ≤ 1 / (α / Real.pi * x) := one_div_le_one_div_of_le hlo0 hlo
  have e1 : 1 / (Real.pi / α * x) = α / Real.pi * (1 / x) := by
    first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [one_div_mul_eq_div, div_mul_eq_div_div]; ring)
  have e2 : 1 / (α / Real.pi * x) = Real.pi / α * (1 / x) := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  rw [e1] at i1
  rw [e2] at i2
  exact ⟨i1, i2⟩

/-- (4.3): `p ↦ (1 + p²)^(q-1)` is integrable on `ℝ` for `q < 1/2`. -/
theorem weighted_diag_integrable {q : ℝ} (hq : q < 1 / 2) :
    Integrable (fun p : ℝ => (1 + p ^ 2) ^ (q - 1)) := by
  first
    | (have h := integrable_rpow_neg_one_add_sq (show (1 : ℝ) / 2 < 1 - q by linarith)
       refine h.congr (ae_of_all _ fun p => ?_)
       show (1 + p ^ 2) ^ (-(1 - q)) = (1 + p ^ 2) ^ (q - 1)
       congr 1
       ring)
    | (have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 2 * (1 - q) := by
         simp only [Module.finrank_self, Nat.cast_one]
         linarith
       have h : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(2 * (1 - q)) / 2)) volume :=
         integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hr
       refine h.congr (ae_of_all _ fun p => ?_)
       show (1 + ‖p‖ ^ 2) ^ (-(2 * (1 - q)) / 2) = (1 + p ^ 2) ^ (q - 1)
       rw [Real.norm_eq_abs, sq_abs]
       congr 1
       ring)
    | (have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 2 * (1 - q) := by
         simp only [Module.finrank_self, Nat.cast_one]
         linarith
       have h : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(2 * (1 - q)) / 2)) volume :=
         integrable_rpow_neg_one_add_norm_sq hr
       refine h.congr (ae_of_all _ fun p => ?_)
       show (1 + ‖p‖ ^ 2) ^ (-(2 * (1 - q)) / 2) = (1 + p ^ 2) ^ (q - 1)
       rw [Real.norm_eq_abs, sq_abs]
       congr 1
       ring)

/-- (4.3), half-line form used in the paper. -/
theorem weighted_diag_integrableOn {q : ℝ} (hq : q < 1 / 2) :
    IntegrableOn (fun p : ℝ => (1 + p ^ 2) ^ (q - 1)) (Set.Ioi 0) :=
  (weighted_diag_integrable hq).integrableOn

/-- (4.12), dyadic shells: masses `m j ≤ M 2^(j+1) k` at distance `d j ≥ 2^j k / 2` give
`∑ m j / d j² ≤ 16 M / k`. -/
theorem dyadic_shell_sum (n : ℕ) {k M : ℝ} (hk : 0 < k) (hM : 0 ≤ M) (m d : ℕ → ℝ)
    (hm0 : ∀ j, 0 ≤ m j) (hm : ∀ j, m j ≤ M * (2 ^ (j + 1) * k))
    (hd : ∀ j, 2 ^ j * k / 2 ≤ d j) :
    ∑ j ∈ Finset.range n, m j / d j ^ 2 ≤ 16 * M / k := by
  have hterm : ∀ j, m j / d j ^ 2 ≤ 8 * M / k * (1 / 2) ^ j := by
    intro j
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have hdj : 0 < (2 : ℝ) ^ j * k / 2 := by positivity
    have hdj' : 0 < d j := lt_of_lt_of_le hdj (hd j)
    have hsq : ((2 : ℝ) ^ j * k / 2) ^ 2 ≤ d j ^ 2 := by
      nlinarith [hd j, mul_le_mul (hd j) (hd j) hdj.le (hdj.le.trans (hd j))]
    have hnum : 0 ≤ M * (2 ^ (j + 1) * k) := mul_nonneg hM (by positivity)
    have hden : 0 < ((2 : ℝ) ^ j * k / 2) ^ 2 := by positivity
    have s1 : m j / d j ^ 2 ≤ m j / ((2 : ℝ) ^ j * k / 2) ^ 2 := by
      first
        | exact div_le_div_of_nonneg_left (hm0 j) hden hsq
        | (gcongr; exact hd j)
        | (apply div_le_div_of_nonneg_left (hm0 j) hden hsq)
    have s2 : m j / ((2 : ℝ) ^ j * k / 2) ^ 2 ≤ M * (2 ^ (j + 1) * k) / ((2 : ℝ) ^ j * k / 2) ^ 2 := by
      first
        | exact div_le_div_of_nonneg_right (hm j) hden.le
        | (gcongr; exact hm j)
    have hk0 : k ≠ 0 := hk.ne'
    have hp0 : (2 : ℝ) ^ j ≠ 0 := hp.ne'
    have s3 : M * (2 ^ (j + 1) * k) / ((2 : ℝ) ^ j * k / 2) ^ 2 = 8 * M / k * (1 / 2) ^ j := by
      rw [pow_succ, one_div_pow]
      first
        | (field_simp; ring)
        | (field_simp; done)
    linarith
  have hgeom : ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j ≤ 2 := sum_geometric_two_le n
  have hc : 0 ≤ 8 * M / k := div_nonneg (by linarith) hk.le
  calc ∑ j ∈ Finset.range n, m j / d j ^ 2
      ≤ ∑ j ∈ Finset.range n, 8 * M / k * (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = 8 * M / k * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ 8 * M / k * 2 := mul_le_mul_of_nonneg_left hgeom hc
    _ = 16 * M / k := by ring

/-- (4.12), converting `1/k` into `k / y²` when `|y| ≤ C₁ k`. -/
theorem inv_le_mul_div_sq {k y C₁ : ℝ} (hk : 0 < k) (hy : 0 < |y|) (hyk : |y| ≤ C₁ * k) :
    1 / k ≤ C₁ ^ 2 * k / y ^ 2 := by
  have hy2 : 0 < y ^ 2 := by
    have h := pow_pos hy 2
    rwa [sq_abs] at h
  have hsq : y ^ 2 ≤ (C₁ * k) ^ 2 := by
    rw [← sq_abs y]
    nlinarith [mul_le_mul hyk hyk (abs_nonneg y) (le_trans (abs_nonneg y) hyk), abs_nonneg y]
  first
    | (rw [div_le_div_iff₀ hk hy2]; nlinarith)
    | (rw [div_le_div_iff hk hy2]; nlinarith)
    | (rw [div_le_div_iff_of_pos hk hy2]; nlinarith)

/-- (4.12), assembled: near mass `m0 ≤ 2 M k` at distance `≥ |y|` plus the dyadic shells give
`m0 / y² + ∑ m j / d j² ≤ (2 + 16 C₁²) M k / y²`. With `M = C log(2/k)` this is the shape
`C k log(2/k) / y²` of (4.12). -/
theorem resolvent_dyadic_bookkeeping (n : ℕ) {k M y C₁ m0 : ℝ} (hk : 0 < k) (hM : 0 ≤ M)
    (hy : 0 < |y|) (hyk : |y| ≤ C₁ * k) (hm00 : 0 ≤ m0) (hm0 : m0 ≤ 2 * M * k)
    (m d : ℕ → ℝ) (hmj0 : ∀ j, 0 ≤ m j) (hm : ∀ j, m j ≤ M * (2 ^ (j + 1) * k))
    (hd : ∀ j, 2 ^ j * k / 2 ≤ d j) :
    m0 / y ^ 2 + ∑ j ∈ Finset.range n, m j / d j ^ 2 ≤ (2 + 16 * C₁ ^ 2) * M * k / y ^ 2 := by
  have hy2 : 0 < y ^ 2 := by
    have h := pow_pos hy 2
    rwa [sq_abs] at h
  have a1 : m0 / y ^ 2 ≤ 2 * M * k / y ^ 2 := by
    first
      | exact div_le_div_of_nonneg_right hm0 hy2.le
      | (gcongr)
  have a2 := dyadic_shell_sum n hk hM m d hmj0 hm hd
  have a3 : 16 * M / k ≤ 16 * M * (C₁ ^ 2 * k / y ^ 2) := by
    have h := inv_le_mul_div_sq hk hy hyk
    have h16 : 0 ≤ 16 * M := by linarith
    calc 16 * M / k = 16 * M * (1 / k) := by ring
      _ ≤ 16 * M * (C₁ ^ 2 * k / y ^ 2) := mul_le_mul_of_nonneg_left h h16
  have e : (2 + 16 * C₁ ^ 2) * M * k / y ^ 2
      = 2 * M * k / y ^ 2 + 16 * M * (C₁ ^ 2 * k / y ^ 2) := by ring
  rw [e]
  linarith

end SteklovAudit.Section4Scalar
