import Mathlib

/-!
# Scalar reductions behind the fixed-time model edge law (7.38) and (7.45) (roadmap item G134)

The proposition "fixed-time model law" (7.38) gives the wedge count
`N^S_{qθ_γ,α₀}(L) = L²/(4π) ∫ q²θ_γ² dS + c_{α₀} ‖q‖₂² L + o_γ(L)`, and (7.45) carries it to the
tetrahedron. Its proof mixes operator theory (the weighted trace ideal, (7.39), the face law of
the face subsection, upper locality) with scalar steps. This file proves the scalar steps without any continuum
operator:

* `k_integral`: (7.40), `∫₀^∞ (w k / b²) e^{−w k / b} dk = 1 / w` for real `w, b > 0`.
* `pertrace_scalar`: the scalar part of (7.41): integrating (7.40) against a spectral shift density
  `ξ` gives `(∫ ξ) / w`; with `∫ ξ = π c_α` this is the `c_α / w` law (normalizations as in the paper).
* `smoothed_ramp`, `smoothed_ramp_sq`, `smoothed_ramp_neg`: the cumulative primitives `L₊ * ρ = L` and
  `L₊² * ρ = L²` for large `L`, and `L₊ * ρ = 0` for very negative `L` (the zero primitive constant),
  for a kernel `ρ` with `∫ ρ = 1`, vanishing first (and second) moments and support in `[−R, R]`.
  The paper's `ρ_S` is Schwartz rather than compactly supported and gives `O(L^{−N})` instead of an
  exact identity; the compact-support version is a stand-in for that step.
* `dyadic_sum_closed`, `dyadic_sum_le`: the far-exterior sum `∑_j R_j^{−2}` with `R_j = 2^j R₀` is
  at most `4 / (3 R₀²)`, the constant in the bound `C S R₀^{−2}` for (7.43).
* `littleO_of_bounded`: a bounded remainder (such as `G^S_far`) is `o(L)`; (7.38) needs only this,
  not the sharper `o(1)` of (7.43).
* `model_law_of_decomposition`: the assembly. If the wedge-minus-flat count has the form (7.44)
  minus finitely many annulus terms, the flat count is `L²/(4π) ∫ q²θ² + o(L)`, the smoothed ramp is
  `L + o(L)`, `G_far = o(L)` and each annulus term is `o(L)`, then (7.38) holds with an `o(L)`
  remainder. The finite index set is fixed (fixed `γ`); nothing is claimed uniformly in `γ`.

What this file does NOT prove: the trace-ideal bound (7.39), the spectral shift trace formula and
`∫ ξ = Tr V = π c_α`, the per-unit-length trace (7.41) as an operator identity, the face law and
the nonreturn lemma on the annuli, the bound (7.42) on `F_j`, (7.44) itself, Proposition 7.3 / (7.29), the
transfer to (7.45), H5, or Theorem 1.3 / 11.1. Every hypothesis of `model_law_of_decomposition` is
a named input.
-/

namespace SteklovAudit.ModelEdgeLawReduction

open MeasureTheory Set Filter Asymptotics

/-- **G134.** (7.40): `∫₀^∞ (w k / b²) e^{−w k / b} dk = 1 / w` for `w, b > 0`. -/
theorem k_integral (w b : ℝ) (hw : 0 < w) (hb : 0 < b) :
    ∫ k in Ioi (0:ℝ), w * k / b ^ 2 * Real.exp (-(w * k / b)) = 1 / w := by
  have hr : 0 < w / b := div_pos hw hb
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := w / b) two_pos hr
  have key' : ∫ k in Ioi (0:ℝ), w * k / b ^ 2 * Real.exp (-(w * k / b)) =
      (w / b ^ 2) * ((1 / (w / b)) ^ (2:ℝ) * Real.Gamma 2) := by
    rw [← key, ← MeasureTheory.integral_const_mul]
    congr 1
    funext k
    rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one, show w / b * k = w * k / b by ring]
    ring
  rw [key']
  have hG : Real.Gamma 2 = 1 := by
    first
      | exact Real.Gamma_two
      | simpa using Real.Gamma_nat_eq_factorial 1
  rw [hG, Real.rpow_two]
  have hb0 : b ≠ 0 := hb.ne'
  have hw0 : w ≠ 0 := hw.ne'
  first
    | (field_simp; ring)
    | field_simp

/-- **G134.** Scalar part of (7.41): integrating (7.40) against a density `ξ` on `(0, ∞)` gives
`(∫ ξ) / w`. -/
theorem pertrace_scalar (ξ : ℝ → ℝ) (w : ℝ) (hw : 0 < w) :
    ∫ b in Ioi (0:ℝ), ξ b * (∫ k in Ioi (0:ℝ), w * k / b ^ 2 * Real.exp (-(w * k / b))) =
      (∫ b in Ioi (0:ℝ), ξ b) / w := by
  have h : ∀ b ∈ Ioi (0:ℝ),
      ξ b * (∫ k in Ioi (0:ℝ), w * k / b ^ 2 * Real.exp (-(w * k / b))) = ξ b * (1 / w) := by
    intro b hb
    rw [k_integral w b hw hb]
  have hc : ∫ b in Ioi (0:ℝ), ξ b * (∫ k in Ioi (0:ℝ), w * k / b ^ 2 * Real.exp (-(w * k / b))) =
      ∫ b in Ioi (0:ℝ), ξ b * (1 / w) := by
    first
      | exact setIntegral_congr_fun measurableSet_Ioi h
      | exact setIntegral_congr measurableSet_Ioi h
      | exact setIntegral_congr_ae measurableSet_Ioi (Eventually.of_forall h)
  rw [hc, MeasureTheory.integral_mul_const]
  ring

/-- **G134.** Cumulative primitive at positive energy: for a kernel with `∫ ρ = 1`, `∫ u ρ = 0` and
support in `[−R, R]`, `∫ (L − u)₊ ρ(u) du = L` for `L ≥ R`. -/
theorem smoothed_ramp (ρ : ℝ → ℝ) (R L : ℝ) (hρ : Integrable ρ)
    (hm : Integrable (fun u => u * ρ u)) (h0 : ∫ u, ρ u = 1) (h1 : ∫ u, u * ρ u = 0)
    (hsupp : ∀ u, R < |u| → ρ u = 0) (hL : R ≤ L) :
    ∫ u, max (L - u) 0 * ρ u = L := by
  have e : ∀ u, max (L - u) 0 * ρ u = L * ρ u - u * ρ u := by
    intro u
    by_cases hu : R < |u|
    · rw [hsupp u hu]
      ring
    · push_neg at hu
      have hle : u ≤ L := le_trans (le_abs_self u) (hu.trans hL)
      rw [max_eq_left (by linarith)]
      ring
  simp_rw [e]
  rw [integral_sub (hρ.const_mul L) hm, MeasureTheory.integral_const_mul, h0, h1]
  ring

/-- **G134.** The same for the square: with also `∫ u² ρ = 0`, `∫ (L − u)₊² ρ(u) du = L²` for
`L ≥ R` (the flat count `L₊² ∫ q²θ² / (4π)` after smoothing). -/
theorem smoothed_ramp_sq (ρ : ℝ → ℝ) (R L : ℝ) (hρ : Integrable ρ)
    (hm : Integrable (fun u => u * ρ u)) (hm2 : Integrable (fun u => u ^ 2 * ρ u))
    (h0 : ∫ u, ρ u = 1) (h1 : ∫ u, u * ρ u = 0) (h2 : ∫ u, u ^ 2 * ρ u = 0)
    (hsupp : ∀ u, R < |u| → ρ u = 0) (hL : R ≤ L) :
    ∫ u, (max (L - u) 0) ^ 2 * ρ u = L ^ 2 := by
  have e : ∀ u, (max (L - u) 0) ^ 2 * ρ u =
      (L ^ 2 * ρ u - (2 * L) * (u * ρ u)) + u ^ 2 * ρ u := by
    intro u
    by_cases hu : R < |u|
    · rw [hsupp u hu]
      ring
    · push_neg at hu
      have hle : u ≤ L := le_trans (le_abs_self u) (hu.trans hL)
      rw [max_eq_left (by linarith)]
      ring
  have i1 : Integrable (fun u => L ^ 2 * ρ u) := hρ.const_mul _
  have i2 : Integrable (fun u => (2 * L) * (u * ρ u)) := hm.const_mul _
  have i12 : Integrable (fun u => L ^ 2 * ρ u - (2 * L) * (u * ρ u)) := i1.sub i2
  simp_rw [e]
  rw [integral_add i12 hm2, integral_sub i1 i2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, h0, h1, h2]
  ring

/-- **G134.** Zero primitive constant: for `L ≤ −R` the smoothed ramp vanishes. -/
theorem smoothed_ramp_neg (ρ : ℝ → ℝ) (R L : ℝ) (hsupp : ∀ u, R < |u| → ρ u = 0)
    (hL : L ≤ -R) :
    ∫ u, max (L - u) 0 * ρ u = 0 := by
  have e : ∀ u, max (L - u) 0 * ρ u = 0 := by
    intro u
    by_cases hu : R < |u|
    · rw [hsupp u hu, mul_zero]
    · push_neg at hu
      have hle : -R ≤ u := by
        have := neg_abs_le u
        linarith
      rw [max_eq_right (by linarith), zero_mul]
  simp_rw [e]
  simp

/-- **G134.** Closed form of the dyadic far-exterior sum: `∑_{j<N} (2^j R₀)^{−2} = 4/(3R₀²) (1 − 4^{−N})`,
written with `(2^N)²`. -/
theorem dyadic_sum_closed (R₀ : ℝ) (hR : 0 < R₀) (N : ℕ) :
    ∑ j ∈ Finset.range N, 1 / ((2:ℝ) ^ j * R₀) ^ 2 =
      4 / (3 * R₀ ^ 2) * (1 - 1 / ((2:ℝ) ^ N) ^ 2) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : (2:ℝ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
    have hR0 : R₀ ≠ 0 := hR.ne'
    field_simp
    ring

/-- **G134.** The dyadic sum is at most `4 / (3 R₀²)`, uniformly in the number of annuli. -/
theorem dyadic_sum_le (R₀ : ℝ) (hR : 0 < R₀) (N : ℕ) :
    ∑ j ∈ Finset.range N, 1 / ((2:ℝ) ^ j * R₀) ^ 2 ≤ 4 / (3 * R₀ ^ 2) := by
  rw [dyadic_sum_closed R₀ hR N]
  have hpos : 0 < 4 / (3 * R₀ ^ 2) := by positivity
  have hx : 0 ≤ 1 / ((2:ℝ) ^ N) ^ 2 := by positivity
  exact mul_le_of_le_one_right hpos.le (by linarith)

/-- **G134.** A bounded remainder is `o(L)`. -/
theorem littleO_of_bounded (G : ℝ → ℝ) (B : ℝ) (h : ∀ L, |G L| ≤ B) :
    G =o[atTop] (fun L : ℝ => L) := by
  have h1 : G =O[atTop] (fun _ : ℝ => B) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun L => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
      exact (h L).trans (le_abs_self B))
  exact h1.trans_isLittleO (isLittleO_const_id_atTop B)

/-- **G134.** Assembly of (7.38) from the decomposition (7.44). For a fixed finite family `s` of
compact face annuli (fixed `γ`): if
`N_wedge − N_flat = c ‖q‖² (L₊ * ρ_S) − G_far − ∑_{i ∈ s} A_i`, the flat count is
`L²/(4π) I + o(L)`, the smoothed ramp is `L + o(L)`, `G_far = o(L)` and every `A_i = o(L)`, then
`N_wedge = L²/(4π) I + c ‖q‖² L + o(L)`. All five are hypotheses. -/
theorem model_law_of_decomposition {ι : Type*} (s : Finset ι) (Nw Nf P G : ℝ → ℝ)
    (A : ι → ℝ → ℝ) (c Q I : ℝ)
    (hdiff : ∀ L, Nw L - Nf L = c * Q * P L - G L - ∑ i ∈ s, A i L)
    (hflat : (fun L => Nf L - L ^ 2 / (4 * Real.pi) * I) =o[atTop] (fun L : ℝ => L))
    (hP : (fun L => P L - L) =o[atTop] (fun L : ℝ => L))
    (hG : G =o[atTop] (fun L : ℝ => L))
    (hA : ∀ i ∈ s, A i =o[atTop] (fun L : ℝ => L)) :
    (fun L => Nw L - (L ^ 2 / (4 * Real.pi) * I + c * Q * L)) =o[atTop] (fun L : ℝ => L) := by
  have e : (fun L => Nw L - (L ^ 2 / (4 * Real.pi) * I + c * Q * L)) =
      fun L => (Nf L - L ^ 2 / (4 * Real.pi) * I) + c * Q * (P L - L) - G L -
        ∑ i ∈ s, A i L := by
    funext L
    linear_combination hdiff L
  have hfun : (∑ i ∈ s, A i) = fun L => ∑ i ∈ s, A i L := by
    funext L
    simp [Finset.sum_apply]
  have hsum : (fun L => ∑ i ∈ s, A i L) =o[atTop] (fun L : ℝ => L) := by
    first
      | (rw [← hfun]; exact IsLittleO.sum hA)
      | exact hfun ▸ IsLittleO.sum hA
      | simpa [Finset.sum_apply] using IsLittleO.sum hA
  rw [e]
  exact ((hflat.add (hP.const_mul_left (c * Q))).sub hG).sub hsum

/-- Non-vacuity of `model_law_of_decomposition`: exact flat count, exact ramp, no far term and no
annuli satisfy every hypothesis. -/
theorem model_law_nonvacuous (c Q I : ℝ) :
    (fun L : ℝ => (L ^ 2 / (4 * Real.pi) * I + c * Q * L) -
      (L ^ 2 / (4 * Real.pi) * I + c * Q * L)) =o[atTop] (fun L : ℝ => L) :=
  model_law_of_decomposition (∅ : Finset Unit)
    (fun L => L ^ 2 / (4 * Real.pi) * I + c * Q * L) (fun L => L ^ 2 / (4 * Real.pi) * I)
    (fun L => L) (fun _ => 0) (fun _ _ => 0) c Q I
    (fun L => by simp)
    (by simpa using (isLittleO_zero (fun L : ℝ => L) atTop))
    (by simpa using (isLittleO_zero (fun L : ℝ => L) atTop))
    (isLittleO_zero _ _)
    (fun i hi => by simp at hi)

end SteklovAudit.ModelEdgeLawReduction
