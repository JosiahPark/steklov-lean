import Mathlib
import SteklovAudit

/-!
# E5: continuation 35 counterexample, discrete part

Roadmap item E5. For `F(x) = 10x² + x sin(2πx)` and `N(x) = ⌊F(x)⌋`:

* `sin_quarter`: `sin(2π(n + 1/4)) = 1` for `n : ℕ`;
* `floor_excess`: `N(n + 1/4) − 10(n + 1/4)² > (n + 1/4) − 1`, so the excess over `10x²` grows
  linearly along `x = n + 1/4` (the roadmap's `≥ k` is off by a constant: the exact value is
  `n − 5/8`);
* `not_sharp`: `N` does NOT satisfy `HasSharpRealLaw N 10 0` (no law `10L² + o(L)`);
* `hasDerivAt_F`, `deriv_F_pos`: `F' = 20x + sin 2πx + 2πx cos 2πx > 0` on `[1, ∞)`, so `F` is a
  smooth increasing profile with the right leading term.

What this file does NOT prove: the smoothing half of continuation 35 (that the smoothed count of
`N` at one fixed width has the sharp law). So it does not yet show formally that one fixed
smoothing width cannot give the sharp law; it gives the discrete obstruction only. Nothing here
concerns the Steklov operator or the main theorem.
-/

namespace SteklovAudit.FloorCounterexample

open SteklovAudit

/-- The profile `F(x) = 10x² + x sin(2πx)`. -/
noncomputable def F (x : ℝ) : ℝ := 10 * x * x + x * Real.sin (2 * Real.pi * x)

/-- The counting function `N(x) = ⌊F(x)⌋`. -/
noncomputable def Nc (x : ℝ) : ℝ := (⌊F x⌋ : ℝ)

theorem sin_quarter (n : ℕ) : Real.sin (2 * Real.pi * ((n : ℝ) + 1 / 4)) = 1 := by
  have e : 2 * Real.pi * ((n : ℝ) + 1 / 4) = Real.pi / 2 + n * (2 * Real.pi) := by ring
  rw [e]
  first
    | rw [Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
    | rw [(Real.sin_periodic.nat_mul n) (Real.pi / 2), Real.sin_pi_div_two]

theorem floor_excess (n : ℕ) :
    ((n : ℝ) + 1 / 4) - 1 < Nc ((n : ℝ) + 1 / 4) - 10 * ((n : ℝ) + 1 / 4) ^ 2 := by
  have hF : F ((n : ℝ) + 1 / 4) = 10 * ((n : ℝ) + 1 / 4) ^ 2 + ((n : ℝ) + 1 / 4) := by
    unfold F
    rw [sin_quarter]
    ring
  have hfl := Int.sub_one_lt_floor (F ((n : ℝ) + 1 / 4))
  unfold Nc
  rw [hF] at hfl ⊢
  linarith

/-- `⌊10x² + x sin 2πx⌋` is not `10 L² + o(L)`. -/
theorem not_sharp : ¬ HasSharpRealLaw Nc 10 0 := by
  intro h
  obtain ⟨L₀, _, hL⟩ := h (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈L₀⌉₊ + 3 := ⟨_, rfl⟩
  have hc : L₀ ≤ (⌈L₀⌉₊ : ℝ) := Nat.le_ceil L₀
  have hc0 : (0 : ℝ) ≤ (⌈L₀⌉₊ : ℝ) := Nat.cast_nonneg _
  have hcast : (n : ℝ) = (⌈L₀⌉₊ : ℝ) + 3 := by
    first
      | (rw [hn, Nat.cast_add, Nat.cast_ofNat])
      | (rw [hn]; push_cast; ring)
      | (rw [hn]; push_cast)
      | (rw [hn]; norm_num)
  have hx : L₀ ≤ (n : ℝ) + 1 / 4 := by rw [hcast]; linarith
  have hb := hL _ hx
  have he := floor_excess n
  unfold realWeylPolynomial at hb
  have h1 := le_abs_self (Nc ((n : ℝ) + 1 / 4) - (10 * ((n : ℝ) + 1 / 4) ^ 2 + 0 * ((n : ℝ) + 1 / 4)))
  have h3 : (3 : ℝ) ≤ n := by rw [hcast]; linarith
  linarith

/-- `F' = 20x + sin(2πx) + 2πx cos(2πx)`. -/
theorem hasDerivAt_F (x : ℝ) :
    HasDerivAt F (20 * x + Real.sin (2 * Real.pi * x)
      + 2 * Real.pi * x * Real.cos (2 * Real.pi * x)) x := by
  have hA : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hB : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
  have hS := hB.sin
  have hP := hA.mul hS
  have hQ := (hA.const_mul 10).mul hA
  have hT := hQ.add hP
  show HasDerivAt (fun y => 10 * y * y + y * Real.sin (2 * Real.pi * y)) _ x
  convert hT using 1
  try beta_reduce
  first | ring | (simp only []; ring) | (simp; ring)

/-- `F' > 0` on `[1, ∞)`. -/
theorem deriv_F_pos (x : ℝ) (hx : 1 ≤ x) :
    0 < 20 * x + Real.sin (2 * Real.pi * x) + 2 * Real.pi * x * Real.cos (2 * Real.pi * x) := by
  have h1 := Real.neg_one_le_sin (2 * Real.pi * x)
  have h2 := Real.neg_one_le_cos (2 * Real.pi * x)
  have hp := Real.pi_pos
  have h4 := Real.pi_le_four
  have hx0 : 0 ≤ 2 * Real.pi * x := mul_nonneg (by positivity) (by linarith)
  have h3 : 2 * Real.pi * x * (-1) ≤ 2 * Real.pi * x * Real.cos (2 * Real.pi * x) :=
    mul_le_mul_of_nonneg_left h2 hx0
  have h5 : Real.pi * x ≤ 4 * x := mul_le_mul_of_nonneg_right h4 (by linarith)
  nlinarith

end SteklovAudit.FloorCounterexample
