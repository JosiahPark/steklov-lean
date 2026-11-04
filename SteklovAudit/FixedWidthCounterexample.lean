import Mathlib
import SteklovAudit

/-!
# E11: continuation 35 counterexample, discrete part (every `B`, monotone `N`)

Roadmap item E11. It strengthens E5 (`FloorCounterexample.not_sharp`, the case `B = 0`) to every
`B` and adds that `N` is monotone on `[1, ∞)`. Let `F(x) = 10x² + x sin(2πx)` and `N(x) = ⌊F(x)⌋`. Proved here:

* `sin_quarter`, `sin_three_quarter`: `sin(2π(k + 1/4)) = 1`, `sin(2π(k + 3/4)) = −1` for `k ∈ ℕ`;
* `N_quarter_lower`: `N(k + 1/4) − 10(k + 1/4)² ≥ (k + 1/4) − 1`;
* `N_three_quarter_upper`: `N(k + 3/4) − 10(k + 3/4)² ≤ −(k + 3/4)`;
* `not_sharp_law`: for every `B`, `N` does NOT satisfy `HasSharpRealLaw N 10 B`, i.e. `N` is not
  `10L² + BL + o(L)`: its deviation from `10L²` oscillates between about `+L` and `−L`;
* `hasDerivAt_F`, `deriv_F_pos`, `F_strictMonoOn`, `N_monotoneOn`: `F' > 0` on `[1, ∞)`, so `F` is
  strictly increasing there and `N` is monotone there, like a genuine counting function.

Correction to the roadmap wording: at `x = k + 1/4` one has `F(x) = 10k² + 6k + 7/8`, so
`N(x) − 10x² = k − 5/8`, which is `≥ k − 1` but not `≥ k`. The bound proved is `≥ x − 1`.

So a monotone function can fail the sharp two-term law by a full `±L`. Together with
continuation 35's smoothing computation (NOT formalized here: that the fixed-width smoothing of `N`
does satisfy the law), this is why E2 needs smoothing widths `σ_n → 0`. What this file does NOT
prove: the smoothing half of continuation 35; anything about the Steklov operator; the main theorem.
-/

namespace SteklovAudit.FixedWidthCounterexample

open SteklovAudit

/-- `F(x) = 10x² + x sin(2πx)`. -/
noncomputable def F (x : ℝ) : ℝ := 10 * x ^ 2 + x * Real.sin (2 * Real.pi * x)

/-- `N(x) = ⌊F(x)⌋`. -/
noncomputable def N (x : ℝ) : ℝ := (Int.floor (F x) : ℝ)

theorem sin_quarter (k : ℕ) : Real.sin (2 * Real.pi * ((k : ℝ) + 1 / 4)) = 1 := by
  have e : 2 * Real.pi * ((k : ℝ) + 1 / 4) = Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by ring
  rw [e, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]

theorem sin_three_quarter (k : ℕ) : Real.sin (2 * Real.pi * ((k : ℝ) + 3 / 4)) = -1 := by
  have e : 2 * Real.pi * ((k : ℝ) + 3 / 4) = (Real.pi / 2 + Real.pi) + (k : ℝ) * (2 * Real.pi) := by
    ring
  rw [e, Real.sin_add_nat_mul_two_pi, Real.sin_add_pi, Real.sin_pi_div_two]

theorem N_quarter_lower (k : ℕ) :
    ((k : ℝ) + 1 / 4) - 1 ≤ N ((k : ℝ) + 1 / 4) - 10 * ((k : ℝ) + 1 / 4) ^ 2 := by
  have hF : F ((k : ℝ) + 1 / 4) = 10 * ((k : ℝ) + 1 / 4) ^ 2 + ((k : ℝ) + 1 / 4) := by
    unfold F
    rw [sin_quarter]
    ring
  have h := Int.sub_one_lt_floor (F ((k : ℝ) + 1 / 4))
  unfold N
  rw [hF] at h ⊢
  linarith

theorem N_three_quarter_upper (k : ℕ) :
    N ((k : ℝ) + 3 / 4) - 10 * ((k : ℝ) + 3 / 4) ^ 2 ≤ -((k : ℝ) + 3 / 4) := by
  have hF : F ((k : ℝ) + 3 / 4) = 10 * ((k : ℝ) + 3 / 4) ^ 2 - ((k : ℝ) + 3 / 4) := by
    unfold F
    rw [sin_three_quarter]
    ring
  have h := Int.floor_le (F ((k : ℝ) + 3 / 4))
  unfold N
  rw [hF] at h ⊢
  linarith

/-- E11. `N` is not `10L² + BL + o(L)` for any `B`. -/
theorem not_sharp_law (B : ℝ) : ¬ HasSharpRealLaw N 10 B := by
  intro h
  obtain ⟨L₀, hL₀, hL⟩ := h (1 / 4) (by norm_num)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, L₀ + 1 ≤ (k : ℝ) :=
    ⟨⌈L₀⌉₊ + 1, by push_cast; linarith [Nat.le_ceil L₀]⟩
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have hx1 : L₀ ≤ (k : ℝ) + 1 / 4 := by linarith
  have hx3 : L₀ ≤ (k : ℝ) + 3 / 4 := by linarith
  have e1 := abs_le.mp (hL _ hx1)
  have e3 := abs_le.mp (hL _ hx3)
  have q1 := N_quarter_lower k
  have q3 := N_three_quarter_upper k
  unfold realWeylPolynomial at e1 e3
  -- from x = k + 3/4: B ≤ -3/4
  have hB : B ≤ -3 / 4 := by
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < (B + 3 / 4) * ((k : ℝ) + 3 / 4) := mul_pos (by linarith) (by linarith)
    nlinarith [e3.1, q3]
  -- from x = k + 1/4: (3/4 - B) (k + 1/4) ≤ 1
  have hup : (3 / 4 - B) * ((k : ℝ) + 1 / 4) ≤ 1 := by nlinarith [e1.2, q1]
  have hbig : (3 / 2 : ℝ) * ((k : ℝ) + 1 / 4) ≤ (3 / 4 - B) * ((k : ℝ) + 1 / 4) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- The derivative of `F`. -/
theorem hasDerivAt_F (x : ℝ) :
    HasDerivAt F (20 * x + Real.sin (2 * Real.pi * x)
      + x * (Real.cos (2 * Real.pi * x) * (2 * Real.pi))) x := by
  have h1 : HasDerivAt (fun y : ℝ => 10 * y ^ 2) (10 * (2 * x)) x := by
    convert (hasDerivAt_pow 2 x).const_mul (10 : ℝ) using 1 <;> norm_num
  have h2 : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) x := by
    convert (hasDerivAt_id' x).const_mul (2 * Real.pi) using 1 <;> ring
  have h3 : HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * y))
      (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) x := h2.sin
  have h4 : HasDerivAt (fun y : ℝ => y * Real.sin (2 * Real.pi * y))
      (1 * Real.sin (2 * Real.pi * x) + x * (Real.cos (2 * Real.pi * x) * (2 * Real.pi))) x :=
    (hasDerivAt_id' x).mul h3
  have h5 := h1.add h4
  show HasDerivAt (fun y : ℝ => 10 * y ^ 2 + y * Real.sin (2 * Real.pi * y)) _ x
  convert h5 using 1
  ring

/-- `F' > 0` on `[1, ∞)`. -/
theorem deriv_F_pos (x : ℝ) (hx : 1 ≤ x) :
    0 < 20 * x + Real.sin (2 * Real.pi * x) + x * (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) := by
  have hs := Real.neg_one_le_sin (2 * Real.pi * x)
  have hc := Real.neg_one_le_cos (2 * Real.pi * x)
  have hpi := Real.pi_le_four
  have hx0 : 0 ≤ x := by linarith
  have hprod : x * (2 * Real.pi) * (-1) ≤ x * (2 * Real.pi) * Real.cos (2 * Real.pi * x) :=
    mul_le_mul_of_nonneg_left hc (mul_nonneg hx0 (by linarith [Real.pi_pos]))
  have hx8 : x * (2 * Real.pi) ≤ x * 8 := mul_le_mul_of_nonneg_left (by linarith) hx0
  linarith

/-- `F` is strictly increasing on `[1, ∞)`. -/
theorem F_strictMonoOn : StrictMonoOn F (Set.Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · exact fun x _ => (hasDerivAt_F x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_F x).deriv]
    exact deriv_F_pos x (le_of_lt hx)

/-- `N = ⌊F⌋` is monotone on `[1, ∞)`. -/
theorem N_monotoneOn : MonotoneOn N (Set.Ici 1) := by
  intro x hx y hy hxy
  unfold N
  exact_mod_cast Int.floor_mono (F_strictMonoOn.monotoneOn hx hy hxy)

end SteklovAudit.FixedWidthCounterexample
