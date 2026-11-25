import Mathlib
import SteklovAudit.WindowLocalMassBounded

/-!
# Definition check for the bounded-defect window route (roadmap item G157)

Row 3 of the priority table (abstract cumulative budget refinement).

`WindowLocalMassBounded.littleO_of_window_bounded_defect` (G146) assumes, for every window `T > 0`,
eventually `|r L| ≤ C L / T + K T ε₀ √(Mloc L)`. This file checks that this hypothesis is not vacuous:
it holds with `C = K = ε₀ = Mloc = 1` (so `ε₀ > 0`, a defect that is bounded but does NOT vanish) for
the NONZERO remainder `r L = √(max L 0)`.

* `window_witness_bound`: the window hypothesis of G146 holds for `wr L = √(max L 0)`.
* `window_witness_ne`: `wr L ≠ 0` for `L > 0`.
* `window_bounded_nonvacuous`: the conclusion of G146 for this `wr` (`wr = o(L)` in `η`-form).

What this file does NOT prove: the window bound for the actual localized tetrahedron–wedge error, the
local spectral mass bound `O(L)`, the boundedness of the HS defect (Lemma 7.1′ / (7.2)), the Lipschitz
constant `O(T)` of the window, Proposition 7.3, (7.29), H5, or Theorem 1.3 / 11.1. Everything here is
real analysis of one explicit scalar function.
-/

namespace SteklovAudit.WindowBoundedNonvacuous

open Filter

/-- The witness remainder `√(max L 0)`. -/
noncomputable def wr (L : ℝ) : ℝ := Real.sqrt (max L 0)

/-- **G157.** The window hypothesis of `littleO_of_window_bounded_defect` holds for `wr` with
`C = K = ε₀ = Mloc = 1`. -/
theorem window_witness_bound : ∀ T : ℝ, 0 < T → ∀ᶠ L in atTop,
    |wr L| ≤ 1 * L / T + 1 * T * 1 * Real.sqrt (1 * L) := by
  intro T hT
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  have hmax : max L 0 = L := max_eq_left (by linarith)
  have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt L := by nlinarith
  have hsL : Real.sqrt L ≤ L := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 hs1)]
  have key : Real.sqrt L ≤ L / T + T * Real.sqrt L := by
    rcases le_or_lt 1 T with h | h
    · have h1 : 0 ≤ L / T := div_nonneg (by linarith) hT.le
      nlinarith [mul_nonneg (sub_nonneg.2 h) hs0]
    · have h1 : L ≤ L / T := by
        have hLT : L * T ≤ L := by nlinarith
        first
          | exact (le_div_iff₀ hT).2 hLT
          | exact (le_div_iff hT).2 hLT
      have h2 : 0 ≤ T * Real.sqrt L := mul_nonneg hT.le hs0
      linarith
  show |Real.sqrt (max L 0)| ≤ 1 * L / T + 1 * T * 1 * Real.sqrt (1 * L)
  rw [hmax, abs_of_nonneg hs0]
  calc Real.sqrt L ≤ L / T + T * Real.sqrt L := key
    _ = 1 * L / T + 1 * T * 1 * Real.sqrt (1 * L) := by
      first
        | (rw [one_mul L]; ring)
        | simp
        | (simp only [one_mul, mul_one])

/-- **G157.** The witness remainder is nonzero for `L > 0`. -/
theorem window_witness_ne : ∀ L : ℝ, 0 < L → wr L ≠ 0 := by
  intro L hL
  show Real.sqrt (max L 0) ≠ 0
  rw [max_eq_left hL.le]
  exact ne_of_gt (Real.sqrt_pos.mpr hL)

/-- **G157.** G146 applied to the witness: `wr = o(L)` in `η`-form, although `wr ≠ 0` and the defect
`ε₀ = 1` does not vanish. -/
theorem window_bounded_nonvacuous :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |wr L| ≤ η * L :=
  SteklovAudit.WindowLocalMassBounded.littleO_of_window_bounded_defect wr 1 1 1 1
    zero_le_one zero_le_one zero_le_one zero_le_one window_witness_bound

end SteklovAudit.WindowBoundedNonvacuous
