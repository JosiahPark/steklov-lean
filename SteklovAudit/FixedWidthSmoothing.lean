import Mathlib
import SteklovAudit.FloorCounterexample
import SteklovAudit.FixedScaleTauberian
import SteklovAudit.FixedWidthCounterexample

/-!
# E9: smoothing half of continuation 35

Roadmap item E9. For the floor counterexample `Nc(x) = ⌊10x² + x sin 2πx⌋` of E5
(`FloorCounterexample`), take the two-point kernel with nodes `±1/4`, weights `1/2`, at the fixed
width `σ = 1`: `S(x) = (Nc(x − 1/4) + Nc(x + 1/4)) / 2` (this is `FixedScaleTauberian.smooth`).
Proved here:

* `F_pair`: `F(x − 1/4) + F(x + 1/4) = 20x² + 5/4 + cos(2πx)/2` (the oscillation `x sin 2πx` cancels
  to a bounded term);
* `smooth_close`: `|S(x) − 10x²| ≤ 2` for all `x`;
* `smoothed_sharp_law`: `S` has the sharp law `10L² + 0·L + o(L)`;
* `fixed_width_insufficient`: `S` has the sharp law while `Nc` has it for NO linear coefficient `B`
  (via `Nc_eq` and E11 `FixedWidthCounterexample.not_sharp_law`).

So a sharp law for one fixed-width smoothing says nothing about the count itself; E2
(`sharp_law_of_shrinking_scales`) needs widths `σ_n → 0`. What this file does NOT prove: anything
about the Steklov operator; the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.FixedWidthSmoothing

open SteklovAudit SteklovAudit.FloorCounterexample SteklovAudit.FixedScaleTauberian

/-- Weights `1/2, 1/2`. -/
noncomputable def w2 : Fin 2 → ℝ := fun _ => 1 / 2

/-- Nodes `1/4, −1/4`. -/
noncomputable def t2 : Fin 2 → ℝ := ![1 / 4, -1 / 4]

theorem smooth_eq (x : ℝ) :
    smooth w2 t2 1 Nc x = (Nc (x - 1 / 4) + Nc (x + 1 / 4)) / 2 := by
  unfold smooth
  rw [Fin.sum_univ_two]
  have e0 : t2 0 = 1 / 4 := rfl
  have e1 : t2 1 = -1 / 4 := rfl
  have f0 : w2 0 = 1 / 2 := rfl
  have f1 : w2 1 = 1 / 2 := rfl
  rw [e0, e1, f0, f1, show x - 1 * (1 / 4 : ℝ) = x - 1 / 4 by ring,
    show x - 1 * (-1 / 4 : ℝ) = x + 1 / 4 by ring]
  ring

theorem F_pair (x : ℝ) :
    F (x - 1 / 4) + F (x + 1 / 4) = 20 * x ^ 2 + 5 / 4 + Real.cos (2 * Real.pi * x) / 2 := by
  unfold F
  have hs1 : Real.sin (2 * Real.pi * (x - 1 / 4)) = -Real.cos (2 * Real.pi * x) := by
    rw [show 2 * Real.pi * (x - 1 / 4) = 2 * Real.pi * x - Real.pi / 2 by ring,
      Real.sin_sub_pi_div_two]
  have hs2 : Real.sin (2 * Real.pi * (x + 1 / 4)) = Real.cos (2 * Real.pi * x) := by
    rw [show 2 * Real.pi * (x + 1 / 4) = 2 * Real.pi * x + Real.pi / 2 by ring,
      Real.sin_add_pi_div_two]
  rw [hs1, hs2]
  ring

theorem smooth_close (x : ℝ) : |smooth w2 t2 1 Nc x - 10 * x ^ 2| ≤ 2 := by
  rw [smooth_eq]
  have a1 := Int.floor_le (F (x - 1 / 4))
  have a2 := Int.floor_le (F (x + 1 / 4))
  have b1 := Int.sub_one_lt_floor (F (x - 1 / 4))
  have b2 := Int.sub_one_lt_floor (F (x + 1 / 4))
  have hp := F_pair x
  have hc1 := Real.cos_le_one (2 * Real.pi * x)
  have hc2 := Real.neg_one_le_cos (2 * Real.pi * x)
  unfold Nc
  rw [abs_le]
  constructor <;> linarith

/-- E9. The fixed-width smoothing has the sharp law `10L² + o(L)`. -/
theorem smoothed_sharp_law : HasSharpRealLaw (smooth w2 t2 1 Nc) 10 0 := by
  intro δ hδ
  refine ⟨2 / δ, (div_pos two_pos hδ).le, fun L hL => ?_⟩
  have h := smooth_close L
  have h2 : 2 ≤ L * δ := (div_le_iff₀ hδ).mp hL
  unfold realWeylPolynomial
  rw [show (10 : ℝ) * L ^ 2 + 0 * L = 10 * L ^ 2 by ring]
  linarith

/-- `Nc` is the function `N` of E11. -/
theorem Nc_eq : Nc = FixedWidthCounterexample.N := by
  funext x
  show ((⌊10 * x * x + x * Real.sin (2 * Real.pi * x)⌋ : ℤ) : ℝ) =
    ((⌊10 * x ^ 2 + x * Real.sin (2 * Real.pi * x)⌋ : ℤ) : ℝ)
  rw [show 10 * x * x = 10 * x ^ 2 by ring]

/-- E9. One fixed width is not enough: the smoothing has the sharp law, the count has none. -/
theorem fixed_width_insufficient (B : ℝ) :
    HasSharpRealLaw (smooth w2 t2 1 Nc) 10 0 ∧ ¬ HasSharpRealLaw Nc 10 B := by
  refine ⟨smoothed_sharp_law, ?_⟩
  rw [Nc_eq]
  exact FixedWidthCounterexample.not_sharp_law B

end SteklovAudit.FixedWidthSmoothing
