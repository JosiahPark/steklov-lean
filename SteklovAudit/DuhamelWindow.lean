import Mathlib
import SteklovAudit.DuhamelSpectral
import SteklovAudit.FourierOneOverT

/-!
# The Duhamel bound fed through the `1/t` window (roadmap item G134)

For finite spectral data (an overlap matrix `J i j` between eigenvectors with eigenvalues `lam i`,
`mu j`), `hsDiff t` is the HS norm of the propagated difference `J i j (e^{−it lam i} − e^{−it mu j})`
and `hsDefect` is the HS norm of the commutator defect `J i j (lam i − mu j)`. `hsDiff_le` takes the
square root of G129 (`duhamel_hs_le`): `hsDiff t ≤ |t| · hsDefect`. `window_hsDiff_le` feeds this into
G130 (`fourier_cancel_inv`): `|∫_{−T}^{T} t⁻¹ hsDiff t| ≤ 2 T · hsDefect`, the `K T L ε(1/L)` term of
the window-defect shape in G133 (`littleO_of_window_defect`). `hsDiff_zero` and `hsDefect_example`
check that the definitions are not junk: the propagated difference vanishes at `t = 0`, and a
`1 × 1` example has defect `1`.

What this file does NOT prove: anything about unbounded operators, domains, or the Steklov / DtN
operator; that `hsDefect` is `o(1)` (or any size) for the actual tetrahedron–wedge comparison (the
HS defect row of the F table); the uniform window tail `C L / T`; (7.29), H5, or Theorem 1.3 / 11.1.
Everything is finite-dimensional.
-/

namespace SteklovAudit.DuhamelWindow

open Complex SteklovAudit.DuhamelSpectral SteklovAudit.FourierOneOverT

/-- HS norm of the propagated difference `J i j (e^{−it lam i} − e^{−it mu j})`. -/
noncomputable def hsDiff {m n : ℕ} (J : Fin m → Fin n → ℂ) (lam : Fin m → ℝ) (mu : Fin n → ℝ)
    (t : ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖J i j‖ ^ 2 *
    ‖exp (((-(t * lam i) : ℝ) : ℂ) * I) - exp (((-(t * mu j) : ℝ) : ℂ) * I)‖ ^ 2)

/-- HS norm of the commutator defect `J i j (lam i − mu j)`. -/
noncomputable def hsDefect {m n : ℕ} (J : Fin m → Fin n → ℂ) (lam : Fin m → ℝ) (mu : Fin n → ℝ) :
    ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖J i j‖ ^ 2 * (lam i - mu j) ^ 2)

section

variable {m n : ℕ} (J : Fin m → Fin n → ℂ) (lam : Fin m → ℝ) (mu : Fin n → ℝ)

theorem hsDiff_nonneg (t : ℝ) : 0 ≤ hsDiff J lam mu t := by
  unfold hsDiff
  exact Real.sqrt_nonneg _

theorem hsDefect_nonneg : 0 ≤ hsDefect J lam mu := by
  unfold hsDefect
  exact Real.sqrt_nonneg _

/-- **G134.** Square root of G129: `hsDiff t ≤ |t| · hsDefect`. -/
theorem hsDiff_le (t : ℝ) : hsDiff J lam mu t ≤ |t| * hsDefect J lam mu := by
  have h := duhamel_hs_le J lam mu t
  unfold hsDiff hsDefect
  calc _ ≤ Real.sqrt (t ^ 2 * ∑ i, ∑ j, ‖J i j‖ ^ 2 * (lam i - mu j) ^ 2) := by
        first
          | exact Real.sqrt_le_sqrt h
          | exact Real.sqrt_le_sqrt (h := h)
          | gcongr
    _ = |t| * Real.sqrt (∑ i, ∑ j, ‖J i j‖ ^ 2 * (lam i - mu j) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

/-- **G134.** G129 through the `1/t` window of G130: `|∫_{−T}^{T} t⁻¹ hsDiff t| ≤ 2 T · hsDefect`. -/
theorem window_hsDiff_le (T : ℝ) (hT : 0 ≤ T) :
    |∫ t in (-T)..T, t⁻¹ * hsDiff J lam mu t| ≤ 2 * T * hsDefect J lam mu :=
  fourier_cancel_inv (hsDiff J lam mu) (hsDefect J lam mu) T hT (hsDiff_le J lam mu)

/-- Non-junk check: the propagated difference vanishes at `t = 0`. -/
theorem hsDiff_zero : hsDiff J lam mu 0 = 0 := by
  have h := hsDiff_le J lam mu 0
  rw [abs_zero, zero_mul] at h
  exact le_antisymm h (hsDiff_nonneg J lam mu 0)

/-- Zero defect forces zero propagated difference at every time. -/
theorem hsDiff_eq_zero_of_defect (h0 : hsDefect J lam mu = 0) (t : ℝ) : hsDiff J lam mu t = 0 := by
  have h := hsDiff_le J lam mu t
  rw [h0, mul_zero] at h
  exact le_antisymm h (hsDiff_nonneg J lam mu t)

end

/-- Non-vacuity: a `1 × 1` example with eigenvalues `0` and `1` has defect `1`. -/
theorem hsDefect_example :
    hsDefect (fun _ _ => (1 : ℂ)) (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
  first
    | simp [hsDefect]
    | (unfold hsDefect; norm_num)
    | (unfold hsDefect; simp)

end SteklovAudit.DuhamelWindow
