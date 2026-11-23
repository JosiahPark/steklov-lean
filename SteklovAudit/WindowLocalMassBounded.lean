import Mathlib
import SteklovAudit.CumulativeBudgetQuantifiers

/-!
# Window route with `O(h⁻¹)` local mass needs only a bounded HS defect (roadmap item G146)

Row 3 of the priority table (abstract cumulative budget refinement), toward row 5.

`CumulativeBudgetQuantifiers.littleO_of_window_defect` (G133) asks for a window bound
`|r L| ≤ C L / T + K T L ε(1/L)` with `ε(h) → 0`. If the defect term instead comes as
`K T ε₀ √(Mloc L)` (a Lipschitz window constant `O(T)`, an HS defect bounded by `ε₀`, and local
spectral mass `≤ Mloc L = Mloc / h`), then it already has that shape with `ε(h) = ε₀ √(Mloc h)`, which
tends to `0`. So with local mass `O(L)`, a BOUNDED defect suffices; decay of the defect is not needed.

* `sqrt_local_mass_eq`: `√(Mloc L) = L √(Mloc (1/L))` for `L > 0`.
* `eps_of_bounded_small`: `ε₀ √(Mloc h) ≤ δ` for all small `h > 0`.
* `littleO_of_window_bounded_defect`: the window bound with a bounded defect gives `r = o(L)`.
* `local_mass_rate_needed`: with local mass `O(L²)` the defect term is `K T ε₀ L`, and the example
  `r L = L` (from `window_needs_vanishing`) satisfies it for every `T` but is not `o(L)`.

What this file does NOT prove: the window bound for the actual localized tetrahedron–wedge error, the
local mass bound `O(L)` (row "Localized spectral mass"), the boundedness of the HS defect (Lemma 7.1′ /
(7.2)), the Lipschitz constant `O(T)` of the window, Proposition 7.3, (7.29), H5, or
Theorem 1.3 / 11.1. Everything here is real analysis of scalar functions.
-/

namespace SteklovAudit.WindowLocalMassBounded

open Filter

/-- **G146.** `√(Mloc L) = L √(Mloc (1/L))` for `L > 0`. -/
theorem sqrt_local_mass_eq {L Mloc : ℝ} (hL : 0 < L) (_hM : 0 ≤ Mloc) :
    Real.sqrt (Mloc * L) = L * Real.sqrt (Mloc * (1 / L)) := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have e : Mloc * L = L ^ 2 * (Mloc * (1 / L)) := by
    first
      | (field_simp; ring)
      | field_simp
      | (rw [one_div]; field_simp)
  rw [e, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le]

/-- **G146.** The effective defect `ε₀ √(Mloc h)` is small for small `h > 0`. -/
theorem eps_of_bounded_small {ε₀ Mloc : ℝ} (hε₀ : 0 ≤ ε₀) (hM : 0 ≤ Mloc) :
    ∀ δ : ℝ, 0 < δ → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ε₀ * Real.sqrt (Mloc * h) ≤ δ := by
  intro δ hδ
  have hε1 : (0 : ℝ) < ε₀ + 1 := by linarith
  have hM1 : (0 : ℝ) < Mloc + 1 := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = δ / (ε₀ + 1) := ⟨_, rfl⟩
  have hq : 0 < q := by rw [hqdef]; exact div_pos hδ hε1
  have hqd : q * (ε₀ + 1) = δ := by
    rw [hqdef]
    first
      | exact div_mul_cancel₀ δ (ne_of_gt hε1)
      | field_simp
  refine ⟨q ^ 2 / (Mloc + 1), by positivity, ?_⟩
  intro h hh hle
  have h1 : h * (Mloc + 1) ≤ q ^ 2 := by
    first
      | exact (le_div_iff₀ hM1).1 hle
      | exact (le_div_iff hM1).1 hle
  have hMh : Mloc * h ≤ q ^ 2 := by nlinarith
  have hs : Real.sqrt (Mloc * h) ≤ q := by
    calc Real.sqrt (Mloc * h) ≤ Real.sqrt (q ^ 2) := Real.sqrt_le_sqrt hMh
      _ = q := Real.sqrt_sq hq.le
  calc ε₀ * Real.sqrt (Mloc * h) ≤ ε₀ * q := mul_le_mul_of_nonneg_left hs hε₀
    _ ≤ δ := by nlinarith [hq.le]

/-- **G146.** Window bound with local mass `≤ Mloc L` and a BOUNDED defect `ε₀`: if for every window
`T > 0`, eventually `|r L| ≤ C L / T + K T ε₀ √(Mloc L)`, then `r = o(L)` (`η`-form). -/
theorem littleO_of_window_bounded_defect (r : ℝ → ℝ) (C K ε₀ Mloc : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hε₀ : 0 ≤ ε₀) (hM : 0 ≤ Mloc)
    (hr : ∀ T : ℝ, 0 < T → ∀ᶠ L in atTop,
      |r L| ≤ C * L / T + K * T * ε₀ * Real.sqrt (Mloc * L)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L := by
  apply SteklovAudit.CumulativeBudgetQuantifiers.littleO_of_window_defect r C K hC hK
    (fun h => ε₀ * Real.sqrt (Mloc * h)) (eps_of_bounded_small hε₀ hM)
  intro T hT
  filter_upwards [hr T hT, eventually_gt_atTop (0 : ℝ)] with L h1 hL
  calc |r L| ≤ C * L / T + K * T * ε₀ * Real.sqrt (Mloc * L) := h1
    _ = C * L / T + K * T * L * (ε₀ * Real.sqrt (Mloc * (1 / L))) := by
      rw [sqrt_local_mass_eq hL hM]
      ring

/-- **G146.** The local mass rate is needed: with local mass `L²` (here `Mloc = 1`, mass `1 · L ^ 2`),
`C = K = ε₀ = 1` and `r L = L`, the window bound holds eventually for every `T > 0`, yet `r` is not
`o(L)`. -/
theorem local_mass_rate_needed :
    (∀ T : ℝ, 0 < T → ∀ᶠ L in atTop,
      |L| ≤ 1 * L / T + 1 * T * 1 * Real.sqrt (1 * L ^ 2)) ∧
      ¬ ((fun L : ℝ => L) =o[atTop] (fun L : ℝ => L)) := by
  refine ⟨fun T hT => ?_, SteklovAudit.CumulativeBudgetQuantifiers.window_needs_vanishing.2⟩
  filter_upwards [SteklovAudit.CumulativeBudgetQuantifiers.window_needs_vanishing.1 T hT,
    eventually_ge_atTop (0 : ℝ)] with L h1 hL
  have hs : Real.sqrt (1 * L ^ 2) = L := by rw [one_mul, Real.sqrt_sq hL]
  rw [hs]
  calc |L| ≤ 1 * L / T + 1 * T * L * 1 := h1
    _ = 1 * L / T + 1 * T * 1 * L := by ring

end SteklovAudit.WindowLocalMassBounded
