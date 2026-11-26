import Mathlib
import SteklovAudit.PartitionAreaAdditivity

/-!
# K10b: Lebesgue area of the equilateral face (geometry step of ledger field H2)

The planar equilateral triangle of side `a ≥ 0` is written as the region between two lines,
`eqTriangle a = {(y, x) | 0 ≤ y ≤ √3 a / 2, √3 y / 3 < x < a − √3 y / 3}`, with corners
`(0, 0)`, `(0, a)` and `(√3 a / 2, a / 2)`; `triangle_equilateral` checks all three sides have
length `a`. `triangle_area` computes its Lebesgue measure in `ℝ × ℝ` as `√3 a² / 4` via
`volume_regionBetween_eq_integral`, so four faces give `√3 a²` (`surface_area_four_faces`).
`area_field_of_faces` feeds this into K10a's `area_field_of_surface`, replacing its hypothesis
`hsurf : μ(∂T) = √3 a²` by the decomposition hypothesis `hfaces`: the boundary measure is four
times the area of this triangle.

What this file does NOT prove: Lean has no surface measure on `∂T_a` here, so `hfaces` (the
boundary measure is the sum of four face areas, each face isometric to `eqTriangle a`) stays a
named hypothesis; it does not prove the pointwise partition identity (K11, hypothesis `hsum`), it
does not construct a Dirichlet-to-Neumann operator, it does not prove any ledger input H1–H6 for
the actual operator, and it does not prove Theorem 1.3 / 11.1.
-/

open MeasureTheory Set

namespace SteklovAudit.PartitionSurfaceArea

/-- Lower edge of the triangle, as a function of the first coordinate. -/
noncomputable def triLo (y : ℝ) : ℝ := Real.sqrt 3 / 3 * y

/-- Upper edge of the triangle. -/
noncomputable def triHi (a y : ℝ) : ℝ := a - Real.sqrt 3 / 3 * y

/-- The equilateral triangle of side `a` with corners `(0,0)`, `(0,a)`, `(√3 a/2, a/2)`. -/
noncomputable def eqTriangle (a : ℝ) : Set (ℝ × ℝ) :=
  regionBetween triLo (triHi a) (Icc 0 (Real.sqrt 3 * a / 2))

/-- All three sides of `eqTriangle a` have squared length `a²`. -/
theorem triangle_equilateral (a : ℝ) :
    (0 - 0) ^ 2 + (a - 0) ^ 2 = a ^ 2 ∧
    (Real.sqrt 3 * a / 2 - 0) ^ 2 + (a / 2 - 0) ^ 2 = a ^ 2 ∧
    (Real.sqrt 3 * a / 2 - 0) ^ 2 + (a / 2 - a) ^ 2 = a ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨by ring, ?_, ?_⟩
  · linear_combination (a ^ 2 / 4) * hs
  · linear_combination (a ^ 2 / 4) * hs

theorem continuous_triLo : Continuous triLo := by
  unfold triLo; fun_prop

theorem continuous_triHi (a : ℝ) : Continuous (triHi a) := by
  unfold triHi; fun_prop

theorem triLo_le_triHi {a : ℝ} :
    ∀ y ∈ Icc (0 : ℝ) (Real.sqrt 3 * a / 2), triLo y ≤ triHi a y := by
  intro y hy
  unfold triLo triHi
  have h1 := mul_le_mul_of_nonneg_left hy.2 (Real.sqrt_nonneg 3)
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3 : Real.sqrt 3 * (Real.sqrt 3 * a / 2) = 3 * a / 2 := by
    linear_combination (a / 2) * h2
  first
    | linarith [h1, h3]
    | nlinarith [h1, h3, Real.sqrt_nonneg 3]

theorem triangle_width_integral (a h : ℝ) :
    ∫ y in (0 : ℝ)..h, (triHi a - triLo) y = a * h - Real.sqrt 3 / 3 * h ^ 2 := by
  have e2 : (triHi a - triLo) = fun y => a - 2 * Real.sqrt 3 / 3 * y := by
    funext y
    simp only [Pi.sub_apply, triHi, triLo]
    ring
  simp only [e2]
  first
    | (rw [intervalIntegral.integral_sub
          ((by fun_prop : Continuous fun _ : ℝ => a).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun y : ℝ => 2 * Real.sqrt 3 / 3 * y).intervalIntegrable _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
        smul_eq_mul]
       ring)
    | (simp [integral_id]; ring)
    | (norm_num [integral_id]; ring)

/-- The equilateral triangle of side `a` has Lebesgue area `√3 a² / 4`. -/
theorem triangle_area {a : ℝ} (ha : 0 ≤ a) :
    ((volume : Measure ℝ).prod volume) (eqTriangle a) =
      ENNReal.ofReal (Real.sqrt 3 * a ^ 2 / 4) := by
  have hh : (0 : ℝ) ≤ Real.sqrt 3 * a / 2 := by positivity
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [eqTriangle, volume_regionBetween_eq_integral continuous_triLo.integrableOn_Icc
      (continuous_triHi a).integrableOn_Icc measurableSet_Icc triLo_le_triHi,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh,
    triangle_width_integral]
  congr 1
  linear_combination (-(Real.sqrt 3 * a ^ 2 / 12)) * hs

theorem triangle_area_toReal {a : ℝ} (ha : 0 ≤ a) :
    (((volume : Measure ℝ).prod volume) (eqTriangle a)).toReal = Real.sqrt 3 * a ^ 2 / 4 := by
  rw [triangle_area ha, ENNReal.toReal_ofReal (by positivity)]

/-- Four equilateral faces of side `a` have total area `√3 a²`. -/
theorem surface_area_four_faces {a : ℝ} (ha : 0 ≤ a) :
    4 * (((volume : Measure ℝ).prod volume) (eqTriangle a)).toReal = Real.sqrt 3 * a ^ 2 := by
  rw [triangle_area_toReal ha]; ring

/-- K10a's H2 field with `hsurf` replaced by the four-face decomposition `hfaces`. -/
theorem area_field_of_faces {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F] [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 ≤ a)
    (wV : V → X → ℝ) (wE : E → X → ℝ) (wF : F → X → ℝ)
    (hsum : ∀ x, ∑ v, wV v x + ∑ e, wE e x + ∑ f, wF f x = 1)
    (hV : ∀ v, Integrable (wV v) μ) (hE : ∀ e, Integrable (wE e) μ)
    (hF : ∀ f, Integrable (wF f) μ)
    (hfaces : (μ Set.univ).toReal =
      4 * (((volume : Measure ℝ).prod volume) (eqTriangle a)).toReal) :
    PartitionAreaAdditivity.groupArea μ wV + PartitionAreaAdditivity.groupArea μ wE +
        PartitionAreaAdditivity.groupArea μ wF =
      SteklovAudit.MainConditional.areaCoeff a :=
  PartitionAreaAdditivity.area_field_of_surface a wV wE wF hsum hV hE hF
    (by rw [hfaces, surface_area_four_faces ha])

end SteklovAudit.PartitionSurfaceArea
