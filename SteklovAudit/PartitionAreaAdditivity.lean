import Mathlib
import SteklovAudit.PartitionTraceSplitting
import SteklovAudit.MainConditional

/-!
# K10a: area additivity from a partition of unity (shape of ledger field H2)

For a finite measure `μ` on the boundary `X` and a finite weight family `w j` (for the
tetrahedral partition: the squared cutoffs `ζ_v²`, `χ_e²`, `χ_f²`) with `∑ j, w j x = 1` for
every `x`, integrating the pointwise identity gives `∑ j, ∫ w j ∂μ = μ(X)`. Grouping the weights
into vertex, edge and face families, the area coefficients `A_• = (∑ ∫ w) / (4π)` satisfy
`AV + AE + AF = μ(X) / (4π)`, and if `μ(X) = √3 a²` this is `MainConditional.areaCoeff a`, the
right-hand side of the `area` field of `Thm111Inputs`.

These are the same weights as in K9 (`PartitionTraceSplitting.lean`), so one partition feeds
both the `splitting` and the `area` fields.

What this file does NOT prove: it does not prove the pointwise identity
`∑ ζ_v² + ∑ χ_e² + ∑ χ_f² = 1` for the tetrahedral partition (item K11, taken here as the
hypothesis `hsum`), it does not prove that the surface measure of `∂T_a` is `√3 a²` (item K10b,
taken here as the hypothesis `hsurf`), it does not construct a Dirichlet-to-Neumann operator, it
does not prove any ledger input H1–H6 for the actual operator, and it does not prove
Theorem 1.3 / 11.1.
-/

open MeasureTheory

namespace SteklovAudit.PartitionAreaAdditivity

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The integral of the constant `1` is the total mass. -/
theorem integral_one_eq [IsFiniteMeasure μ] :
    ∫ _x, (1 : ℝ) ∂μ = (μ Set.univ).toReal := by
  first
    | (simp [integral_const]; done)
    | (simp [integral_const, measureReal_def]; done)
    | (simp [integral_const, Measure.real]; done)
    | (rw [integral_const, smul_eq_mul, mul_one]; rfl)

/-- Integrating the pointwise partition identity: the total weight is the total measure. -/
theorem sum_integral_weights {J : Type*} [Fintype J] [IsFiniteMeasure μ]
    (w : J → X → ℝ) (hsum : ∀ x, ∑ j, w j x = 1) (hint : ∀ j, Integrable (w j) μ) :
    ∑ j, ∫ x, w j x ∂μ = (μ Set.univ).toReal := by
  have h := integral_finset_sum (μ := μ) Finset.univ
    (fun j (_ : j ∈ Finset.univ) => hint j)
  calc ∑ j, ∫ x, w j x ∂μ = ∫ x, ∑ j, w j x ∂μ := h.symm
    _ = ∫ _x, (1 : ℝ) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show ∑ j, w j x = 1
        exact hsum x
    _ = (μ Set.univ).toReal := integral_one_eq (μ := μ)

/-- Area coefficient of a weight family: total weight divided by `4π`. -/
noncomputable def groupArea {J : Type*} [Fintype J] (μ : Measure X) (w : J → X → ℝ) : ℝ :=
  (∑ j, ∫ x, w j x ∂μ) / (4 * Real.pi)

/-- The vertex, edge and face area coefficients add to `μ(X) / (4π)`. -/
theorem area_coeffs_add {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [IsFiniteMeasure μ]
    (wV : V → X → ℝ) (wE : E → X → ℝ) (wF : F → X → ℝ)
    (hsum : ∀ x, ∑ v, wV v x + ∑ e, wE e x + ∑ f, wF f x = 1)
    (hV : ∀ v, Integrable (wV v) μ) (hE : ∀ e, Integrable (wE e) μ)
    (hF : ∀ f, Integrable (wF f) μ) :
    groupArea μ wV + groupArea μ wE + groupArea μ wF =
      (μ Set.univ).toReal / (4 * Real.pi) := by
  have hw : ∀ x, ∑ j, Sum.elim (Sum.elim wV wE) wF j x = 1 := by
    intro x
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact hsum x
  have hi : ∀ j, Integrable (Sum.elim (Sum.elim wV wE) wF j) μ := by
    rintro ((v | e) | f)
    · exact hV v
    · exact hE e
    · exact hF f
  have h := sum_integral_weights (μ := μ) (Sum.elim (Sum.elim wV wE) wF) hw hi
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at h
  unfold groupArea
  rw [← h]
  ring

/-- The H2 field shape: if the surface measure is `√3 a²` (four equilateral faces of side `a`,
item K10b), the three area coefficients add to `MainConditional.areaCoeff a`. -/
theorem area_field_of_surface {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [IsFiniteMeasure μ] (a : ℝ)
    (wV : V → X → ℝ) (wE : E → X → ℝ) (wF : F → X → ℝ)
    (hsum : ∀ x, ∑ v, wV v x + ∑ e, wE e x + ∑ f, wF f x = 1)
    (hV : ∀ v, Integrable (wV v) μ) (hE : ∀ e, Integrable (wE e) μ)
    (hF : ∀ f, Integrable (wF f) μ)
    (hsurf : (μ Set.univ).toReal = Real.sqrt 3 * a ^ 2) :
    groupArea μ wV + groupArea μ wE + groupArea μ wF =
      SteklovAudit.MainConditional.areaCoeff a := by
  rw [area_coeffs_add wV wE wF hsum hV hE hF, hsurf]
  first
    | rfl
    | (unfold SteklovAudit.MainConditional.areaCoeff; ring)

end SteklovAudit.PartitionAreaAdditivity
