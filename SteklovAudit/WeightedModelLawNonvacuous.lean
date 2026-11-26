import Mathlib
import SteklovAudit.WeightedModelLaw

/-!
# Non-vacuity of the weighted-decomposition route (roadmap item G163)

Definition check for G162 (`WeightedModelLaw.unweighted_model_law`): its hypotheses hold in a scalar
model where the weighted counts `Nγ` differ from the unweighted count `N` by a NONZERO,
`γ`-dependent gap `γ L`, so the weighting-error input is used non-trivially.

Model (`ι = Unit`, fixed `I : ℝ`): `N L = main L = L²/(4π) I` (`wmMain`), and
`Nγ L = L²/(4π) I + γ L` (`wmNγ`). The decomposition data are `s = ∅`, `Nf L = L²/(4π) I`, `P L = L`,
`G = 0`, `A = 0`, `c = γ`, `Q = 1`, `C' = 1`, so `mγ − main = γ L`; the weighting constant is `C = 1`.

* `witness_decomp`: `GammaDecomp Unit (wmNγ I γ) (wmMain I) 1 γ` for every `γ > 0`.
* `witness_gap`, `witness_gap_ne`: `|N L − Nγ L| = γ L`, nonzero for `L > 0`.
* `witness_conclusion`: G162 applies.

What this file does NOT prove: anything about the actual wedge or tetrahedron Dirichlet-to-Neumann
operator, the weighting error for the paper's weighted count, (7.44), (7.38)/(7.45), (7.29), H5, or
Theorem 1.3 / 11.1. The model functions are explicit polynomials chosen only to show that the
hypotheses of G162 are satisfiable with a nonzero weighting gap.
-/

namespace SteklovAudit.WeightedModelLawNonvacuous

open Filter Asymptotics

/-- **G163.** Model unweighted count and main term `L²/(4π) I`. -/
noncomputable def wmMain (I : ℝ) : ℝ → ℝ := fun L => L ^ 2 / (4 * Real.pi) * I

/-- **G163.** Model weighted count `L²/(4π) I + γ L`. -/
noncomputable def wmNγ (I γ : ℝ) : ℝ → ℝ := fun L => L ^ 2 / (4 * Real.pi) * I + γ * L

/-- **G163.** The per-`γ` decomposition (7.44) of the model weighted count. -/
theorem witness_decomp (I : ℝ) :
    ∀ γ : ℝ, 0 < γ →
      SteklovAudit.ModelEdgeLawGammaFree.GammaDecomp Unit (wmNγ I γ) (wmMain I) 1 γ := by
  intro γ hγ
  first
    | unfold SteklovAudit.ModelEdgeLawGammaFree.GammaDecomp
    | simp only [SteklovAudit.ModelEdgeLawGammaFree.GammaDecomp]
    | delta SteklovAudit.ModelEdgeLawGammaFree.GammaDecomp
  refine ⟨∅, fun L => L ^ 2 / (4 * Real.pi) * I, fun L => L, fun _ => 0, fun _ _ => 0, γ, 1, I,
    ?_, ?_, ?_, isLittleO_zero _ _, fun i hi => by simp at hi, ?_⟩
  · intro L
    first
      | (simp only [wmNγ, Finset.sum_empty]; ring)
      | (simp [wmNγ])
      | (simp [wmNγ]; ring)
  · simpa using (isLittleO_zero (fun L : ℝ => L) atTop)
  · simpa using (isLittleO_zero (fun L : ℝ => L) atTop)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    have hp : 0 ≤ γ * L := mul_nonneg hγ.le hL
    simp only [wmMain]
    rw [abs_le]
    constructor
    · first
        | linarith
        | nlinarith
    · first
        | linarith
        | nlinarith

/-- **G163.** The weighting gap is exactly `γ L`. -/
theorem witness_gap (I γ L : ℝ) (hγ : 0 < γ) (hL : 0 ≤ L) :
    |wmMain I L - wmNγ I γ L| = γ * L := by
  have e : wmMain I L - wmNγ I γ L = -(γ * L) := by
    simp only [wmMain, wmNγ]
    ring
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg hγ.le hL)]

/-- **G163.** The weighting gap is nonzero for `L > 0`. -/
theorem witness_gap_ne (I γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L) :
    |wmMain I L - wmNγ I γ L| ≠ 0 := by
  rw [witness_gap I γ L hγ hL.le]
  exact (mul_pos hγ hL).ne'

/-- **G163.** `WeightedModelLaw.unweighted_model_law` applies to the model with `C = C' = 1`. -/
theorem witness_conclusion (I : ℝ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |wmMain I L - wmMain I L| ≤ η * L :=
  SteklovAudit.WeightedModelLaw.unweighted_model_law Unit (wmMain I) (wmMain I) 1 1 zero_le_one
    zero_le_one (fun γ hγ => ⟨wmNγ I γ, witness_decomp I γ hγ, by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
      rw [witness_gap I γ L hγ hL, one_mul]⟩)

end SteklovAudit.WeightedModelLawNonvacuous
