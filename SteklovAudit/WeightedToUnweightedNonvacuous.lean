import Mathlib
import SteklovAudit.WeightedToUnweighted

/-!
# Non-vacuity of the weighted-to-unweighted input (roadmap item G156)

Definition check for G154 (`WeightedToUnweighted.unweighted_of_weighted`): its hypotheses hold in a
model where the weighting error is NONZERO and genuinely `γ`-dependent. Model: unweighted count
`Nu L = L ^ 2`, weighted counts `Nw γ L = L ^ 2 + γ * L`, weighted main terms `mγ = Nw γ`,
unweighted main term `Nu`, constants `C = C' = 1`.

* `witness_gap`: `|Nu L − Nw γ L| = γ * L` for `L ≥ 0`, `γ > 0`.
* `witness_gap_ne`: this gap is nonzero for `L > 0`.
* `witness_hyps`: all hypotheses of `unweighted_of_weighted` hold for this model.
* `witness_conclusion`: G154 applied to the model.

What this file does NOT prove: the bound `|N − Nγ| ≤ C γ L` for the paper's weighted count, any
weighted or unweighted edge law for the actual wedge or tetrahedron Dirichlet-to-Neumann operator,
(7.29), (7.38)/(7.45), (9.1), (11.3), H1–H6, or Theorem 1.3 / 11.1. It only shows that the
hypothesis shape of G154 is satisfiable with a nonzero weighting error, so the input is not
vacuous and not the target in disguise.
-/

namespace SteklovAudit.WeightedToUnweightedNonvacuous

open Filter

/-- Model unweighted count `L ^ 2`. -/
def Nu (L : ℝ) : ℝ := L ^ 2

/-- Model weighted count `L ^ 2 + γ L`. -/
def Nw (γ L : ℝ) : ℝ := L ^ 2 + γ * L

/-- **G156.** The model weighting error equals `γ L`. -/
theorem witness_gap (γ L : ℝ) (hγ : 0 < γ) (hL : 0 ≤ L) :
    |Nu L - Nw γ L| = γ * L := by
  have e : Nu L - Nw γ L = -(γ * L) := by
    unfold Nu Nw
    ring
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg hγ.le hL)]

/-- **G156.** The model weighting error is nonzero for `L > 0`. -/
theorem witness_gap_ne (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L) :
    Nu L - Nw γ L ≠ 0 := by
  have e : Nu L - Nw γ L = -(γ * L) := by
    unfold Nu Nw
    ring
  rw [e]
  intro h
  have hp : 0 < γ * L := mul_pos hγ hL
  linarith

/-- **G156.** All hypotheses of `unweighted_of_weighted` hold for the model (`C = C' = 1`). -/
theorem witness_hyps :
    ∀ γ : ℝ, 0 < γ → ∃ Nγ mγ : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |Nγ L - mγ L| ≤ η * L) ∧
        (∀ᶠ L in atTop, |Nu L - Nγ L| ≤ 1 * γ * L) ∧
          ∀ᶠ L in atTop, |mγ L - Nu L| ≤ 1 * γ * L := by
  intro γ hγ
  refine ⟨Nw γ, Nw γ, fun η hη => ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |Nw γ L - Nw γ L| ≤ η * L
    rw [sub_self, abs_zero]
    exact mul_nonneg hη.le hL
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |Nu L - Nw γ L| ≤ 1 * γ * L
    rw [witness_gap γ L hγ hL, one_mul]
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |Nw γ L - Nu L| ≤ 1 * γ * L
    rw [abs_sub_comm, witness_gap γ L hγ hL, one_mul]

/-- **G156.** G154 applied to the model: the unweighted law `Nu − Nu = o(L)` (trivially true here;
the point is that the hypotheses were met with a nonzero weighting error). -/
theorem witness_conclusion :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |Nu L - Nu L| ≤ η * L :=
  SteklovAudit.WeightedToUnweighted.unweighted_of_weighted Nu Nu 1 1 zero_le_one zero_le_one
    witness_hyps

end SteklovAudit.WeightedToUnweightedNonvacuous
