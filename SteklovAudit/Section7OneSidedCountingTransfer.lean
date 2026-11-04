-- From hourly continuation 30 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib

/-! Continuation 30: scalar ingredients of the one-sided counting transfer.
    These are Lean candidates, NOT compiler-checked. The finite-dimensional
    operator theorem in the report is NOT formalized by these declarations. -/
namespace SteklovAudit

theorem spectral_leakage_budget (leakage defect gapBudget : ℝ)
    (hLeak : leakage ≤ gapBudget) (hDef : 0 ≤ defect) :
    leakage ≤ defect + gapBudget := by
  linarith

theorem counting_transfer_scalar (nA nB defect leakage gapBudget : ℝ)
    (hMass : nA ≤ nB + defect + leakage)
    (hGap : leakage ≤ gapBudget) :
    nA ≤ nB + defect + gapBudget := by
  linarith

theorem two_sided_counting_scalar (nA nB leftErr rightErr : ℝ)
    (hAB : nA ≤ nB + leftErr) (hBA : nB ≤ nA + rightErr) :
    nA - nB ≤ leftErr ∧ nB - nA ≤ rightErr := by
  constructor <;> linarith

end SteklovAudit
