import Mathlib
import SteklovAudit.MainConditional

/-!
# D7: the real-parameter law implies the integer-level law

Roadmap item D7. `SteklovAudit.lean` has two forms of the two-term law: `HasSharpRealLaw` (all
real `L`, the form proved conditionally by `MainConditional`) and `HasSharpTwoTermLawOnIntegers`
(levels `n + 1`, the form produced by `sharp_integer_law_of_two_scale`). Proved here:

* `twoTerm_eq_real`: `twoTermPolynomial A B n = realWeylPolynomial A B (n + 1)`;
* `integer_law_of_real_law`: `HasSharpRealLaw N A B` implies
  `HasSharpTwoTermLawOnIntegers (fun n => N (n + 1)) A B`;
* `integer_law_of_inputs`: hence the ledger of `MainConditional` also gives the integer-level law
  with the paper's constants.

So the real-parameter conclusion is the stronger of the two, as the README says. What this file does
NOT prove: the converse (passing from integer levels to all real `L` needs control of `N` between
consecutive levels, where the Weyl polynomial itself moves by about `2A·L`, which is not `o(L)`);
any hypothesis `[H1]`–`[H6]`; the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.RealToIntegerLaw

open SteklovAudit SteklovAudit.MainConditional

/-- The integer-level polynomial is the real one at `L = n + 1`. -/
theorem twoTerm_eq_real (A B : ℝ) (n : ℕ) :
    twoTermPolynomial A B n = realWeylPolynomial A B ((n : ℝ) + 1) := rfl

/-- D7. The real-parameter law implies the integer-level law. -/
theorem integer_law_of_real_law (N : ℝ → ℝ) (A B : ℝ) (h : HasSharpRealLaw N A B) :
    HasSharpTwoTermLawOnIntegers (fun n => N ((n : ℝ) + 1)) A B := by
  intro δ hδ
  obtain ⟨L₀, _, hL⟩ := h δ hδ
  refine ⟨⌈L₀⌉₊, fun n hn => ?_⟩
  have h1 : L₀ ≤ (⌈L₀⌉₊ : ℝ) := Nat.le_ceil L₀
  have h2 : ((⌈L₀⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have h3 : L₀ ≤ (n : ℝ) + 1 := by linarith
  rw [twoTerm_eq_real]
  exact hL ((n : ℝ) + 1) h3

/-- D7. The ledger of `MainConditional` gives the integer-level law with the paper's constants. -/
theorem integer_law_of_inputs (N : ℝ → ℝ) (a c : ℝ) (H : Thm111Inputs N a c) :
    HasSharpTwoTermLawOnIntegers (fun n => N ((n : ℝ) + 1)) (areaCoeff a) (6 * a * c) :=
  integer_law_of_real_law N _ _ (theorem_11_1_of_inputs N a c H)

end SteklovAudit.RealToIntegerLaw
