import Mathlib
import SteklovAudit.MainConditional

/-!
# D3: the two coefficients of a sharp two-term law are unique

Roadmap item D3 (definition check on `HasSharpRealLaw`). Proved here:

* `zero_of_forall_le`: a real number bounded by `4δ` for every `δ > 0` is `0`;
* `sharp_law_unique`: if `N` satisfies `HasSharpRealLaw` with `(A, B)` and with `(A', B')`, then
  `A = A'` and `B = B'`. So the notion used for Theorem 11.1 pins down both coefficients;
* `edge_invariant_determined`: if `N` obeys (11.4)'s shape with edge constants `c` and `c'` and
  `a ≠ 0`, then `c = c'`. The edge invariant is a spectral invariant: it is determined by the
  counting function alone;
* `not_one_term_law`: if `a ≠ 0` and `c ≠ 0`, a count obeying the two-term law with `6ac` does NOT
  obey the one-term law (`B = 0`), so the second term is detectable.

What this file does NOT prove: that the Steklov count obeys any such law; any hypothesis
`[H1]`–`[H6]`; the main theorem (Theorem 1.3 / 11.1). The hypothesis count in STATUS.md is not
changed.
-/

namespace SteklovAudit.SharpLawUnique

open SteklovAudit SteklovAudit.MainConditional

/-- A real number bounded by `4δ` for every `δ > 0` vanishes. -/
theorem zero_of_forall_le (x : ℝ) (hx : ∀ δ : ℝ, 0 < δ → |x| ≤ 4 * δ) : x = 0 := by
  by_contra hne
  have hpos : 0 < |x| := abs_pos.mpr hne
  have h := hx (|x| / 8) (by positivity)
  linarith

/-- Two sharp laws for the same count differ by `o(1)` after division by `L`. -/
theorem diff_small (N : ℝ → ℝ) (A B A' B' : ℝ)
    (h : HasSharpRealLaw N A B) (h' : HasSharpRealLaw N A' B') :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, 0 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → 0 < L →
      |(A - A') * L + (B - B')| ≤ 2 * δ := by
  intro δ hδ
  obtain ⟨L1, hL1, h1⟩ := h δ hδ
  obtain ⟨L2, hL2, h2⟩ := h' δ hδ
  refine ⟨max L1 L2, le_trans hL1 (le_max_left _ _), fun L hL hLpos => ?_⟩
  have e1 := abs_le.mp (h1 L (le_trans (le_max_left _ _) hL))
  have e2 := abs_le.mp (h2 L (le_trans (le_max_right _ _) hL))
  unfold realWeylPolynomial at e1 e2
  have h3 : |((A - A') * L + (B - B')) * L| ≤ 2 * δ * L := by
    rw [abs_le]
    constructor
    · nlinarith [e1.1, e1.2, e2.1, e2.2]
    · nlinarith [e1.1, e1.2, e2.1, e2.2]
  rw [abs_mul, abs_of_pos hLpos] at h3
  exact le_of_mul_le_mul_right h3 hLpos

/-- D3. Uniqueness of the coefficients of a sharp two-term law. -/
theorem sharp_law_unique (N : ℝ → ℝ) (A B A' B' : ℝ)
    (h : HasSharpRealLaw N A B) (h' : HasSharpRealLaw N A' B') : A = A' ∧ B = B' := by
  have key := diff_small N A B A' B' h h'
  have hp : A - A' = 0 := by
    apply zero_of_forall_le
    intro δ hδ
    obtain ⟨L₀, hL₀, hk⟩ := key δ hδ
    have k1 := abs_le.mp (hk (L₀ + 1) (by linarith) (by linarith))
    have k2 := abs_le.mp (hk (L₀ + 2) (by linarith) (by linarith))
    rw [abs_le]
    constructor
    · nlinarith [k1.1, k1.2, k2.1, k2.2]
    · nlinarith [k1.1, k1.2, k2.1, k2.2]
  have hq : B - B' = 0 := by
    apply zero_of_forall_le
    intro δ hδ
    obtain ⟨L₀, hL₀, hk⟩ := key δ hδ
    have k1 := hk (L₀ + 1) (by linarith) (by linarith)
    rw [hp, zero_mul, zero_add] at k1
    linarith
  exact ⟨sub_eq_zero.mp hp, sub_eq_zero.mp hq⟩

/-- D3. The edge invariant in (11.4) is determined by the counting function. -/
theorem edge_invariant_determined (N : ℝ → ℝ) (a c c' : ℝ) (ha : a ≠ 0)
    (h : HasSharpRealLaw N (areaCoeff a) (6 * a * c))
    (h' : HasSharpRealLaw N (areaCoeff a) (6 * a * c')) : c = c' := by
  have hB := (sharp_law_unique N _ _ _ _ h h').2
  have h6 : (6 * a) ≠ 0 := mul_ne_zero (by norm_num) ha
  exact mul_left_cancel₀ h6 hB

/-- D3. With `a ≠ 0` and `c ≠ 0`, the two-term law excludes the one-term law. -/
theorem not_one_term_law (N : ℝ → ℝ) (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0)
    (h : HasSharpRealLaw N (areaCoeff a) (6 * a * c)) :
    ¬ HasSharpRealLaw N (areaCoeff a) 0 := by
  intro h0
  have hB := (sharp_law_unique N _ _ _ _ h h0).2
  have : 6 * a * c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ha) hc
  exact this hB

end SteklovAudit.SharpLawUnique
