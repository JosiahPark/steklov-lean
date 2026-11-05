import Mathlib
import SteklovAudit

/-!
# Two-parameter fixed-smoothing removal (continuation 54; compare R38.1)

Continuation 54 (2026-11-05) proved on paper, and shipped uncompiled, the following scalar step.
Let `N` be a counting function and `S δ` (for `0 < δ ≤ δ₀`) approximants. Assume

* (A) `|N L - S δ L| ≤ C δ L + C` for `L ≥ 1`, with one constant `C` for all `δ`;
* (B) for each fixed `δ`, `limsup_{L→∞} |S δ L - (A L² + B L)| / L ≤ ω δ`, with the SAME `A, B`
  for every `δ` (stated as: for every `η > 0`, eventually `|…| ≤ (ω δ + η) L`);
* (C) `ω δ → 0` as `δ ↓ 0`.

Then `N` has the sharp law `A L² + B L + o(L)` (`HasSharpRealLaw N A B`). Proved here:

* `error_budget`: the pointwise triangle step `|N - P| ≤ C δ + K + ω` (continuation 54's candidate,
  with the proof changed to `abs_sub_le`);
* `sharp_law_of_two_parameter_smoothing`: (A)–(C) imply `HasSharpRealLaw N A B`.

Quantifier caveats recorded by continuation 54 and visible in the statement: the coefficient `C` in
(A) does not depend on `δ`; the coefficients `A, B` in (B) do not depend on `δ` (a `δ`-dependent
`B δ` needs a separate proof that `B δ → B`); a `δ`-dependent `O(L)` error in (A) is not allowed.
Without a vanishing `C δ` the conclusion fails: compare `GridLaw.step_not_real_law` (D8).

What this file does NOT prove: (A) for the tetrahedron (uniform collar window masses and the
fixed-Schwartz smoothing inequality), (B)–(C) (the cumulative trace transfer (7.29) and the
microlocal/diffraction error), the wedge coefficient, any of `[H1]`–`[H6]`, or the main theorem
(Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.TwoParameterSmoothing

open SteklovAudit

/-- Continuation 54, pointwise step of the two-parameter argument. -/
theorem error_budget (N S P C δ K ω : ℝ)
    (hNS : |N - S| ≤ C * δ + K) (hSP : |S - P| ≤ ω) :
    |N - P| ≤ C * δ + K + ω := by
  have h : |N - P| ≤ |N - S| + |S - P| := by
    first
      | exact abs_sub_le N S P
      | (have h' := abs_add_le (N - S) (S - P)
         rwa [sub_add_sub_cancel] at h')
  linarith

/-- Continuation 54: fixed-smoothing approximants with a uniform `C δ L + C` error (A), a per-`δ`
limsup bound `ω δ` with common coefficients (B), and `ω δ → 0` (C) give the sharp law for `N`. -/
theorem sharp_law_of_two_parameter_smoothing
    (N : ℝ → ℝ) (S : ℝ → ℝ → ℝ) (ω : ℝ → ℝ) (A B C δ₀ : ℝ)
    (hC : 0 ≤ C) (hδ₀ : 0 < δ₀)
    (hA : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ L : ℝ, 1 ≤ L →
      |N L - S δ L| ≤ C * δ * L + C)
    (hB : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      |S δ L - realWeylPolynomial A B L| ≤ (ω δ + η) * L)
    (hω : ∀ η : ℝ, 0 < η → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ω δ ≤ η) :
    HasSharpRealLaw N A B := by
  intro ε hε
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨δ₁, hδ₁, hω₁⟩ := hω (ε / 4) (by positivity)
  obtain ⟨δ, hδpos, hδ0, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ δ₁ ∧
      δ ≤ ε / (4 * (C + 1)) :=
    ⟨min (min δ₀ δ₁) (ε / (4 * (C + 1))), lt_min (lt_min hδ₀ hδ₁) (by positivity),
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _), min_le_right _ _⟩
  have hδε' : δ * (4 * (C + 1)) ≤ ε := by
    first
      | exact (le_div_iff₀ (by positivity)).mp hδε
      | exact (le_div_iff (by positivity)).mp hδε
  have hCδ : C * δ ≤ ε / 4 := by linarith
  obtain ⟨L₀, hL₀⟩ := hB δ hδpos hδ0 (ε / 4) (by positivity)
  refine ⟨max (max L₀ 1) (4 * (C + 1) / ε),
    le_max_of_le_left (le_max_of_le_right zero_le_one), ?_⟩
  intro L hL
  have hL1 : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL3 : 4 * (C + 1) / ε ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := by linarith
  have hL3' : 4 * (C + 1) ≤ L * ε := by
    first
      | exact (div_le_iff₀ hε).mp hL3
      | exact (div_le_iff hε).mp hL3
  have hCL : C ≤ ε / 4 * L := by linarith
  have hNS := hA δ hδpos hδ0 L hL2
  have hSP := hL₀ L hL1
  have hωδ := hω₁ δ hδpos hδ1
  have htri := error_budget (N L) (S δ L) (realWeylPolynomial A B L) (C * L) δ C
    ((ω δ + ε / 4) * L) (by linarith) hSP
  have hCδL : C * δ * L ≤ ε / 4 * L := mul_le_mul_of_nonneg_right hCδ hLpos.le
  have hωL : (ω δ + ε / 4) * L ≤ (ε / 4 + ε / 4) * L :=
    mul_le_mul_of_nonneg_right (by linarith) hLpos.le
  linarith

end SteklovAudit.TwoParameterSmoothing
