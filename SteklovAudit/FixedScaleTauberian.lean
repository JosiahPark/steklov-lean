import Mathlib
import SteklovAudit

/-!
# Unsmoothing by a sequence of fixed smoothing scales (continuations 35–41, compiled)

Section 11 passes from smoothed counts to the sharp count `N`. Continuations 36–41 proved on paper
that monotonicity alone is enough if the smoothed law holds, with the same coefficients, for
smoothing kernels of width `σ_n → 0` (each at fixed width; no uniformity in `n` is needed).
Continuation 35 showed that one fixed width is not enough in general. This module proves the
positive statement:

* `smooth_sandwich`: for a nondecreasing `N` and a finite averaging kernel with nodes in `[-1, 1]`,
  `S_σ(x - σ) ≤ N(x) ≤ S_σ(x + σ)`;
* `sharp_law_of_shrinking_scales`: if `S_n(x - σ_n) ≤ N(x) ≤ S_n(x + σ_n)`, each `S_n` obeys the
  sharp two-term law with coefficients `A, B`, and `σ_n` gets arbitrarily small, then `N` obeys it;
* `sharp_law_of_finite_kernels`: the two combined, for monotone `N` and finite kernels.

What this module does NOT prove: that the tetrahedral smoothed counts satisfy the sharp law at any
smoothing width, or that the paper's smoothing class has the required support. Kernels here are
finite weighted averages; general integrable kernels are not formalized. Continuation 35's
counterexample (one fixed width is insufficient) is not formalized.
-/

namespace SteklovAudit.FixedScaleTauberian

open SteklovAudit

/-- Finite smoothing: `S(x) = Σ_k w_k N(x - σ t_k)`. -/
noncomputable def smooth {κ : Type*} [Fintype κ] (w t : κ → ℝ) (σ : ℝ) (N : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k, w k * N (x - σ * t k)

/-- Monotone sandwich between shifted smoothings. -/
theorem smooth_sandwich {κ : Type*} [Fintype κ] (N : ℝ → ℝ) (hN : Monotone N) (w t : κ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) (ht : ∀ k, -1 ≤ t k ∧ t k ≤ 1)
    (σ x : ℝ) (hσ : 0 ≤ σ) :
    smooth w t σ N (x - σ) ≤ N x ∧ N x ≤ smooth w t σ N (x + σ) := by
  have hNx : N x = ∑ k, w k * N x := by rw [← Finset.sum_mul, hsum, one_mul]
  constructor
  · rw [hNx]
    unfold smooth
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ (hw k)
    apply hN
    nlinarith [mul_nonneg hσ (show (0 : ℝ) ≤ 1 + t k by linarith [(ht k).1])]
  · rw [hNx]
    unfold smooth
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ (hw k)
    apply hN
    nlinarith [mul_nonneg hσ (show (0 : ℝ) ≤ 1 - t k by linarith [(ht k).2])]

/-- Sharp law from a sequence of fixed, shrinking smoothing scales (continuations 37, 38, 40). -/
theorem sharp_law_of_shrinking_scales (N : ℝ → ℝ) (A B : ℝ) (S : ℕ → ℝ → ℝ) (σ : ℕ → ℝ)
    (hσ : ∀ n, 0 ≤ σ n)
    (hlo : ∀ n x, S n (x - σ n) ≤ N x) (hhi : ∀ n x, N x ≤ S n (x + σ n))
    (hS : ∀ n, HasSharpRealLaw (S n) A B)
    (hsmall : ∀ ε, 0 < ε → ∃ n, σ n ≤ ε) :
    HasSharpRealLaw N A B := by
  intro δ hδ
  have hA1 : 0 < |A| + 1 := by positivity
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = δ / (4 * (|A| + 1)) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  have hAη : |A| * η ≤ δ / 4 := by
    rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg A]
  obtain ⟨n, hn⟩ := hsmall η hηpos
  have hn0 := hσ n
  have hAh : |A| * σ n ≤ δ / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hn (abs_nonneg A)) hAη
  obtain ⟨L₁, hL₁0, hL₁⟩ := hS n (δ / 4) (by positivity)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = δ / 4 * σ n + |A| * σ n ^ 2 + |B| * σ n := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    have h1 : 0 ≤ δ / 4 * σ n := mul_nonneg (by positivity) hn0
    have h2 : 0 ≤ |A| * σ n ^ 2 := mul_nonneg (abs_nonneg A) (sq_nonneg _)
    have h3 : 0 ≤ |B| * σ n := mul_nonneg (abs_nonneg B) hn0
    linarith
  refine ⟨max (L₁ + σ n) (4 * C / δ),
    le_trans (div_nonneg (by linarith) hδ.le) (le_max_right _ _), fun L hL => ?_⟩
  have hL1 : L₁ + σ n ≤ L := le_trans (le_max_left _ _) hL
  have hLC : 4 * C / δ ≤ L := le_trans (le_max_right _ _) hL
  have hCL : 4 * C ≤ L * δ := (div_le_iff₀ hδ).mp hLC
  have hL0 : 0 ≤ L := by linarith
  have hup := hL₁ (L + σ n) (by linarith)
  have hdn := hL₁ (L - σ n) (by linarith)
  have hlo' := hlo n L
  have hhi' := hhi n L
  simp only [realWeylPolynomial] at hup hdn ⊢
  obtain ⟨hup1, hup2⟩ := abs_le.mp hup
  obtain ⟨hdn1, hdn2⟩ := abs_le.mp hdn
  have hLs : 0 ≤ L * σ n := mul_nonneg hL0 hn0
  have f1 : A * (L * σ n) ≤ |A| * (L * σ n) := mul_le_mul_of_nonneg_right (le_abs_self A) hLs
  have f2 : -(|A| * (L * σ n)) ≤ A * (L * σ n) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le A) hLs
    linarith
  have f3 : |A| * σ n * L ≤ δ / 4 * L := mul_le_mul_of_nonneg_right hAh hL0
  have f4 : A * σ n ^ 2 ≤ |A| * σ n ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self A) (sq_nonneg _)
  have f5 : -(|A| * σ n ^ 2) ≤ A * σ n ^ 2 := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le A) (sq_nonneg (σ n))
    linarith
  have f6 : B * σ n ≤ |B| * σ n := mul_le_mul_of_nonneg_right (le_abs_self B) hn0
  have f7 : -(|B| * σ n) ≤ B * σ n := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le B) hn0
    linarith
  have f8 : 0 ≤ δ / 4 * σ n := mul_nonneg (by positivity) hn0
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Monotone count plus finite kernels of shrinking width: the smoothed sharp law at each fixed
width gives the sharp law for the count. -/
theorem sharp_law_of_finite_kernels {κ : Type*} [Fintype κ] (N : ℝ → ℝ) (hN : Monotone N)
    (A B : ℝ) (w t : ℕ → κ → ℝ) (σ : ℕ → ℝ)
    (hw : ∀ n k, 0 ≤ w n k) (hsum : ∀ n, ∑ k, w n k = 1) (ht : ∀ n k, -1 ≤ t n k ∧ t n k ≤ 1)
    (hσ : ∀ n, 0 ≤ σ n) (hsmall : ∀ ε, 0 < ε → ∃ n, σ n ≤ ε)
    (hS : ∀ n, HasSharpRealLaw (smooth (w n) (t n) (σ n) N) A B) :
    HasSharpRealLaw N A B :=
  sharp_law_of_shrinking_scales N A B (fun n => smooth (w n) (t n) (σ n) N) σ hσ
    (fun n x => (smooth_sandwich N hN (w n) (t n) (hw n) (hsum n) (ht n) (σ n) x (hσ n)).1)
    (fun n x => (smooth_sandwich N hN (w n) (t n) (hw n) (hsum n) (ht n) (σ n) x (hσ n)).2)
    hS hsmall

end SteklovAudit.FixedScaleTauberian
