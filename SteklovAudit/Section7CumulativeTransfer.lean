import Mathlib
/-!
Scalar bookkeeping behind the fixed-time cumulative transfer step (7.29).

If a one-step transfer quantity obeys `f (k+1) ≤ f k + e k`, then after `n`
steps it is bounded by the sum of the step errors (telescoping); with a
multiplicative loss `f (k+1) ≤ (1+δ) f k + η` one gets the discrete Grönwall
bound `(1+δ)^n (f 0 + n η)`. If `N` steps of size `h` cover a fixed time
`T = N h` and each step error is at most `ε h`, the cumulative error is at
most `ε T`. Conversely, a uniform per-step error budget alone gives no bound
independent of the number of steps.

What this module does NOT prove: it defines no Dirichlet-to-Neumann operator
or wave group, does not prove the per-step estimate itself, and does not
establish (7.29), the gluing estimate (7.2), or Theorem 1.3 / 11.1. These are
scalar sublemmas only.
-/
namespace SteklovAudit

/-- Telescoping: additive step errors accumulate as their sum. -/
theorem cumulative_transfer_telescope (f e : ℕ → ℝ)
    (h : ∀ k, f (k + 1) ≤ f k + e k) :
    ∀ n : ℕ, f n ≤ f 0 + ∑ k ∈ Finset.range n, e k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [h n]

/-- Discrete Grönwall bound for a transfer with multiplicative loss `1+δ`. -/
theorem transfer_gronwall_bound (f : ℕ → ℝ) (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (h : ∀ k, f (k + 1) ≤ (1 + δ) * f k + η) :
    ∀ n : ℕ, f n ≤ (1 + δ) ^ n * (f 0 + (n : ℝ) * η) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℝ) ≤ (1 + δ) ^ (n + 1) := one_le_pow₀ (by linarith)
    have h2 : (1 + δ) * f n ≤ (1 + δ) * ((1 + δ) ^ n * (f 0 + (n : ℝ) * η)) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h3 : η ≤ (1 + δ) ^ (n + 1) * η := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hη]
    calc f (n + 1) ≤ (1 + δ) * f n + η := h n
      _ ≤ (1 + δ) * ((1 + δ) ^ n * (f 0 + (n : ℝ) * η)) + (1 + δ) ^ (n + 1) * η := by
        linarith
      _ = (1 + δ) ^ (n + 1) * (f 0 + ((n + 1 : ℕ) : ℝ) * η) := by
        push_cast
        ring

/-- Fixed time `T = N h` with per-step error `ε h` gives cumulative error `ε T`. -/
theorem fixed_time_step_budget (N : ℕ) (h T ε : ℝ) (hNT : (N : ℝ) * h = T)
    (e : ℕ → ℝ) (he : ∀ k, e k ≤ ε * h) :
    ∑ k ∈ Finset.range N, e k ≤ ε * T := by
  calc ∑ k ∈ Finset.range N, e k ≤ ∑ _k ∈ Finset.range N, ε * h :=
        Finset.sum_le_sum (fun k _ => he k)
    _ = ε * T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hNT]
        ring

/-- Obstruction: a unit per-step error budget, with the number of steps
unconstrained, admits no uniform cumulative bound. -/
theorem cumulative_transfer_unbounded (C : ℝ) :
    ∃ n : ℕ, C < ∑ _k ∈ Finset.range n, (1 : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt C
  exact ⟨n, by simpa using hn⟩

end SteklovAudit
