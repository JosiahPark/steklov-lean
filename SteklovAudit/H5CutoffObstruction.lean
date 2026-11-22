import Mathlib

/-!
# The full-trace condition cannot be dropped (roadmap item G123)

Block example from the 2026-11-22 review. Probe `j` lives on a 2-dimensional block with eigenvalues
`2j` and `2j + 2`, overlap weights `1/2, 1/2`, and comparison value `μ_j = 2j + 1`; the multiplier is
`F x = cos (π x)` (Lipschitz constant `π`). For each probe: mass `1`, squared defect `1`, first moment
`0`, centered value `2`. For the first `n` probes and the cutoff `L = 4n`: every eigenvalue is below the
cutoff (so the truncated trace equals the full trace `S = 2n`), the cutoff ratio
`π · n / (4n − (2n − 1)) = π n / (2n + 1)` is at most `π / 2` and hence eventually `≤ η L`, and with
`D(4n) := 2n` truncated-trace matching is exact; yet `D(4n) / (4n) = 1/2`, so `D` is not `o(L)`.
So estimates (i) and (ii) of `H5CutoffInterface` do not imply `D = o(L)` without (iii) of
`H5CutoffTerminal`.

This is an obstruction to the abstract implication only, stated in scalar form. It is NOT a
counterexample to the tetrahedral theorem and says nothing about the Dirichlet-to-Neumann operator,
(7.29), H5 or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.H5CutoffObstruction

/-- The multiplier `F x = cos (π x)`. -/
noncomputable def F (x : ℝ) : ℝ := Real.cos (x * Real.pi)

/-- Lower eigenvalue of block `j`. -/
noncomputable def lo (j : ℕ) : ℝ := 2 * j
/-- Upper eigenvalue of block `j`. -/
noncomputable def hi (j : ℕ) : ℝ := 2 * j + 2
/-- Comparison value of probe `j`. -/
noncomputable def mu (j : ℕ) : ℝ := 2 * j + 1

theorem cos_even (j : ℕ) : Real.cos ((2 * j : ℝ) * Real.pi) = 1 := by
  have h := Real.cos_nat_mul_pi (2 * j)
  push_cast at h
  rw [h, pow_mul]
  norm_num

theorem cos_odd (j : ℕ) : Real.cos ((2 * j + 1 : ℝ) * Real.pi) = -1 := by
  have h := Real.cos_nat_mul_pi (2 * j + 1)
  push_cast at h
  rw [h, pow_succ, pow_mul]
  norm_num

theorem cos_even_succ (j : ℕ) : Real.cos ((2 * j + 2 : ℝ) * Real.pi) = 1 := by
  have h := cos_even (j + 1)
  push_cast at h
  rw [show (2 * (j : ℝ) + 2) = 2 * ((j : ℝ) + 1) by ring]
  exact h

/-- Mass of probe `j`. -/
theorem block_mass (j : ℕ) : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num

/-- Squared defect of probe `j`. -/
theorem block_defect (j : ℕ) :
    (lo j - mu j) ^ 2 * (1 / 2) + (hi j - mu j) ^ 2 * (1 / 2) = 1 := by
  unfold lo hi mu
  ring

/-- First moment of probe `j`. -/
theorem block_first_moment (j : ℕ) :
    (lo j - mu j) * (1 / 2) + (hi j - mu j) * (1 / 2) = 0 := by
  unfold lo hi mu
  ring

/-- Centered value of probe `j`. -/
noncomputable def centered (j : ℕ) : ℝ :=
  (F (lo j) - F (mu j)) * (1 / 2) + (F (hi j) - F (mu j)) * (1 / 2)

theorem block_centered (j : ℕ) : centered j = 2 := by
  unfold centered F lo hi mu
  rw [cos_even, cos_odd, cos_even_succ]
  norm_num

/-- The full centered trace of the first `n` probes is `2n`. -/
theorem obstruction_sum (n : ℕ) : ∑ j ∈ Finset.range n, centered j = 2 * n := by
  have h : ∀ j ∈ Finset.range n, centered j = 2 := fun j _ => block_centered j
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The summed squared defect of the first `n` probes is `n`. -/
theorem obstruction_defect_sum (n : ℕ) :
    ∑ j ∈ Finset.range n, ((lo j - mu j) ^ 2 * (1 / 2) + (hi j - mu j) ^ 2 * (1 / 2)) = n := by
  have h : ∀ j ∈ Finset.range n,
      (lo j - mu j) ^ 2 * (1 / 2) + (hi j - mu j) ^ 2 * (1 / 2) = 1 := fun j _ => block_defect j
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- Every eigenvalue of the first `n` probes lies below the cutoff `4n`. -/
theorem obstruction_below_cutoff (n j : ℕ) (hj : j < n) : lo j < 4 * n ∧ hi j < 4 * n := by
  have h1 : j + 1 ≤ n := hj
  have h2 : (j : ℝ) + 1 ≤ n := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold lo hi
  constructor <;> linarith

/-- The cutoff ratio `Lip(F) · E / (L − μ*) = π n / (4n − (2n − 1))` is at most `π / 2`. -/
theorem obstruction_ratio_le (n : ℕ) :
    Real.pi * n / ((4 * n : ℝ) - (2 * n - 1)) ≤ Real.pi / 2 := by
  have e : (4 * n : ℝ) - (2 * n - 1) = 2 * n + 1 := by ring
  have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
  rw [e]
  have hpi := Real.pi_pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  first
    | (rw [div_le_iff₀ hpos]; nlinarith)
    | (rw [div_le_iff hpos]; nlinarith)

/-- Estimate (i) holds along `L = 4n`: the ratio is eventually `≤ η L`. -/
theorem obstruction_ratio_small (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.pi * n / ((4 * n : ℝ) - (2 * n - 1)) ≤ η * (4 * n) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.pi / (8 * η))
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h8 : (0 : ℝ) < 8 * η := by linarith
  have hη0 : η ≠ 0 := hη.ne'
  have hq : Real.pi / (8 * η) * (8 * η) = Real.pi := by
    first
      | exact div_mul_cancel₀ _ h8.ne'
      | field_simp
  have hlt : 8 * η * (Real.pi / (8 * η)) < 8 * η * n :=
    mul_lt_mul_of_pos_left (lt_of_lt_of_le hN hn') h8
  have hr := obstruction_ratio_le n
  linarith

/-- With `D(4n) := 2n`, `D(4n) / (4n) = 1/2` for every `n ≥ 1`: `D` is not `o(L)`. -/
theorem obstruction_D_ratio (n : ℕ) (hn : 0 < n) : (2 * n : ℝ) / (4 * n) = 1 / 2 := by
  have h : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  first
    | (field_simp; ring)
    | field_simp
    | (rw [div_eq_iff (by positivity)]; ring)

end SteklovAudit.H5CutoffObstruction
