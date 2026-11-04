import Mathlib
import SteklovAudit.RealToIntegerLaw

/-!
# D8, D9: from grid-level laws to the real-parameter law

Roadmap items D8 and D9, the converse direction left open by D7 (`RealToIntegerLaw`).
Eigenvalue counts are monotone step functions, so the question is when a law checked on a grid of
spectral levels gives the law for all real `L`.

* D8 `step_integer_law`, `step_not_real_law`: the monotone step function `N(L) = A ⌊L⌋₊²`
  (`A > 0`) satisfies the integer-level law with coefficients `(A, 0)` exactly, but satisfies
  `HasSharpRealLaw N A B` for NO `B`: at half-integers it is off by about `A·L`. So the integer-level
  law of `sharp_integer_law_of_two_scale` does not by itself give Theorem 11.1's real-parameter law,
  even for monotone counts.
* D9 `real_law_of_fine_grids`: if `N` is monotone and the law holds along every grid `k/m`
  (`m ≥ 1`), then `HasSharpRealLaw N A B`. The proof sandwiches `N(L)` between the two neighbouring
  grid points; the Weyl polynomial moves by `O(L/m)` across one cell, which is made small by
  choosing `m`.

What this file does NOT prove: any law for the Steklov count; the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.GridLaw

open SteklovAudit

/-- The step function `A ⌊L⌋₊²`. -/
noncomputable def stepN (A : ℝ) (L : ℝ) : ℝ := A * ((⌊L⌋₊ : ℕ) : ℝ) ^ 2

theorem stepN_monotone (A : ℝ) (hA : 0 ≤ A) : Monotone (stepN A) := by
  intro x y hxy
  unfold stepN
  have h1 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.floor_mono hxy
  have h0 : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : ((⌊x⌋₊ : ℕ) : ℝ) ^ 2 ≤ ((⌊y⌋₊ : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
  exact mul_le_mul_of_nonneg_left h2 hA

theorem stepN_nat (A : ℝ) (n : ℕ) : stepN A ((n : ℝ) + 1) = A * ((n : ℝ) + 1) ^ 2 := by
  unfold stepN
  have h : ⌊((n : ℝ) + 1)⌋₊ = n + 1 := by exact_mod_cast Nat.floor_natCast (n + 1)
  rw [h, Nat.cast_add, Nat.cast_one]

theorem stepN_half (A : ℝ) (n : ℕ) : stepN A ((n : ℝ) + 1 / 2) = A * (n : ℝ) ^ 2 := by
  unfold stepN
  have h : ⌊((n : ℝ) + 1 / 2)⌋₊ = n := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  rw [h]

/-- D8. The step function obeys the integer-level law exactly. -/
theorem step_integer_law (A : ℝ) :
    HasSharpTwoTermLawOnIntegers (fun n => stepN A ((n : ℝ) + 1)) A 0 := by
  intro δ hδ
  refine ⟨0, fun n _ => ?_⟩
  show |stepN A ((n : ℝ) + 1) - twoTermPolynomial A 0 n| ≤ δ * ((n : ℝ) + 1)
  rw [stepN_nat]
  unfold twoTermPolynomial
  rw [show A * ((n : ℝ) + 1) ^ 2 - (A * ((n : ℝ) + 1) ^ 2 + 0 * ((n : ℝ) + 1)) = 0 by ring,
    abs_zero]
  have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  exact mul_nonneg hδ.le this

/-- D8. For `A > 0` the step function obeys the real-parameter law for no `B`. -/
theorem step_not_real_law (A B : ℝ) (hA : 0 < A) : ¬ HasSharpRealLaw (stepN A) A B := by
  intro h
  obtain ⟨L₀, hL₀, hL⟩ := h (A / 4) (by linarith)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, L₀ + 1 ≤ (n : ℝ) :=
    ⟨⌈L₀⌉₊ + 1, by push_cast; linarith [Nat.le_ceil L₀]⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have e1 := abs_le.mp (hL ((n : ℝ) + 1) (by linarith))
  have e2 := abs_le.mp (hL ((n : ℝ) + 1 / 2) (by linarith))
  rw [stepN_nat] at e1
  rw [stepN_half] at e2
  unfold realWeylPolynomial at e1 e2
  -- integer points: |B| ≤ A/4
  have hB1 : B * ((n : ℝ) + 1) ≤ A / 4 * ((n : ℝ) + 1) := by linarith [e1.1]
  have hB2 : -(A / 4 * ((n : ℝ) + 1)) ≤ B * ((n : ℝ) + 1) := by linarith [e1.2]
  have hBlo : -(A / 4) ≤ B := by
    by_contra hc
    push_neg at hc
    have := mul_lt_mul_of_pos_right hc (by linarith : (0 : ℝ) < (n : ℝ) + 1)
    linarith
  -- half-integer point
  have hhalf : (A + B) * ((n : ℝ) + 1 / 2) - A / 4 ≤ A / 4 * ((n : ℝ) + 1 / 2) := by
    nlinarith [e2.1]
  have hge : (A / 2) * ((n : ℝ) + 1 / 2) ≤ (A + B - A / 4) * ((n : ℝ) + 1 / 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

/-- D9. A monotone count obeying the law along every grid `k/m` obeys the real-parameter law. -/
theorem real_law_of_fine_grids (N : ℝ → ℝ) (A B : ℝ) (hN : Monotone N)
    (hgrid : ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      |N ((k : ℝ) / m) - realWeylPolynomial A B ((k : ℝ) / m)| ≤ δ * ((k : ℝ) / m)) :
    HasSharpRealLaw N A B := by
  intro ε hε
  set K : ℝ := 3 * |A| + |B| with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * K / ε + 1 ≤ (m : ℝ) :=
    ⟨⌈2 * K / ε⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (2 * K / ε)]⟩
  have hm1 : (1 : ℝ) ≤ m := by
    have : 0 ≤ 2 * K / ε := div_nonneg (by linarith) hε.le
    linarith
  have hm0 : 0 < m := by exact_mod_cast (lt_of_lt_of_le one_pos hm1)
  have hmpos : (0 : ℝ) < m := by linarith
  have hm0' : (m : ℝ) ≠ 0 := hmpos.ne'
  have hε0 : ε ≠ 0 := hε.ne'
  have hKm : K / m ≤ ε / 2 := by
    rw [div_le_iff₀ hmpos]
    have h1 : 2 * K / ε * ε = 2 * K := div_mul_cancel₀ (2 * K) hε0
    have h2 : 2 * K / ε ≤ (m : ℝ) := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hε.le
    linarith
  obtain ⟨k₀, hk₀⟩ := hgrid m hm0 (ε / 4) (by linarith)
  refine ⟨((k₀ : ℝ) + 1) / m + 1, by positivity, ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ ((k₀ : ℝ) + 1) / m := by positivity
    linarith
  have hL0 : 0 ≤ L := by linarith
  set k : ℕ := ⌊(m : ℝ) * L⌋₊ with hkdef
  have hmL0 : 0 ≤ (m : ℝ) * L := mul_nonneg hmpos.le hL0
  have hk_le : (k : ℝ) ≤ (m : ℝ) * L := Nat.floor_le hmL0
  have hk_lt : (m : ℝ) * L < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  -- grid neighbours x = k/m ≤ L < y = (k+1)/m
  have hx : (k : ℝ) / m ≤ L := by rw [div_le_iff₀ hmpos]; linarith
  have hy : L ≤ ((k + 1 : ℕ) : ℝ) / m := by
    rw [le_div_iff₀ hmpos]; push_cast; linarith
  have hyx : ((k + 1 : ℕ) : ℝ) / m = (k : ℝ) / m + 1 / m := by push_cast; ring
  have hinv : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one hmpos]; exact hm1
  have hinv0 : 0 < 1 / (m : ℝ) := by positivity
  have hxL : L - 1 / m ≤ (k : ℝ) / m := by
    have : (m : ℝ) * L - 1 < k := by linarith
    rw [le_div_iff₀ hmpos]
    have e : (L - 1 / m) * m = (m : ℝ) * L - 1 := by
      rw [sub_mul, one_div_mul_cancel hm0']
      ring
    linarith
  -- k is large
  have hkk : k₀ ≤ k := by
    have h1 : ((k₀ : ℝ) + 1) / m + 1 ≤ L := hL
    have h2 : (k₀ : ℝ) + 1 ≤ (m : ℝ) * L := by
      have h3 : ((k₀ : ℝ) + 1) / m ≤ L := by linarith
      rw [div_le_iff₀ hmpos] at h3
      linarith
    have h4 : (k₀ : ℝ) < (k : ℝ) + 1 := by linarith
    have h5 : k₀ < k + 1 := by exact_mod_cast h4
    omega
  have gx := abs_le.mp (hk₀ k hkk)
  have gy := abs_le.mp (hk₀ (k + 1) (by omega))
  have nx : N ((k : ℝ) / m) ≤ N L := hN hx
  have ny : N L ≤ N (((k + 1 : ℕ) : ℝ) / m) := hN hy
  rw [hyx] at gy ny hy
  set x : ℝ := (k : ℝ) / m with hxdef
  set h : ℝ := 1 / (m : ℝ) with hhdef
  unfold realWeylPolynomial at gx gy ⊢
  -- polynomial increments across one cell
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hLx : L - x ≤ h := by linarith
  have hxL' : x ≤ L := hx
  have p1 : 0 ≤ x + h - L := by linarith
  have p2 : x + h - L ≤ h := by linarith
  have p3 : 0 ≤ x + h + L := by linarith
  have p4 : x + h + L ≤ 3 * L := by linarith
  have q1 : 0 ≤ L - x := by linarith
  have q3 : 0 ≤ L + x := by linarith
  have q4 : L + x ≤ 3 * L := by linarith
  have hhL : h ≤ L * h := by
    have := mul_le_mul_of_nonneg_right hL1 hinv0.le
    linarith
  have m1 := mul_le_mul p2 p4 p3 hinv0.le
  have m2 := mul_le_mul hLx q4 q3 hinv0.le
  have m3 := mul_nonneg p1 p3
  have m4 := mul_nonneg q1 q3
  have incA1 : |A * ((x + h) ^ 2 - L ^ 2)| ≤ |A| * (3 * L * h) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
    rw [abs_le]
    constructor <;> nlinarith
  have incA2 : |A * (L ^ 2 - x ^ 2)| ≤ |A| * (3 * L * h) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
    rw [abs_le]
    constructor <;> nlinarith
  have incB1 : |B * (x + h - L)| ≤ |B| * (L * h) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg B)
    rw [abs_le]
    constructor <;> linarith
  have incB2 : |B * (L - x)| ≤ |B| * (L * h) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg B)
    rw [abs_le]
    constructor <;> linarith
  have hKh : K * h ≤ ε / 2 := by rw [hhdef]; rw [mul_one_div]; exact hKm
  have hsum : |A| * (3 * L * h) + |B| * (L * h) ≤ ε / 2 * L := by
    have : |A| * (3 * L * h) + |B| * (L * h) = (K * h) * L := by rw [hK]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hKh hL0
  have a1 := abs_le.mp incA1
  have a2 := abs_le.mp incA2
  have b1 := abs_le.mp incB1
  have b2 := abs_le.mp incB2
  have hxh : x + h ≤ L + 1 := by linarith
  have hε4 : (0 : ℝ) ≤ ε / 4 := by linarith
  have hδy : ε / 4 * (x + h) ≤ ε / 2 * L := by
    have := mul_le_mul_of_nonneg_left (by linarith : x + h ≤ 2 * L) hε4
    linarith
  have hδx : ε / 4 * x ≤ ε / 2 * L := by
    have := mul_le_mul_of_nonneg_left (by linarith : x ≤ 2 * L) hε4
    linarith
  rw [abs_le]
  constructor
  · linarith [gx.1, nx, a2.1, a2.2, b2.1, b2.2, hsum, hδx]
  · linarith [gy.2, ny, a1.1, a1.2, b1.1, b1.2, hsum, hδy]

end SteklovAudit.GridLaw
