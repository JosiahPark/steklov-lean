import Mathlib

/-!
# Second-order Taylor remainder from a Lipschitz derivative (roadmap item G125)

If `F` is differentiable on `ℝ` with derivative `F'`, and `F'` is `B`-Lipschitz, then
`|F x − F y − F' y (x − y)| ≤ (B/2) (x − y)²` (`taylor_remainder_of_lipschitz_deriv`). This is the
calculus input of the centered-trace bound (`ReviewExtensions.countable_centered_remainder_bound`
with `C = B/2`). Proof: the functions `t ↦ F t − F y − F' y (t − y) ∓ (B/2)(t − y)²` are monotone on each
side of `y`, by the mean value theorem (`exists_hasDerivAt_eq_slope`).

What this file does NOT prove: anything about spectral multipliers of the Dirichlet-to-Neumann operator,
the regularity of the paper's smoothing functions, (7.29), or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.TaylorRemainder

/-- Mean value theorem, sign form: a nonpositive derivative on `(p, q)` gives `g q ≤ g p`. -/
theorem le_of_deriv_nonpos {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) {p q : ℝ}
    (hpq : p < q) (hs : ∀ c, p < c → c < q → g' c ≤ 0) : g q ≤ g p := by
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' hpq
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hqp : 0 < q - p := sub_pos.mpr hpq
  have h1 := hs c hc.1 hc.2
  rw [hcs] at h1
  by_contra hneg
  push_neg at hneg
  have := div_pos (sub_pos.mpr hneg) hqp
  linarith

/-- Mean value theorem, sign form: a nonnegative derivative on `(p, q)` gives `g p ≤ g q`. -/
theorem le_of_deriv_nonneg {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) {p q : ℝ}
    (hpq : p < q) (hs : ∀ c, p < c → c < q → 0 ≤ g' c) : g p ≤ g q := by
  have h := le_of_deriv_nonpos (g := fun t => -g t) (g' := fun t => -g' t)
    (fun t => (hg t).neg) hpq (fun c h1 h2 => by have := hs c h1 h2; linarith)
  have h' : -g q ≤ -g p := h
  linarith

/-- Derivative of `t ↦ F t − F y − F' y (t − y) + k (t − y)²`. -/
theorem hasDerivAt_aux (F F' : ℝ → ℝ) (hd : ∀ x, HasDerivAt F (F' x) x) (y k t : ℝ) :
    HasDerivAt (fun s => F s - F y - F' y * (s - y) + k * ((s - y) * (s - y)))
      (F' t - F' y + 2 * k * (t - y)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s - y) 1 t := (hasDerivAt_id t).sub_const y
  have h3 := (((hd t).sub_const (F y)).sub (h1.const_mul (F' y))).add ((h1.mul h1).const_mul k)
  convert h3 using 1
  ring

/-- Upper half of the remainder bound. -/
theorem taylor_upper (F F' : ℝ → ℝ) (B : ℝ) (hd : ∀ x, HasDerivAt F (F' x) x)
    (hL : ∀ x y, |F' x - F' y| ≤ B * |x - y|) (x y : ℝ) :
    F x - F y - F' y * (x - y) ≤ B / 2 * ((x - y) * (x - y)) := by
  have hG := hasDerivAt_aux F F' hd y (-(B / 2))
  rcases lt_trichotomy x y with h | h | h
  · have hm := le_of_deriv_nonneg hG h (fun c hc1 hc2 => by
      have hl := hL c y
      have hcy : |c - y| = y - c := by rw [abs_of_neg (by linarith)]; ring
      rw [hcy] at hl
      have := neg_abs_le (F' c - F' y)
      nlinarith)
    have hm' : F x - F y - F' y * (x - y) + -(B / 2) * ((x - y) * (x - y)) ≤
        F y - F y - F' y * (y - y) + -(B / 2) * ((y - y) * (y - y)) := hm
    nlinarith [hm']
  · subst h
    simp
  · have hm := le_of_deriv_nonpos hG h (fun c hc1 hc2 => by
      have hl := hL c y
      have hcy : |c - y| = c - y := abs_of_pos (by linarith)
      rw [hcy] at hl
      have := le_abs_self (F' c - F' y)
      nlinarith)
    have hm' : F x - F y - F' y * (x - y) + -(B / 2) * ((x - y) * (x - y)) ≤
        F y - F y - F' y * (y - y) + -(B / 2) * ((y - y) * (y - y)) := hm
    nlinarith [hm']

/-- Lower half of the remainder bound. -/
theorem taylor_lower (F F' : ℝ → ℝ) (B : ℝ) (hd : ∀ x, HasDerivAt F (F' x) x)
    (hL : ∀ x y, |F' x - F' y| ≤ B * |x - y|) (x y : ℝ) :
    -(B / 2 * ((x - y) * (x - y))) ≤ F x - F y - F' y * (x - y) := by
  have hG := hasDerivAt_aux F F' hd y (B / 2)
  rcases lt_trichotomy x y with h | h | h
  · have hm := le_of_deriv_nonpos hG h (fun c hc1 hc2 => by
      have hl := hL c y
      have hcy : |c - y| = y - c := by rw [abs_of_neg (by linarith)]; ring
      rw [hcy] at hl
      have := le_abs_self (F' c - F' y)
      nlinarith)
    have hm' : F y - F y - F' y * (y - y) + B / 2 * ((y - y) * (y - y)) ≤
        F x - F y - F' y * (x - y) + B / 2 * ((x - y) * (x - y)) := hm
    nlinarith [hm']
  · subst h
    simp
  · have hm := le_of_deriv_nonneg hG h (fun c hc1 hc2 => by
      have hl := hL c y
      have hcy : |c - y| = c - y := abs_of_pos (by linarith)
      rw [hcy] at hl
      have := neg_abs_le (F' c - F' y)
      nlinarith)
    have hm' : F y - F y - F' y * (y - y) + B / 2 * ((y - y) * (y - y)) ≤
        F x - F y - F' y * (x - y) + B / 2 * ((x - y) * (x - y)) := hm
    nlinarith [hm']

/-- **G125.** `C¹,¹` regularity with constant `B` gives the second-order remainder `B/2`. -/
theorem taylor_remainder_of_lipschitz_deriv (F F' : ℝ → ℝ) (B : ℝ)
    (hd : ∀ x, HasDerivAt F (F' x) x) (hL : ∀ x y, |F' x - F' y| ≤ B * |x - y|) (x y : ℝ) :
    |F x - F y - F' y * (x - y)| ≤ B / 2 * (x - y) ^ 2 := by
  have hu := taylor_upper F F' B hd hL x y
  have hl := taylor_lower F F' B hd hL x y
  have e : (x - y) ^ 2 = (x - y) * (x - y) := by ring
  rw [e, abs_le]
  constructor <;> linarith

end SteklovAudit.TaylorRemainder
