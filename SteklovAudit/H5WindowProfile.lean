import Mathlib
import SteklovAudit.H5LipRows

/-!
# G6: the Lipschitz rows for a translated window profile

Roadmap item G6. The test is one fixed profile `φ` translated to the energy window,
`x ↦ φ (x - L)`. Hypotheses are on `φ` only:

* `φ` is differentiable with `|φ' t| ≤ Λ0` for all `t`;
* left tail: `∀ R t, t ≤ -R → |φ' t| ≤ ψ R`.

Results:

* `hasDerivAt_shift`, `deriv_shift`, `differentiable_shift`: the derivative of `x ↦ φ (x - L)`;
* `lipHi_of_profile`: the `lipHi` inequality with constant `Λ0` (via G5's `lipHi_of_deriv_bound`);
* `lipLo_of_profile`: for `M + R ≤ L`, low-energy pairs satisfy the `lipLo` inequality with
  constant `ψ R` (via G5's `lipLo_of_deriv_bound_le`);
* `lipHi_field_profile`, `lipLo_field_profile`: the same in the shape of the `H5bInputs` fields,
  for the test `F ε γ L x = φ (x - L)`.

So the F-table row "Lipschitz-type bounds Λ, λ" becomes a property of one fixed profile,
independent of the operator, whenever the smoothed count has this translated form.

What this file does NOT prove: that the paper's smoothed counting function has the translated form
`φ (x - L)`; that `ψ R → 0` (it is not even assumed here; G7 uses it for `lamVanish`); any other
field of `H5bInputs`; anything about the Steklov operator. (7.29) and Theorem 1.3 / 11.1 remain
conditional.
-/

namespace SteklovAudit.H5WindowProfile

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5LipRows

/-- Derivative of the translated profile. -/
theorem hasDerivAt_shift {φ : ℝ → ℝ} (hd : Differentiable ℝ φ) (L x : ℝ) :
    HasDerivAt (fun y => φ (y - L)) (deriv φ (x - L)) x := by
  have h : HasDerivAt φ (deriv φ (x - L)) (x - L) := (hd (x - L)).hasDerivAt
  first
    | exact h.comp_sub_const x L
    | exact HasDerivAt.comp_sub_const x L h
    | (have h2 : HasDerivAt (fun y : ℝ => y - L) 1 x := by
          first
            | exact (hasDerivAt_id' x).sub_const L
            | exact (hasDerivAt_id x).sub_const L
       have h3 := HasDerivAt.comp x h h2
       rw [mul_one] at h3
       exact h3)

theorem deriv_shift {φ : ℝ → ℝ} (hd : Differentiable ℝ φ) (L x : ℝ) :
    deriv (fun y => φ (y - L)) x = deriv φ (x - L) :=
  (hasDerivAt_shift hd L x).deriv

theorem differentiable_shift {φ : ℝ → ℝ} (hd : Differentiable ℝ φ) (L : ℝ) :
    Differentiable ℝ (fun y => φ (y - L)) :=
  fun x => (hasDerivAt_shift hd L x).differentiableAt

/-- The `lipHi` inequality for the translated profile, with constant `Λ0`. -/
theorem lipHi_of_profile {ι κ : Type*} (D : Data ι κ) (M L : ℝ) {φ : ℝ → ℝ} {Λ0 : ℝ}
    (hd : Differentiable ℝ φ) (hb : ∀ t, |deriv φ t| ≤ Λ0) :
    ∀ (i : ι) (j : κ), hiE D M i j →
      |φ (D.a i - L) - φ (D.b j - L)| ≤ Λ0 * |D.a i - D.b j| :=
  lipHi_of_deriv_bound D (fun y => φ (y - L)) M Λ0 (differentiable_shift hd L)
    (fun x => by rw [deriv_shift hd L x, Real.norm_eq_abs]; exact hb (x - L))

/-- The `lipLo` inequality for the translated profile: for `M + R ≤ L`, low-energy pairs
satisfy it with constant `ψ R`. -/
theorem lipLo_of_profile {ι κ : Type*} (D : Data ι κ) {M L R : ℝ} {φ ψ : ℝ → ℝ}
    (hd : Differentiable ℝ φ) (htail : ∀ R t, t ≤ -R → |deriv φ t| ≤ ψ R) (hL : M + R ≤ L) :
    ∀ (i : ι) (j : κ), ¬ hiE D M i j →
      |φ (D.a i - L) - φ (D.b j - L)| ≤ ψ R * |D.a i - D.b j| :=
  lipLo_of_deriv_bound_le D (fun y => φ (y - L)) M (ψ R)
    (fun x _ => differentiable_shift hd L x)
    (fun x hx => by
      have hx' : x ≤ M := hx
      rw [deriv_shift hd L x, Real.norm_eq_abs]
      exact htail R (x - L) (by linarith))

/-- The field `lipHi` of `H5bInputs` for the test `F ε γ L x = φ (x - L)`. -/
theorem lipHi_field_profile {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) {φ : ℝ → ℝ} {Λ0 : ℝ}
    (hd : Differentiable ℝ φ) (hb : ∀ t, |deriv φ t| ≤ Λ0) :
    ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), hiE (D ε γ L) M i j →
      |φ ((D ε γ L).a i - L) - φ ((D ε γ L).b j - L)|
        ≤ Λ0 * |(D ε γ L).a i - (D ε γ L).b j| :=
  fun ε γ M L => lipHi_of_profile (D ε γ L) M L hd hb

/-- The field `lipLo` of `H5bInputs` for the translated profile, with
`lam ε γ M L = ψ (L - M)` (take `R = L - M`). -/
theorem lipLo_field_profile {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) {φ ψ : ℝ → ℝ}
    (hd : Differentiable ℝ φ) (htail : ∀ R t, t ≤ -R → |deriv φ t| ≤ ψ R) :
    ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), ¬ hiE (D ε γ L) M i j →
      |φ ((D ε γ L).a i - L) - φ ((D ε γ L).b j - L)|
        ≤ ψ (L - M) * |(D ε γ L).a i - (D ε γ L).b j| :=
  fun ε γ M L => lipLo_of_profile (D ε γ L) (R := L - M) hd htail (by linarith)

end SteklovAudit.H5WindowProfile
