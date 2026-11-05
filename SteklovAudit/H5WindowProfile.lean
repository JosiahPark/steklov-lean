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

/-! ## G7: `hlam`, `lipLo`, `lamVanish` for the translated profile

`profLam Λ0 ψ M L` is `max (ψ (L - M)) 0` when `M ≤ L` and `Λ0` otherwise. With the left-tail
bound `htail` and its decay `hψ` (fields of `ProfileLipRows`), `lipGroup_of_profile` gives the five
fields `hΛ0`, `lipHi`, `hlam`, `lipLo`, `lamVanish` of `H5bInputs` for the test
`F ε γ L x = φ (x - L)`, with `Λ0 ε γ = Λ0` and `lam ε γ M L = profLam Λ0 ψ M L`.

What this section does NOT prove: that the paper's smoothed count has this translated form (to be
checked on paper), any other field of `H5bInputs`, or anything about the Steklov operator. -/

/-- The low-energy Lipschitz constant for the translated profile. -/
noncomputable def profLam (Λ0 : ℝ) (ψ : ℝ → ℝ) (M L : ℝ) : ℝ :=
  if M ≤ L then max (ψ (L - M)) 0 else Λ0

theorem profLam_nonneg {Λ0 : ℝ} (hΛ0 : 0 ≤ Λ0) (ψ : ℝ → ℝ) (M L : ℝ) :
    0 ≤ profLam Λ0 ψ M L := by
  unfold profLam
  split_ifs
  · exact le_max_right _ _
  · exact hΛ0

/-- The `lipLo` inequality with constant `profLam Λ0 ψ M L`, for every `L`. -/
theorem lipLo_profLam {ι κ : Type*} (D : Data ι κ) {M L : ℝ} {φ ψ : ℝ → ℝ} {Λ0 : ℝ}
    (hd : Differentiable ℝ φ) (hb : ∀ t, |deriv φ t| ≤ Λ0)
    (htail : ∀ R t, t ≤ -R → |deriv φ t| ≤ ψ R) :
    ∀ (i : ι) (j : κ), ¬ hiE D M i j →
      |φ (D.a i - L) - φ (D.b j - L)| ≤ profLam Λ0 ψ M L * |D.a i - D.b j| := by
  intro i j h
  unfold profLam
  split_ifs with hML
  · have h1 := lipLo_of_profile D (M := M) (L := L) (R := L - M) hd htail (by linarith) i j h
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · exact abs_sub_le_of_deriv_bound (differentiable_shift hd L)
      (fun x => by rw [deriv_shift hd L x, Real.norm_eq_abs]; exact hb (x - L)) (D.a i) (D.b j)

/-- `profLam` vanishes as `L → ∞` for fixed `M`, given the decay of `ψ`. -/
theorem profLam_vanish {Λ0 : ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ η : ℝ, 0 < η → ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → ψ R ≤ η)
    (M η : ℝ) (hη : 0 < η) : ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → profLam Λ0 ψ M L ≤ η := by
  obtain ⟨R₀, hR₀⟩ := hψ η hη
  refine ⟨M + max R₀ 0, fun L hL => ?_⟩
  have h1 : R₀ ≤ L - M := by have := le_max_left R₀ 0; linarith
  have h2 : M ≤ L := by have := le_max_right R₀ 0; linarith
  unfold profLam
  rw [if_pos h2]
  exact max_le (hR₀ _ h1) hη.le

/-- `ψ → 0` at `+∞` gives the decay hypothesis `hψ`. -/
theorem eventually_le_of_tendsto {ψ : ℝ → ℝ} (h : Filter.Tendsto ψ Filter.atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η → ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → ψ R ≤ η := by
  intro η hη
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h η hη
  refine ⟨N, fun R hR => ?_⟩
  have h1 := hN R hR
  rw [Real.dist_eq, sub_zero] at h1
  exact le_trans (le_abs_self _) h1.le

/-- A window profile: bounded derivative, with a left-tail derivative bound `ψ` that decays. -/
structure ProfileLipRows where
  φ : ℝ → ℝ
  ψ : ℝ → ℝ
  Λ0 : ℝ
  hd : Differentiable ℝ φ
  hb : ∀ t, |deriv φ t| ≤ Λ0
  htail : ∀ R t, t ≤ -R → |deriv φ t| ≤ ψ R
  hψ : ∀ η : ℝ, 0 < η → ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → ψ R ≤ η

/-- **G7.** The five fields `hΛ0`, `lipHi`, `hlam`, `lipLo`, `lamVanish` of `H5bInputs`, in their
exact shapes, for `F ε γ L x = P.φ (x - L)`, `Λ0 ε γ = P.Λ0`, `lam ε γ M L = profLam P.Λ0 P.ψ M L`. -/
theorem lipGroup_of_profile (P : ProfileLipRows) {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) :
    (∀ _ε _γ : ℝ, 0 ≤ P.Λ0) ∧
    (∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), hiE (D ε γ L) M i j →
      |P.φ ((D ε γ L).a i - L) - P.φ ((D ε γ L).b j - L)|
        ≤ P.Λ0 * |(D ε γ L).a i - (D ε γ L).b j|) ∧
    (∀ _ε _γ M L : ℝ, 0 ≤ profLam P.Λ0 P.ψ M L) ∧
    (∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), ¬ hiE (D ε γ L) M i j →
      |P.φ ((D ε γ L).a i - L) - P.φ ((D ε γ L).b j - L)|
        ≤ profLam P.Λ0 P.ψ M L * |(D ε γ L).a i - (D ε γ L).b j|) ∧
    (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      profLam P.Λ0 P.ψ M L ≤ η) := by
  have hΛ0 : 0 ≤ P.Λ0 := le_trans (abs_nonneg _) (P.hb 0)
  refine ⟨fun _ _ => hΛ0, lipHi_field_profile D P.hd P.hb,
    fun _ _ M L => profLam_nonneg hΛ0 P.ψ M L,
    fun ε γ M L => lipLo_profLam (D ε γ L) (M := M) (L := L) P.hd P.hb P.htail,
    fun _ _ _ _ M η hη => profLam_vanish P.hψ M η hη⟩

end SteklovAudit.H5WindowProfile
