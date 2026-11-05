import Mathlib
import SteklovAudit.H5WindowProfile

/-!
# G8: non-vacuity of the window-profile rows (G6/G7)

Roadmap item G8. `φ := Real.arctan` satisfies every hypothesis of `ProfileLipRows`
(`H5WindowProfile.lean`) with `Λ0 = 1` and left-tail bound
`ψ R = 1 / (1 + (max R 0) ^ 2)` (equal to `1 / (1 + R ^ 2)` for `R ≥ 0`; the `max` makes the
bound valid for every `R`, as the field `htail` requires). Results:

* `arctan_hasDerivAt'`, `arctan_deriv_eq`, `arctan_differentiable'`: derivative of `arctan`;
* `arctan_deriv_le_one`: `|arctan' t| ≤ 1`;
* `arctan_tail`: `t ≤ -R → |arctan' t| ≤ arctanTail R`;
* `arctanTail_small`: `arctanTail R ≤ η` for `R ≥ max 1 (1/η)`;
* `arctanProfile : ProfileLipRows` and `arctan_lipGroup` (G7's five fields for this profile);
* `arctan_profile_nonjunk`: `arctan 1 - arctan 0 ≠ 0`, and `arctan_shift_nonconst`: for every `L`
  the translated test `x ↦ arctan (x - L)` is non-constant, so the rows are not met by a trivial test.

What this file does NOT prove: that the paper's smoothed counting function is `arctan (x - L)` or
has the translated form at all; any field of `H5bInputs` other than the Lipschitz group; anything
about the Steklov operator. (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5WindowWitness

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5WindowProfile

theorem arctan_hasDerivAt' (t : ℝ) : HasDerivAt Real.arctan (1 / (1 + t ^ 2)) t := by
  first
    | exact Real.hasDerivAt_arctan t
    | simpa using Real.hasDerivAt_arctan t

theorem arctan_deriv_eq (t : ℝ) : deriv Real.arctan t = 1 / (1 + t ^ 2) :=
  (arctan_hasDerivAt' t).deriv

theorem arctan_differentiable' : Differentiable ℝ Real.arctan :=
  fun t => (arctan_hasDerivAt' t).differentiableAt

theorem arctan_deriv_le_one (t : ℝ) : |deriv Real.arctan t| ≤ 1 := by
  rw [arctan_deriv_eq]
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hq : 0 < 1 / (1 + t ^ 2) := one_div_pos.mpr hp
  rw [abs_of_pos hq]
  have hx : 1 / (1 + t ^ 2) * (1 + t ^ 2) = 1 := by
    first | exact one_div_mul_cancel hp.ne' | field_simp
  nlinarith [sq_nonneg t]

/-- Left-tail bound for `arctan'`. -/
noncomputable def arctanTail (R : ℝ) : ℝ := 1 / (1 + (max R 0) ^ 2)

theorem arctan_tail (R t : ℝ) (ht : t ≤ -R) : |deriv Real.arctan t| ≤ arctanTail R := by
  rw [arctan_deriv_eq]
  have hp : 0 < 1 + t ^ 2 := by positivity
  rw [abs_of_pos (one_div_pos.mpr hp)]
  unfold arctanTail
  have hm0 : 0 ≤ max R 0 := le_max_right _ _
  have hmt : max R 0 ≤ |t| :=
    max_le (by rcases abs_cases t with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith) (abs_nonneg t)
  have hsq : (max R 0) ^ 2 ≤ t ^ 2 := by
    have h1 := mul_le_mul hmt hmt hm0 (abs_nonneg t)
    have h2 := sq_abs t
    nlinarith
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem arctanTail_small (η : ℝ) (hη : 0 < η) :
    ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → arctanTail R ≤ η := by
  refine ⟨max 1 (1 / η), fun R hR => ?_⟩
  have h1 : 1 / η ≤ R := le_trans (le_max_right _ _) hR
  have h2 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
  unfold arctanTail
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ R)]
  have h3 : η * (1 / η) = 1 := by
    first | exact mul_one_div_cancel hη.ne' | field_simp
  have h4 : 1 ≤ η * R := by nlinarith [mul_le_mul_of_nonneg_left h1 hη.le]
  have h5 : 1 ≤ η * (1 + R ^ 2) := by
    nlinarith [mul_nonneg hη.le (by nlinarith : (0 : ℝ) ≤ R ^ 2 - R)]
  have hp : 0 < 1 + R ^ 2 := by positivity
  have hx : 1 / (1 + R ^ 2) * (1 + R ^ 2) = 1 := by
    first | exact one_div_mul_cancel hp.ne' | field_simp
  nlinarith [one_div_pos.mpr hp]

/-- **G8.** `arctan` is a window profile in the sense of G7. -/
noncomputable def arctanProfile : ProfileLipRows where
  φ := Real.arctan
  ψ := arctanTail
  Λ0 := 1
  hd := arctan_differentiable'
  hb := arctan_deriv_le_one
  htail := arctan_tail
  hψ := arctanTail_small

/-- G7's five Lipschitz-group fields hold for the `arctan` profile (non-vacuity of G6/G7). -/
theorem arctan_lipGroup {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) :
    (∀ _ε _γ : ℝ, (0 : ℝ) ≤ 1) ∧
    (∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), hiE (D ε γ L) M i j →
      |Real.arctan ((D ε γ L).a i - L) - Real.arctan ((D ε γ L).b j - L)|
        ≤ 1 * |(D ε γ L).a i - (D ε γ L).b j|) ∧
    (∀ _ε _γ M L : ℝ, 0 ≤ profLam 1 arctanTail M L) ∧
    (∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), ¬ hiE (D ε γ L) M i j →
      |Real.arctan ((D ε γ L).a i - L) - Real.arctan ((D ε γ L).b j - L)|
        ≤ profLam 1 arctanTail M L * |(D ε γ L).a i - (D ε γ L).b j|) ∧
    (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      profLam 1 arctanTail M L ≤ η) :=
  lipGroup_of_profile arctanProfile D

/-- The profile is not constant. -/
theorem arctan_profile_nonjunk : Real.arctan 1 - Real.arctan 0 ≠ 0 := by
  have h : Real.arctan 0 < Real.arctan 1 := by
    first
      | exact Real.arctan_strictMono (by norm_num)
      | (rw [Real.arctan_one, Real.arctan_zero]; positivity)
  linarith

/-- For every window position `L`, the translated test is not constant. -/
theorem arctan_shift_nonconst (L : ℝ) :
    Real.arctan ((L + 1) - L) - Real.arctan (L - L) ≠ 0 := by
  have h1 : (L + 1) - L = 1 := by ring
  have h2 : L - L = 0 := by ring
  rw [h1, h2]
  exact arctan_profile_nonjunk

end SteklovAudit.H5WindowWitness
