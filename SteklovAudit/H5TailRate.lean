import Mathlib
import SteklovAudit.H5Compare

/-!
# G9: the high-energy tail row as a decay rate

Roadmap item G9. The row "high-energy defect tail τ(M), σ(M) → 0" of the section F table enters
`H5bInputs` through the field `tailVanish` (for each `δ > 0` some split energy `M` has
`τ ε γ M ≤ δ`). Here that field is reduced to a power-type decay rate stated on `τ` alone:

* `TailRate τ C`: `0 ≤ C ε γ` and `τ ε γ M ≤ C ε γ / M` for every `M ≥ 1`;
* `tailVanish_of_power`: `TailRate τ C` implies the `tailVanish` field;
* `tailVanish_field`: the same, stated for the `τ` of a given `H5bInputs`;
* `invRate`, `invRate_vanish`: non-vacuity (`τ = 1/M`, `C = 1`);
* `tail_rate_not_target`: `TailRate` holds for `τ = 1/M` while `H5bTarget` fails for the counts
  `E = 2L`, `Emod = 0`. `TailRate` is a `Prop` on `τ` and `C` only and mentions neither `E` nor
  `Emod`, so the F2 "target in disguise" audit applies to it by construction.

What this file does NOT prove: no bound `τ(M) ≤ C/M` (or any decay) for the high-energy masked
defect of the Steklov operator of the tetrahedron; no field of `H5bInputs` other than `tailVanish`
is touched; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5TailRate

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- Power-type decay of the high-energy tail, stated on `τ` alone. -/
def TailRate (τ : ℝ → ℝ → ℝ → ℝ) (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε γ : ℝ, 0 ≤ C ε γ ∧ ∀ M : ℝ, 1 ≤ M → τ ε γ M ≤ C ε γ / M

theorem div_le_of_rate {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) : C / (C / δ + 1) ≤ δ := by
  have hq : 0 ≤ C / δ := div_nonneg hC hδ.le
  have hM : 0 < C / δ + 1 := by linarith
  have h : δ * (C / δ) = C := by
    first
      | exact mul_div_cancel₀ C hδ.ne'
      | (field_simp; done)
      | (field_simp; ring)
  have h2 : δ * (C / δ + 1) = C + δ := by rw [mul_add, h, mul_one]
  first
    | (rw [div_le_iff₀ hM]; linarith)
    | (rw [div_le_iff hM]; linarith)

/-- **G9.** A decay rate `τ ≤ C / M` gives the `tailVanish` field of `H5bInputs`. -/
theorem tailVanish_of_power {τ : ℝ → ℝ → ℝ → ℝ} {C : ℝ → ℝ → ℝ} (h : TailRate τ C) :
    ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ → ∃ M, τ ε γ M ≤ δ := by
  intro ε γ _ _ δ hδ
  obtain ⟨hC, hr⟩ := h ε γ
  refine ⟨C ε γ / δ + 1, ?_⟩
  have hq : 0 ≤ C ε γ / δ := div_nonneg hC hδ.le
  have h1 : (1 : ℝ) ≤ C ε γ / δ + 1 := by linarith
  exact le_trans (hr _ h1) (div_le_of_rate hC hδ)

/-- The same, with the conclusion in the exact shape of `H.tailVanish`. -/
theorem tailVanish_field {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod)
    (C : ℝ → ℝ → ℝ) (h : TailRate H.τ C) :
    ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ → ∃ M, H.τ ε γ M ≤ δ :=
  tailVanish_of_power h

/-- Non-vacuity: `τ = 1 / M` has rate `C = 1`. -/
theorem invRate : TailRate (fun _ _ M => 1 / M) (fun _ _ => 1) :=
  fun _ _ => ⟨zero_le_one, fun _ _ => le_rfl⟩

theorem invRate_vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ →
    ∃ M : ℝ, (fun _ _ M => 1 / M : ℝ → ℝ → ℝ → ℝ) ε γ M ≤ δ :=
  tailVanish_of_power invRate

/-- The counts `E = 2L`, `Emod = 0` violate the H5b target. -/
theorem not_target_double : ¬ H5bTarget (fun _ _ L => 2 * L) (fun _ _ _ => 0) := by
  intro h
  unfold H5bTarget at h
  obtain ⟨L₀, hL⟩ := h 1 1 one_pos one_pos 1 one_pos
  have h1 : |2 * max L₀ 1 - 0| ≤ 1 * max L₀ 1 := hL _ (le_max_left _ _)
  have h2 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  rw [sub_zero, abs_of_nonneg (by linarith)] at h1
  linarith

/-- **G9 audit.** The rate hypothesis is satisfiable while the target fails, so `TailRate`
(a statement on `τ` alone) is not the H5b target in disguise. -/
theorem tail_rate_not_target :
    TailRate (fun _ _ M => 1 / M) (fun _ _ => 1) ∧
      ¬ H5bTarget (fun _ _ L => 2 * L) (fun _ _ _ => 0) :=
  ⟨invRate, not_target_double⟩

end SteklovAudit.H5TailRate
