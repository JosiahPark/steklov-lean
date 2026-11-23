import Mathlib
import SteklovAudit.H5Compare

/-!
# `H5bTarget` is per-`γ`, not uniform in `γ` (roadmap item G150)

`H5Compare.H5bTarget E Emod` asks, for each fixed `ε, γ > 0`, that `E − Emod = o(L)`; the threshold
`L₀` may depend on `γ`. This file gives an explicit scalar model showing that this per-`γ` statement
is strictly weaker than a `γ`-uniform one, and that it says nothing about the `γ → 0` limit:

* `qE ε γ L := min (max L 0) (1 / γ)`, with `Emod := 0`.
* `model_target`: `H5bTarget qE 0` holds (take `L₀ = 1 / (γ η)`).
* `model_not_uniform`: no single `L₀` works for all `γ > 0` (already for `η = 1/2`).
* `model_small_gamma_eq`: for `L > 0` and `γ L ≤ 1`, `qE ε γ L = L`; so the `γ → 0` limit at fixed `L`
  is `max L 0`.
* `model_limit_not_littleO`: that limit, `max L 0`, is not `o(L)`.

So the paper's order "first `L → ∞`, then `γ → 0`" is forced, and passing to `γ → 0` needs a
separate `γ`-uniform cutoff bound (the `C γ L` hypothesis of `ModelEdgeLawGammaFamily`, G148).
(The roadmap's draft third theorem, "no `C` with `|qE 1 γ L| ≤ C γ L` eventually", is false for this
model, since `qE 1 γ L = 1 / γ` for large `L`; it is replaced by the two limit theorems above.)

What this file does NOT prove: anything about the actual edge counts `E`, `Emod` of the paper, the
cutoff bound itself, (7.29), H5, or Theorem 1.3 / 11.1. It is a scalar example only.
-/

namespace SteklovAudit.H5bQuantifierOrder

open SteklovAudit.H5Compare

/-- The model count: `o(L)` for each fixed `γ > 0`, but equal to `L` on `0 < L ≤ 1 / γ`. -/
noncomputable def qE (_ε γ L : ℝ) : ℝ := min (max L 0) (1 / γ)

/-- **G150.** The model satisfies `H5bTarget` against `Emod = 0`. -/
theorem model_target : H5bTarget qE (fun _ _ _ => 0) := by
  intro ε γ _hε hγ η hη
  refine ⟨1 / (γ * η), fun L hL => ?_⟩
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hη0 : η ≠ 0 := hη.ne'
  have hE0 : 0 ≤ qE ε γ L := le_min (le_max_right L 0) (le_of_lt (one_div_pos.2 hγ))
  have hE1 : qE ε γ L ≤ 1 / γ := min_le_right _ _
  have hk : η * (1 / (γ * η)) = 1 / γ := by
    first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [mul_one_div, mul_comm γ η, div_mul_eq_div_div, div_self hη0])
  have hmono : η * (1 / (γ * η)) ≤ η * L := mul_le_mul_of_nonneg_left hL hη.le
  show |qE ε γ L - 0| ≤ η * L
  rw [sub_zero, abs_of_nonneg hE0]
  linarith

/-- **G150.** `H5bTarget` for the model is not uniform in `γ`: no `L₀` serves every `γ > 0`. -/
theorem model_not_uniform :
    ¬ ∃ L₀ : ℝ, ∀ γ : ℝ, 0 < γ → ∀ L, L₀ ≤ L → |qE 1 γ L| ≤ L / 2 := by
  rintro ⟨L₀, h⟩
  have hLpos : (0 : ℝ) < max L₀ 1 + 1 := by
    have := le_max_right L₀ 1
    linarith
  have hγ : (0 : ℝ) < 1 / (max L₀ 1 + 1) := div_pos one_pos hLpos
  have hle : L₀ ≤ max L₀ 1 + 1 := by
    have := le_max_left L₀ 1
    linarith
  have hv := h _ hγ _ hle
  have hq : qE 1 (1 / (max L₀ 1 + 1)) (max L₀ 1 + 1) = max L₀ 1 + 1 := by
    unfold qE
    rw [one_div_one_div, max_eq_left hLpos.le, min_self]
  rw [hq, abs_of_pos hLpos] at hv
  linarith

/-- **G150.** For `L > 0` and `γ ≤ 1 / L` the model equals `L`: small cutoffs see the full count. -/
theorem model_small_gamma_eq (ε γ L : ℝ) (hL : 0 < L) (hγ : 0 < γ) (hγL : γ ≤ 1 / L) :
    qE ε γ L = L := by
  have hLg : L ≤ 1 / γ := by
    first
      | exact (le_one_div hL hγ).2 hγL
      | exact (le_div_iff₀ hγ).2 (by have := (le_div_iff₀ hL).1 hγL; linarith)
      | exact (le_div_iff hγ).2 (by have := (le_div_iff hL).1 hγL; linarith)
  unfold qE
  rw [max_eq_left hL.le]
  exact min_eq_left hLg

/-- **G150.** The `γ → 0` limit of the model, `max L 0`, is not `o(L)`. -/
theorem model_limit_not_littleO :
    ¬ ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |max L 0| ≤ η * L := by
  intro h
  obtain ⟨L₀, hL₀⟩ := h (1 / 2) (by norm_num)
  have hpos : (0 : ℝ) < max L₀ 1 := lt_of_lt_of_le one_pos (le_max_right L₀ 1)
  have hv := hL₀ (max L₀ 1) (le_max_left L₀ 1)
  rw [max_eq_left hpos.le, abs_of_pos hpos] at hv
  linarith

end SteklovAudit.H5bQuantifierOrder
