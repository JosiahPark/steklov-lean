import Mathlib
import SteklovAudit.H5Compare

/-!
# G5: the Lipschitz rows of `H5bInputs` from derivative bounds

Roadmap item G5. The F-table row "Lipschitz-type bounds Λ, λ for the smoothed counting function"
is the pair of fields `lipHi`, `lipLo` of `H5Compare.H5bInputs`. This file shows that both follow
from derivative bounds on the test function `F`:

* `abs_sub_le_of_deriv_bound`, `abs_sub_le_of_deriv_bound_Iic`: mean value inequality on `ℝ` and
  on `Set.Iic M` (via `Convex.norm_image_sub_le_of_norm_deriv_le`);
* `lipHi_of_deriv_bound`: `‖F'‖ ≤ Λ0` everywhere gives the `lipHi` inequality for all pairs;
* `lipLo_of_deriv_bound_le`: `‖F'‖ ≤ lam` on `Set.Iic M` gives the `lipLo` inequality for the
  low-energy pairs (`¬ hiE`, i.e. both energies `≤ M`);
* `lipHi_field`, `lipLo_field`, `hΛ0_of_deriv_bound`: the same in the exact field types.

So the row can be stated as: the smoothed counting test `F ε γ L` is differentiable, `|F'| ≤ Λ0`,
and `sup_{x ≤ M} |F'(x)| → 0` as `L → ∞` for fixed `M` (that is `lamVanish`).

What this file does NOT prove: no derivative bound for the actual smoothed counting function of the
paper, no `lamVanish`, no other field of `H5bInputs`, nothing about the Steklov operator; (7.29)
and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5LipRows

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- Mean value inequality on `ℝ`. -/
theorem abs_sub_le_of_deriv_bound {F : ℝ → ℝ} {Λ0 : ℝ} (hd : Differentiable ℝ F)
    (hb : ∀ x, ‖deriv F x‖ ≤ Λ0) (x y : ℝ) : |F x - F y| ≤ Λ0 * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (s := Set.univ)
    (fun z _ => hd z) (fun z _ => hb z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simp only [Real.norm_eq_abs] at h
  exact h

/-- Mean value inequality on `Set.Iic M`. -/
theorem abs_sub_le_of_deriv_bound_Iic {F : ℝ → ℝ} {lam M : ℝ}
    (hd : ∀ x ∈ Set.Iic M, DifferentiableAt ℝ F x) (hb : ∀ x ∈ Set.Iic M, ‖deriv F x‖ ≤ lam)
    {x y : ℝ} (hx : x ≤ M) (hy : y ≤ M) : |F x - F y| ≤ lam * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (s := Set.Iic M)
    hd hb (convex_Iic M) (show y ∈ Set.Iic M from hy) (show x ∈ Set.Iic M from hx)
  simp only [Real.norm_eq_abs] at h
  exact h

/-- A global derivative bound gives the `lipHi` inequality (for every pair, high or not). -/
theorem lipHi_of_deriv_bound {ι κ : Type*} (D : Data ι κ) (F : ℝ → ℝ) (M Λ0 : ℝ)
    (hd : Differentiable ℝ F) (hb : ∀ x, ‖deriv F x‖ ≤ Λ0) :
    ∀ (i : ι) (j : κ), hiE D M i j → |F (D.a i) - F (D.b j)| ≤ Λ0 * |D.a i - D.b j| :=
  fun i j _ => abs_sub_le_of_deriv_bound hd hb (D.a i) (D.b j)

/-- Low-energy pairs have both energies `≤ M`. -/
theorem le_of_not_hiE {ι κ : Type*} (D : Data ι κ) (M : ℝ) (i : ι) (j : κ)
    (h : ¬ hiE D M i j) : D.a i ≤ M ∧ D.b j ≤ M := by
  unfold hiE at h
  exact max_le_iff.1 (not_lt.1 h)

/-- A derivative bound on `Set.Iic M` gives the `lipLo` inequality for low-energy pairs. -/
theorem lipLo_of_deriv_bound_le {ι κ : Type*} (D : Data ι κ) (F : ℝ → ℝ) (M lam : ℝ)
    (hd : ∀ x ∈ Set.Iic M, DifferentiableAt ℝ F x) (hb : ∀ x ∈ Set.Iic M, ‖deriv F x‖ ≤ lam) :
    ∀ (i : ι) (j : κ), ¬ hiE D M i j → |F (D.a i) - F (D.b j)| ≤ lam * |D.a i - D.b j| := by
  intro i j h
  obtain ⟨ha, hb'⟩ := le_of_not_hiE D M i j h
  exact abs_sub_le_of_deriv_bound_Iic hd hb ha hb'

/-- The derivative bound forces `0 ≤ Λ0` (the field `hΛ0`). -/
theorem hΛ0_of_deriv_bound {F : ℝ → ℝ} {Λ0 : ℝ} (hb : ∀ x, ‖deriv F x‖ ≤ Λ0) : 0 ≤ Λ0 :=
  le_trans (norm_nonneg _) (hb 0)

/-- The field `lipHi` of `H5bInputs`, from derivative bounds. -/
theorem lipHi_field {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) (F : ℝ → ℝ → ℝ → ℝ → ℝ)
    (Λ0 : ℝ → ℝ → ℝ) (hd : ∀ ε γ L, Differentiable ℝ (F ε γ L))
    (hb : ∀ ε γ L x, ‖deriv (F ε γ L) x‖ ≤ Λ0 ε γ) :
    ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), hiE (D ε γ L) M i j →
      |F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)|
        ≤ Λ0 ε γ * |(D ε γ L).a i - (D ε γ L).b j| :=
  fun ε γ M L => lipHi_of_deriv_bound (D ε γ L) (F ε γ L) M (Λ0 ε γ) (hd ε γ L) (hb ε γ L)

/-- The field `lipLo` of `H5bInputs`, from derivative bounds on `Set.Iic M`. -/
theorem lipLo_field {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) (F : ℝ → ℝ → ℝ → ℝ → ℝ)
    (lam : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hd : ∀ ε γ M L, ∀ x ∈ Set.Iic M, DifferentiableAt ℝ (F ε γ L) x)
    (hb : ∀ ε γ M L, ∀ x ∈ Set.Iic M, ‖deriv (F ε γ L) x‖ ≤ lam ε γ M L) :
    ∀ (ε γ M L : ℝ) (i : Fin (nA ε γ L)) (j : Fin (nB ε γ L)), ¬ hiE (D ε γ L) M i j →
      |F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)|
        ≤ lam ε γ M L * |(D ε γ L).a i - (D ε γ L).b j| :=
  fun ε γ M L => lipLo_of_deriv_bound_le (D ε γ L) (F ε γ L) M (lam ε γ M L)
    (hd ε γ M L) (hb ε γ M L)

end SteklovAudit.H5LipRows
