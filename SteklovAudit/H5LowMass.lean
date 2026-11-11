import Mathlib
import SteklovAudit.H5Compare

/-!
# G10: the low-energy defect row κ from a low-energy mass bound on `J`

Roadmap item G10. On low pairs (`¬ hiE D M i j`, i.e. `max (a i) (b j) ≤ M`) with nonnegative
energies (true for Steklov eigenvalues) one has `|a i - b j| ≤ M`, hence `K i j ^ 2 ≤ M ^ 2 * J i j ^ 2`.

* `abs_sub_le_of_low`: `0 ≤ x`, `0 ≤ y`, `max x y ≤ M` ⇒ `|x - y| ≤ M`.
* `low_K_sq_le`, `low_mask_K_sq_le`, `hs2_low_K_le`: the entrywise and summed bounds.
* `lowDefect_of_lowMass`: a low-energy mass bound `m` on `J` gives the low-energy defect bound
  `M ^ 2 * m`.
* `lowDefect_field`: the same in the exact shape of `H5bInputs.lowDefect`, with
  `κ2 ε γ M := M ^ 2 * m ε γ M`.

This replaces the row "low-energy defect bound κ" by "the identification `J` has L-uniform mass on
energies ≤ M" (a statement on `J`, not on `K`) plus nonnegativity of the energies.

What this file does NOT prove: it does not prove the low-energy mass bound (or any row of the
F table) for the Steklov operator of the tetrahedron, constructs no Dirichlet-to-Neumann
operator, and leaves (7.29) and Theorem 1.3 / 11.1 conditional on the named inputs.
-/

namespace SteklovAudit.H5LowMass

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G10.** Two nonnegative numbers below `M` differ by at most `M`. -/
theorem abs_sub_le_of_low {x y M : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : max x y ≤ M) :
    |x - y| ≤ M := by
  have h1 : x ≤ M := le_trans (le_max_left x y) h
  have h2 : y ≤ M := le_trans (le_max_right x y) h
  rw [abs_le]
  constructor <;> linarith

/-- **G10.** On a low pair the squared defect entry is at most `M ^ 2` times the squared
coupling. -/
theorem low_K_sq_le (D : Data ι κ) (ha : ∀ i, 0 ≤ D.a i) (hb : ∀ j, 0 ≤ D.b j) (M : ℝ)
    (i : ι) (j : κ) (h : ¬ hiE D M i j) : D.K i j ^ 2 ≤ M ^ 2 * D.J i j ^ 2 := by
  have h' : ¬ M < max (D.a i) (D.b j) := h
  have hmax : max (D.a i) (D.b j) ≤ M := not_lt.mp h'
  have hd : |D.a i - D.b j| ≤ M := abs_sub_le_of_low (ha i) (hb j) hmax
  have hab := abs_le.mp hd
  have hsq : (D.a i - D.b j) ^ 2 ≤ M ^ 2 := by
    first
    | exact sq_le_sq' hab.1 hab.2
    | nlinarith [hab.1, hab.2]
  unfold Data.K
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- **G10.** The masked (low-energy) version of `low_K_sq_le`, valid for every pair. -/
theorem low_mask_K_sq_le (D : Data ι κ) (ha : ∀ i, 0 ≤ D.a i) (hb : ∀ j, 0 ≤ D.b j) (M : ℝ)
    (i : ι) (j : κ) :
    mask (fun i j => ¬ hiE D M i j) D.K i j ^ 2
      ≤ M ^ 2 * mask (fun i j => ¬ hiE D M i j) D.J i j ^ 2 := by
  dsimp only [mask]
  by_cases h : hiE D M i j
  · rw [if_neg (not_not.mpr h), if_neg (not_not.mpr h)]
    simp
  · rw [if_pos h, if_pos h]
    exact low_K_sq_le D ha hb M i j h

/-- **G10.** Summed: the low-energy HS defect is at most `M ^ 2` times the low-energy mass. -/
theorem hs2_low_K_le (D : Data ι κ) (ha : ∀ i, 0 ≤ D.a i) (hb : ∀ j, 0 ≤ D.b j) (M : ℝ) :
    hs2 (mask (fun i j => ¬ hiE D M i j) D.K)
      ≤ M ^ 2 * hs2 (mask (fun i j => ¬ hiE D M i j) D.J) := by
  unfold hs2
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => low_mask_K_sq_le D ha hb M i j)

/-- **G10.** A low-energy mass bound on `J` gives the low-energy defect bound. -/
theorem lowDefect_of_lowMass (D : Data ι κ) (ha : ∀ i, 0 ≤ D.a i) (hb : ∀ j, 0 ≤ D.b j)
    (M m : ℝ) (hm : hs2 (mask (fun i j => ¬ hiE D M i j) D.J) ≤ m) :
    hs2 (mask (fun i j => ¬ hiE D M i j) D.K) ≤ M ^ 2 * m :=
  le_trans (hs2_low_K_le D ha hb M) (mul_le_mul_of_nonneg_left hm (sq_nonneg M))

/-- **G10.** The `lowDefect` field of `H5bInputs`, with `κ2 ε γ M := M ^ 2 * m ε γ M`, from
nonnegative energies and an L-uniform low-energy mass bound `m` on `J`. -/
theorem lowDefect_field {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (ha : ∀ ε γ L i, 0 ≤ (D ε γ L).a i) (hb : ∀ ε γ L j, 0 ≤ (D ε γ L).b j)
    (m : ℝ → ℝ → ℝ → ℝ)
    (hm : ∀ ε γ M L : ℝ,
      hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).J) ≤ m ε γ M) :
    ∀ ε γ M L : ℝ,
      hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).K) ≤ M ^ 2 * m ε γ M := by
  intro ε γ M L
  exact lowDefect_of_lowMass (D ε γ L) (ha ε γ L) (hb ε γ L) M (m ε γ M) (hm ε γ M L)

end SteklovAudit.H5LowMass
