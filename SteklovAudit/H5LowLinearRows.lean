import Mathlib
import SteklovAudit.H5LowLinear
import SteklovAudit.H5LowCount
import SteklovAudit.H5LowMass

/-!
# G64: the G62 low rows from a linearly growing low-energy count

Roadmap item G64. For cutoff data `D` with the Bessel row bound `∑ j, J i j ^ 2 ≤ 1`, nonnegative
energies, and at most `c` eigenvalues `a i ≤ M`:

* `lowMass_le_count`: the low-energy mass of `J` is at most `c` (G15's `low_mask_le_rows`,
  `rows_le_card`);
* `lowDefect_le_count`: the low-energy defect of `K` is at most `M ^ 2 * c` (G10's
  `lowDefect_of_lowMass`);
* `lowRows_of_linearCount`: the family version, giving the `lowMass` and `lowDefect` fields of
  `H5bLowLInputs` (G62) with `mLo = C ε γ M * (1 + |L|)` and `κ2 = M ^ 2 * mLo`;
* `lowVanish_of_linear`: the scalar step behind the `lowVanish` field: if `lam L → 0` with
  `lam ≥ 0`, then `lam L · √((M ^ 2 · C (1 + |L|)) · C (1 + |L|)) ≤ η L` eventually.

F table text: the low-energy row needs only a low count `≤ c(M) · (1 + |L|)` together with
`lam → 0`, not an L-uniform count.

What this file does NOT prove: it proves neither the Bessel bound, nor the linear low-energy count,
nor `lam → 0` for the Steklov operator of the tetrahedron; it constructs no Dirichlet-to-Neumann
operator, and (7.29) and Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5LowLinearRows

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G64.** Bessel rows plus at most `c` eigenvalues `≤ M` bound the low-energy mass by `c`. -/
theorem lowMass_le_count (D : Data ι κ) (M c : ℝ) (hrow : ∀ i, ∑ j, D.J i j ^ 2 ≤ 1)
    (hcount : ((Finset.univ.filter fun i => D.a i ≤ M).card : ℝ) ≤ c) :
    hs2 (mask (fun i j => ¬ hiE D M i j) D.J) ≤ c :=
  le_trans (SteklovAudit.H5LowCount.low_mask_le_rows D M)
    (le_trans (SteklovAudit.H5LowCount.rows_le_card D M hrow) hcount)

/-- **G64.** With nonnegative energies the same count bounds the low-energy defect by
`M ^ 2 * c`. -/
theorem lowDefect_le_count (D : Data ι κ) (ha : ∀ i, 0 ≤ D.a i) (hb : ∀ j, 0 ≤ D.b j)
    (M c : ℝ) (hrow : ∀ i, ∑ j, D.J i j ^ 2 ≤ 1)
    (hcount : ((Finset.univ.filter fun i => D.a i ≤ M).card : ℝ) ≤ c) :
    hs2 (mask (fun i j => ¬ hiE D M i j) D.K) ≤ M ^ 2 * c :=
  SteklovAudit.H5LowMass.lowDefect_of_lowMass D ha hb M c (lowMass_le_count D M c hrow hcount)

/-- **G64.** Family version: a low count `≤ C ε γ M * (1 + |L|)` gives the `lowMass` and
`lowDefect` rows of `H5bLowLInputs` with `mLo = C ε γ M * (1 + |L|)`, `κ2 = M ^ 2 * mLo`. -/
theorem lowRows_of_linearCount {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (ha : ∀ ε γ L i, 0 ≤ (D ε γ L).a i) (hb : ∀ ε γ L j, 0 ≤ (D ε γ L).b j)
    (C : ℝ → ℝ → ℝ → ℝ)
    (hrow : ∀ ε γ L i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1)
    (hcount : ∀ ε γ M L : ℝ,
      ((Finset.univ.filter fun i => (D ε γ L).a i ≤ M).card : ℝ) ≤ C ε γ M * (1 + |L|)) :
    (∀ ε γ M L : ℝ, hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).J)
        ≤ C ε γ M * (1 + |L|)) ∧
    (∀ ε γ M L : ℝ, hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).K)
        ≤ M ^ 2 * (C ε γ M * (1 + |L|))) :=
  ⟨fun ε γ M L => lowMass_le_count (D ε γ L) M _ (hrow ε γ L) (hcount ε γ M L),
   fun ε γ M L => lowDefect_le_count (D ε γ L) (ha ε γ L) (hb ε γ L) M _ (hrow ε γ L)
     (hcount ε γ M L)⟩

/-- The square root in `lowVanish` for the linear rows. -/
theorem sqrt_linear_rows (M C L : ℝ) (hc : 0 ≤ C) :
    Real.sqrt ((M ^ 2 * (C * (1 + |L|))) * (C * (1 + |L|))) = |M| * C * (1 + |L|) := by
  have hM : M ^ 2 = |M| ^ 2 := (sq_abs M).symm
  have hsq : (M ^ 2 * (C * (1 + |L|))) * (C * (1 + |L|)) = (|M| * C * (1 + |L|)) ^ 2 := by
    rw [hM]
    ring
  have hnn : 0 ≤ |M| * C * (1 + |L|) :=
    mul_nonneg (mul_nonneg (abs_nonneg M) hc) (by positivity)
  rw [hsq]
  exact Real.sqrt_sq hnn

/-- **G64.** Scalar step: with `lam ≥ 0` and `lam L → 0`, the low term of the linear rows is
`o(L)`. -/
theorem lowVanish_of_linear (M C : ℝ) (lam : ℝ → ℝ) (hc : 0 ≤ C) (hlam : ∀ L, 0 ≤ lam L)
    (hv : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → lam L ≤ η) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      lam L * Real.sqrt ((M ^ 2 * (C * (1 + |L|))) * (C * (1 + |L|))) ≤ η * L := by
  intro η hη
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = |M| * C := ⟨_, rfl⟩
  have hs : 0 ≤ s := by
    rw [hs_def]
    exact mul_nonneg (abs_nonneg M) hc
  have hB : 0 < 2 * (s + 1) := by linarith
  obtain ⟨L₁, hL₁⟩ := hv (η / (2 * (s + 1))) (div_pos hη hB)
  refine ⟨max L₁ 1, fun L hL => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLone : 1 ≤ L := le_trans (le_max_right _ _) hL
  have habs : |L| = L := abs_of_nonneg (by linarith)
  have hlL : lam L ≤ η / (2 * (s + 1)) := hL₁ L hL1
  rw [sqrt_linear_rows M C L hc, habs]
  have h1 : s * (1 + L) ≤ 2 * (s + 1) * L := by
    nlinarith [mul_nonneg hs (by linarith : (0 : ℝ) ≤ L - 1)]
  have h2 : lam L * (|M| * C * (1 + L)) ≤ lam L * (2 * (s + 1) * L) := by
    have h1' : |M| * C * (1 + L) ≤ 2 * (s + 1) * L := by
      rw [← hs_def]
      exact h1
    exact mul_le_mul_of_nonneg_left h1' (hlam L)
  have hpos : 0 ≤ 2 * (s + 1) * L := mul_nonneg (le_of_lt hB) (by linarith)
  have h3 : lam L * (2 * (s + 1) * L) ≤ η / (2 * (s + 1)) * (2 * (s + 1) * L) :=
    mul_le_mul_of_nonneg_right hlL hpos
  have hne : (2 * (s + 1)) ≠ 0 := ne_of_gt hB
  have h4 : η / (2 * (s + 1)) * (2 * (s + 1) * L) = η * L := by
    first
    | (rw [div_mul_eq_mul_div, div_eq_iff hne]; ring)
    | (field_simp; ring)
    | field_simp
  linarith [h2, h3, h4]

end SteklovAudit.H5LowLinearRows
