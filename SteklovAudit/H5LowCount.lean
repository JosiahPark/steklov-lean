import Mathlib
import SteklovAudit.H5LowMass
import SteklovAudit.H5LipRows

/-!
# G15: the low-mass row from a Bessel bound plus an L-uniform low-energy count

Roadmap item G15. A low pair (`¬ hiE D M i j`) has `a i ≤ M` (G5's `le_of_not_hiE`), so the
low-energy mass of `J` is at most the sum of the squared row norms over the eigenvalues `a i ≤ M`.
With rows of norm at most `1` (Bessel) this is at most the number of eigenvalues `≤ M`.

* `low_mask_sq_le_row`, `low_mask_le_rows`: the masked mass is bounded by the low rows of `J`.
* `rows_le_card`, `low_mass_le_count`: with the Bessel bound, by the low-energy count.
* `RowBessel`, `LowCount`: the two inputs as `Prop`s on the data family (and `c`) only; neither
  mentions `E` or `Emod`.
* `lowMass_of_bessel_lowCount`: `RowBessel D` and `LowCount D c` give G11's `LowMass D c`.
* `lowDefect_of_bessel_lowCount`: hence the `lowDefect` field with `κ2 ε γ M := M ^ 2 * c ε γ M`.
* `bessel_lowCount_satisfiable`: both inputs hold for G11's `zeroData` with `c = 1`.

This replaces the row "low-energy defect bound κ" by "eigenvalues `≤ M` are L-uniformly finitely
many" plus the same Bessel bound as G12.

What this file does NOT prove: it does not prove the Bessel bound or the L-uniform low-energy count
(or any row of the F table) for the Steklov operator of the tetrahedron, constructs no
Dirichlet-to-Neumann operator, and leaves (7.29) and Theorem 1.3 / 11.1 conditional on the named
inputs.
-/

namespace SteklovAudit.H5LowCount

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5LowMass

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G15.** Entrywise: a masked low-energy entry is controlled by its row's energy `a i ≤ M`. -/
theorem low_mask_sq_le_row (D : Data ι κ) (M : ℝ) (i : ι) (j : κ) :
    mask (fun i j => ¬ hiE D M i j) D.J i j ^ 2 ≤ (if D.a i ≤ M then D.J i j ^ 2 else 0) := by
  dsimp only [mask]
  by_cases h : hiE D M i j
  · rw [if_neg (not_not.mpr h)]
    split_ifs <;> nlinarith [sq_nonneg (D.J i j)]
  · rw [if_pos h]
    obtain ⟨ha, _⟩ := SteklovAudit.H5LipRows.le_of_not_hiE D M i j h
    rw [if_pos ha]

/-- **G15.** The low-energy mass is at most the squared norms of the rows with `a i ≤ M`. -/
theorem low_mask_le_rows (D : Data ι κ) (M : ℝ) :
    hs2 (mask (fun i j => ¬ hiE D M i j) D.J)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => D.a i ≤ M), ∑ j, D.J i j ^ 2 := by
  rw [Finset.sum_filter]
  unfold hs2
  apply Finset.sum_le_sum
  intro i _
  by_cases ha : D.a i ≤ M
  · rw [if_pos ha]
    apply Finset.sum_le_sum
    intro j _
    have h1 := low_mask_sq_le_row D M i j
    rw [if_pos ha] at h1
    exact h1
  · rw [if_neg ha]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro j _
    have h1 := low_mask_sq_le_row D M i j
    rw [if_neg ha] at h1
    exact le_antisymm h1 (sq_nonneg _)

/-- **G15.** With rows of norm at most `1`, the low rows contribute at most the low count. -/
theorem rows_le_card (D : Data ι κ) (M : ℝ) (hB : ∀ i, ∑ j, D.J i j ^ 2 ≤ 1) :
    ∑ i ∈ Finset.univ.filter (fun i => D.a i ≤ M), ∑ j, D.J i j ^ 2
      ≤ ((Finset.univ.filter fun i => D.a i ≤ M).card : ℝ) := by
  calc ∑ i ∈ Finset.univ.filter (fun i => D.a i ≤ M), ∑ j, D.J i j ^ 2
      ≤ ∑ _i ∈ Finset.univ.filter (fun i => D.a i ≤ M), (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => hB i)
    _ = ((Finset.univ.filter fun i => D.a i ≤ M).card : ℝ) := by
        first
        | rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        | simp

/-- **G15.** Bessel bound plus a low-energy count bound `c` give the low-energy mass bound. -/
theorem low_mass_le_count (D : Data ι κ) (M c : ℝ) (hB : ∀ i, ∑ j, D.J i j ^ 2 ≤ 1)
    (hc : ((Finset.univ.filter fun i => D.a i ≤ M).card : ℝ) ≤ c) :
    hs2 (mask (fun i j => ¬ hiE D M i j) D.J) ≤ c :=
  le_trans (low_mask_le_rows D M) (le_trans (rows_le_card D M hB) hc)

/-- **G15.** Bessel input: every row of `J` has squared norm at most `1`, for every cutoff. -/
def RowBessel {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) : Prop :=
  ∀ (ε γ L : ℝ) (i : Fin (nA ε γ L)), ∑ j, (D ε γ L).J i j ^ 2 ≤ 1

/-- **G15.** L-uniform low-energy count: at most `c ε γ M` eigenvalues `a i ≤ M`, for every `L`. -/
def LowCount {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) (c : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ ε γ M L : ℝ,
    (((Finset.univ : Finset (Fin (nA ε γ L))).filter fun i => (D ε γ L).a i ≤ M).card : ℝ)
      ≤ c ε γ M

/-- **G15.** `RowBessel` and `LowCount` give G11's `LowMass` with the same bound `c`. -/
theorem lowMass_of_bessel_lowCount {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) (c : ℝ → ℝ → ℝ → ℝ)
    (hB : RowBessel D) (hc : LowCount D c) : LowMass D c := by
  unfold LowMass
  intro ε γ M L
  exact low_mass_le_count (D ε γ L) M (c ε γ M) (hB ε γ L) (hc ε γ M L)

/-- **G15.** Hence the `lowDefect` field of `H5bInputs` with `κ2 ε γ M := M ^ 2 * c ε γ M`. -/
theorem lowDefect_of_bessel_lowCount {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (ha : ∀ ε γ L i, 0 ≤ (D ε γ L).a i) (hb : ∀ ε γ L j, 0 ≤ (D ε γ L).b j)
    (c : ℝ → ℝ → ℝ → ℝ) (hB : RowBessel D) (hc : LowCount D c) :
    ∀ ε γ M L : ℝ,
      hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).K) ≤ M ^ 2 * c ε γ M :=
  lowDefect_of_LowMass D ha hb c (lowMass_of_bessel_lowCount D c hB hc)

/-- **G15 non-vacuity.** Both inputs hold for G11's `zeroData` with `c = 1`. -/
theorem bessel_lowCount_satisfiable :
    RowBessel (nA := fun _ _ _ => 1) (nB := fun _ _ _ => 1) (fun _ _ _ => zeroData) ∧
      LowCount (nA := fun _ _ _ => 1) (nB := fun _ _ _ => 1)
        (fun _ _ _ => zeroData) (fun _ _ _ => 1) := by
  constructor
  · unfold RowBessel
    intro ε γ L i
    first
    | simp [zeroData]
    | (show ∑ _j : Fin 1, (0 : ℝ) ^ 2 ≤ 1; simp)
  · unfold LowCount
    intro ε γ M L
    have h : ((Finset.univ : Finset (Fin 1)).filter fun i => zeroData.a i ≤ M).card ≤ 1 :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    have h' : (((Finset.univ : Finset (Fin 1)).filter fun i => zeroData.a i ≤ M).card : ℝ) ≤ 1 := by
      exact_mod_cast h
    exact h'

end SteklovAudit.H5LowCount
