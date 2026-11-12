import Mathlib
import SteklovAudit.H5LowMass
import SteklovAudit.H5MassRow

/-!
# G15: the low-mass row from a Bessel bound plus an L-uniform low-energy count

Roadmap item G15. A low pair (`¬ hiE D M i j`, i.e. `max (a i) (b j) ≤ M`) has `a i ≤ M`, so the
low-energy mass of `J` is at most the sum of the squared row norms over the rows with `a i ≤ M`.
With the Bessel bound of G12 (`∀ i, ∑ j, J i j ^ 2 ≤ 1`) this is at most the number of eigenvalues
`a i ≤ M`.

* `not_hiE_le`, `mask_sq_le_row`, `low_mask_le_rows`: the reduction to rows with `a i ≤ M`.
* `rows_le_card`: Bessel bound ⇒ those rows sum to at most their number.
* `lowMass_of_bessel_lowCount`: Bessel bound plus an L-uniform count `c ε γ M` of eigenvalues
  `≤ M` gives `LowMass D c` (G11).
* `lowDefect_of_bessel_lowCount`: the same feeds the `lowDefect` row (G10) with `κ2 = M ^ 2 * c`.
* `lowCount_nonjunk`: both hypotheses hold for the identity coupling on `Fin 2`, whose mass is `2`,
  so they are not met only by `J = 0`.

This replaces the row "low-energy defect bound κ" by "eigenvalues `≤ M` are L-uniformly finitely
many" plus the same Bessel bound as G12. Both hypotheses mention neither `E` nor `Emod`.

What this file does NOT prove: it proves neither the Bessel bound nor the L-uniform low-energy count
for the Steklov operator of the tetrahedron, constructs no Dirichlet-to-Neumann operator, and leaves
(7.29) and Theorem 1.3 / 11.1 conditional on the named inputs.
-/

namespace SteklovAudit.H5LowCount

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G15.** A low pair has `a i ≤ M`. -/
theorem not_hiE_le (D : Data ι κ) (M : ℝ) (i : ι) (j : κ) (h : ¬ hiE D M i j) : D.a i ≤ M := by
  have h' : ¬ M < max (D.a i) (D.b j) := h
  exact le_trans (le_max_left _ _) (not_lt.mp h')

/-- **G15.** Entrywise: a masked (low) entry is dominated by the entry on rows with `a i ≤ M`
and vanishes on the other rows. -/
theorem mask_sq_le_row (D : Data ι κ) (M : ℝ) (i : ι) (j : κ) :
    mask (fun i j => ¬ hiE D M i j) D.J i j ^ 2 ≤ (if D.a i ≤ M then D.J i j ^ 2 else 0) := by
  dsimp only [mask]
  by_cases h : hiE D M i j
  · rw [if_neg (not_not.mpr h)]
    split_ifs <;> nlinarith [sq_nonneg (D.J i j)]
  · rw [if_pos h, if_pos (not_hiE_le D M i j h)]

/-- **G15.** The low-energy mass is at most the squared row norms summed over rows `a i ≤ M`. -/
theorem low_mask_le_rows (D : Data ι κ) (M : ℝ) :
    hs2 (mask (fun i j => ¬ hiE D M i j) D.J)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => D.a i ≤ M), ∑ j, D.J i j ^ 2 := by
  rw [Finset.sum_filter]
  unfold hs2
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases h : D.a i ≤ M
  · rw [if_pos h]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hj := mask_sq_le_row D M i j
    rw [if_pos h] at hj
    exact hj
  · rw [if_neg h]
    have hz : ∀ j ∈ (Finset.univ : Finset κ),
        mask (fun i j => ¬ hiE D M i j) D.J i j ^ 2 ≤ (0 : ℝ) := by
      intro j _
      have hj := mask_sq_le_row D M i j
      rw [if_neg h] at hj
      exact hj
    calc ∑ j, mask (fun i j => ¬ hiE D M i j) D.J i j ^ 2
        ≤ ∑ _j : κ, (0 : ℝ) := Finset.sum_le_sum hz
      _ = 0 := by simp

/-- **G15.** Under the Bessel bound the rows with `a i ≤ M` sum to at most their number. -/
theorem rows_le_card (D : Data ι κ) (M : ℝ) (hrow : ∀ i, ∑ j, D.J i j ^ 2 ≤ 1) :
    ∑ i ∈ Finset.univ.filter (fun i => D.a i ≤ M), ∑ j, D.J i j ^ 2
      ≤ ((Finset.univ.filter fun i => D.a i ≤ M).card : ℝ) := by
  calc ∑ i ∈ Finset.univ.filter (fun i => D.a i ≤ M), ∑ j, D.J i j ^ 2
      ≤ ∑ _i ∈ Finset.univ.filter (fun i => D.a i ≤ M), (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => hrow i)
    _ = ((Finset.univ.filter fun i => D.a i ≤ M).card : ℝ) := by
        first
        | rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        | simp
        | exact (Finset.cast_card _).symm

/-- **G15.** Bessel bound plus an L-uniform count of eigenvalues `≤ M` gives `LowMass` (G11). -/
theorem lowMass_of_bessel_lowCount {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) (c : ℝ → ℝ → ℝ → ℝ)
    (hrow : ∀ ε γ L i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1)
    (hcount : ∀ ε γ M L : ℝ,
      ((Finset.univ.filter fun i => (D ε γ L).a i ≤ M).card : ℝ) ≤ c ε γ M) :
    SteklovAudit.H5LowMass.LowMass D c := by
  unfold SteklovAudit.H5LowMass.LowMass
  intro ε γ M L
  exact le_trans (low_mask_le_rows (D ε γ L) M)
    (le_trans (rows_le_card (D ε γ L) M (hrow ε γ L)) (hcount ε γ M L))

/-- **G15.** The same with nonnegative energies gives the `lowDefect` row with `κ2 = M ^ 2 * c`. -/
theorem lowDefect_of_bessel_lowCount {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (ha : ∀ ε γ L i, 0 ≤ (D ε γ L).a i) (hb : ∀ ε γ L j, 0 ≤ (D ε γ L).b j)
    (c : ℝ → ℝ → ℝ → ℝ)
    (hrow : ∀ ε γ L i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1)
    (hcount : ∀ ε γ M L : ℝ,
      ((Finset.univ.filter fun i => (D ε γ L).a i ≤ M).card : ℝ) ≤ c ε γ M) :
    ∀ ε γ M L : ℝ,
      hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).K) ≤ M ^ 2 * c ε γ M :=
  SteklovAudit.H5LowMass.lowDefect_of_LowMass D ha hb c
    (lowMass_of_bessel_lowCount D c hrow hcount)

/-- The witness: zero energies, identity coupling on `Fin 2`. -/
noncomputable def idData : Data (Fin 2) (Fin 2) where
  a := fun _ => 0
  b := fun _ => 0
  J := SteklovAudit.H5MassRow.idJ

/-- Any subset of `Fin 2` has at most two elements. -/
theorem card_filter_le_two (p : Fin 2 → Prop) [DecidablePred p] :
    ((Finset.univ.filter p).card : ℝ) ≤ 2 := by
  have h1 : (Finset.univ.filter p).card ≤ (Finset.univ : Finset (Fin 2)).card :=
    Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Fin 2)).card = 2 := by
    first
    | simp
    | rw [Finset.card_univ, Fintype.card_fin]
  rw [h2] at h1
  exact_mod_cast h1

/-- **G15.** Non-vacuity: the Bessel bound and the low count (`c = 2`) hold for the identity
coupling, so `LowMass` follows, while the total mass is `2` (not the trivial `J = 0`). -/
theorem lowCount_nonjunk :
    SteklovAudit.H5LowMass.LowMass (nA := fun _ _ _ => 2) (nB := fun _ _ _ => 2)
        (fun _ _ _ => idData) (fun _ _ _ => 2) ∧ hs2 idData.J = 2 := by
  refine ⟨?_, SteklovAudit.H5MassRow.idJ_hs2⟩
  apply lowMass_of_bessel_lowCount (nA := fun _ _ _ => 2) (nB := fun _ _ _ => 2)
  · intro ε γ L i
    exact le_of_eq (SteklovAudit.H5MassRow.idJ_row i)
  · intro ε γ M L
    exact card_filter_le_two _

end SteklovAudit.H5LowCount
