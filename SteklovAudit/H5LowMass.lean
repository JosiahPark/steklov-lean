import Mathlib
import SteklovAudit.H5Compare
import SteklovAudit.H5TailRate

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

G11 (same file): `LowMass` (a `Prop` on `D`, `m` only), `lowDefect_of_LowMass`, the toy family
`lowCounter` (zero energies, `J = 1 + L`) with `lowMass_not_of_pde` and `lowMass_row_fails` (the
low-mass row does not follow from `PDEInputs`), and `lowMass_satisfiable`, `lowMass_not_target`
(the row is satisfiable while the H5b target fails, so it is not the target in disguise).

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

/-! ## G11: the low-mass input is a genuine input and not the target in disguise -/

/-- **G11.** The low-mass input as a `Prop` on the data family `D` and the bound `m` only;
it mentions neither `E` nor `Emod`. -/
def LowMass {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))) (m : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ ε γ M L : ℝ, hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).J) ≤ m ε γ M

/-- **G11.** `LowMass` plus nonnegative energies gives the `lowDefect` field (G10). -/
theorem lowDefect_of_LowMass {nA nB : ℝ → ℝ → ℝ → ℕ}
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (ha : ∀ ε γ L i, 0 ≤ (D ε γ L).a i) (hb : ∀ ε γ L j, 0 ≤ (D ε γ L).b j)
    (m : ℝ → ℝ → ℝ → ℝ) (h : LowMass D m) :
    ∀ ε γ M L : ℝ,
      hs2 (mask (fun i j => ¬ hiE (D ε γ L) M i j) (D ε γ L).K) ≤ M ^ 2 * m ε γ M :=
  lowDefect_field D ha hb m h

/-- On `Fin 1 × Fin 1` the HS norm is the square of the single entry. -/
theorem hs2_one (M : Fin 1 → Fin 1 → ℝ) : hs2 M = M 0 0 ^ 2 := by
  first
  | simp only [hs2, Fin.sum_univ_one]
  | simp [hs2]

/-- **G11.** Toy family: zero energies, coupling `1 + L`. -/
noncomputable def lowCounter (L : ℝ) : Data (Fin 1) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => 1 + L

/-- The toy family has nonnegative energies (the G10 side condition holds). -/
theorem lowCounter_nonneg (L : ℝ) :
    (∀ i, 0 ≤ (lowCounter L).a i) ∧ (∀ j, 0 ≤ (lowCounter L).b j) := by
  constructor
  · intro _
    show (0 : ℝ) ≤ 0
    exact le_refl 0
  · intro _
    show (0 : ℝ) ≤ 0
    exact le_refl 0

/-- The toy family satisfies `PDEInputs` with `Cm = 1`, `Ck = 0`, for every `L`. -/
theorem lowCounter_pde (L : ℝ) : PDEInputs (lowCounter L) L 1 0 := by
  constructor
  · rw [hs2_one]
    show (1 + L) ^ 2 ≤ 1 * (1 + L) ^ 2
    apply le_of_eq
    ring
  · rw [hs2_one]
    show ((0 - 0) * (1 + L)) ^ 2 ≤ 0 ^ 2 * (1 + L) ^ 2
    apply le_of_eq
    ring

/-- Below the split energy `1` the masked mass of the toy family is `(1 + L)²`. -/
theorem lowCounter_low_mass (L : ℝ) :
    hs2 (mask (fun i j => ¬ hiE (lowCounter L) 1 i j) (lowCounter L).J) = (1 + L) ^ 2 := by
  rw [hs2_one]
  have hl : ¬ hiE (lowCounter L) 1 0 0 := by
    show ¬ ((1 : ℝ) < max 0 0)
    rw [max_self]
    norm_num
  dsimp only [mask]
  rw [if_pos hl]
  all_goals rfl

/-- **G11.** `PDEInputs` for every `L` (even with zero defect and nonnegative energies) does not
give an L-uniform low-energy mass bound: the low-mass row does not follow from
`PDEInputs.mass`. -/
theorem lowMass_not_of_pde :
    (∀ L : ℝ, PDEInputs (lowCounter L) L 1 0) ∧
    ¬ (∃ m : ℝ, ∀ L : ℝ,
        hs2 (mask (fun i j => ¬ hiE (lowCounter L) 1 i j) (lowCounter L).J) ≤ m) := by
  refine ⟨lowCounter_pde, fun h => ?_⟩
  obtain ⟨m, hm⟩ := h
  have b := hm |m|
  rw [lowCounter_low_mass] at b
  nlinarith [le_abs_self m, abs_nonneg m, sq_nonneg |m|]

/-- **G11.** For the toy family no `m` bounds the low-energy mass uniformly in `L`. -/
theorem lowMass_row_fails (m : ℝ → ℝ) :
    ¬ (∀ M L : ℝ,
        hs2 (mask (fun i j => ¬ hiE (lowCounter L) M i j) (lowCounter L).J) ≤ m M) := by
  intro h
  exact lowMass_not_of_pde.2 ⟨m 1, fun L => h 1 L⟩

/-- A vanishing coupling has zero low-energy mass. -/
theorem lowMass_of_J_zero (D : Data ι κ) (hJ : ∀ i j, D.J i j = 0) (M : ℝ) :
    hs2 (mask (fun i j => ¬ hiE D M i j) D.J) ≤ 0 := by
  apply le_of_eq
  unfold hs2
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  dsimp only [mask]
  split_ifs <;> simp [hJ i j]

/-- The zero witness: zero energies and zero coupling. -/
noncomputable def zeroData : Data (Fin 1) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => 0

/-- **G11.** `LowMass` is satisfiable (zero coupling, `m = 0`). -/
theorem lowMass_satisfiable :
    LowMass (nA := fun _ _ _ => 1) (nB := fun _ _ _ => 1)
      (fun _ _ _ => zeroData) (fun _ _ _ => 0) := by
  unfold LowMass
  intro ε γ M L
  exact lowMass_of_J_zero zeroData (fun _ _ => rfl) M

/-- **G11 audit.** `LowMass` holds for a family while the H5b target fails for `E = 2L`,
`Emod = 0`: the low-mass input (a statement on `D`, `m` alone) is not the target in disguise. -/
theorem lowMass_not_target :
    LowMass (nA := fun _ _ _ => 1) (nB := fun _ _ _ => 1)
        (fun _ _ _ => zeroData) (fun _ _ _ => 0) ∧
      ¬ H5bTarget (fun _ _ L => 2 * L) (fun _ _ _ => 0) :=
  ⟨lowMass_satisfiable, SteklovAudit.H5TailRate.not_target_double⟩

end SteklovAudit.H5LowMass
