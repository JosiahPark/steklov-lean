import Mathlib
import SteklovAudit.H5WeakRows

/-!
# G14: F2-style audit of `H5bWeakInputs` (G13)

Roadmap item G14.

* `weakWitness E`: an explicit `H5bWeakInputs E E` (one eigenvalue on each side, zero energies,
  zero coupling, zero test), so the weak structure is not vacuous; `weakWitness_nonempty`.
* `weak_rows_not_target`: the two replacement rows, `TailRate` (G9) and `LowMass` (G10/G11), are
  satisfiable while `H5bTarget` fails for `E = 2L`, `Emod = 0`, so neither replacement row is the
  target in disguise.
* `weakOfTarget`, `weak_iff_target`: as for F1 (`inputs_iff_target`), the empty cutoff turns
  `cutoff` + `discVanish` into the target itself, so `Nonempty (H5bWeakInputs E Emod)` is
  equivalent to `H5bTarget E Emod`. All "target in disguise" content stays in the cutoff row.

What this file does NOT prove: no field of `H5bWeakInputs` is proved for the Steklov operator of
the tetrahedron; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and
Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5WeakAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5LowMass SteklovAudit.H5TailRate

/-- An array with all entries zero has zero HS norm. -/
theorem weak_hs2_zero {ι κ : Type*} [Fintype ι] [Fintype κ] (M : ι → κ → ℝ)
    (h : ∀ i j, M i j = 0) : hs2 M = 0 := by
  unfold hs2
  simp [h]

theorem zeroData_J (i j : Fin 1) : zeroData.J i j = 0 := rfl

theorem zeroData_K (i j : Fin 1) : zeroData.K i j = 0 := by
  first
  | (show (zeroData.a i - zeroData.b j) * zeroData.J i j = 0; rw [zeroData_J, mul_zero])
  | simp [Data.K, zeroData]

theorem zeroData_pde (L : ℝ) : PDEInputs zeroData L 0 0 := by
  constructor
  · rw [weak_hs2_zero _ zeroData_J]
    simp
  · rw [weak_hs2_zero _ zeroData_K]
    simp

theorem zeroData_tail (M : ℝ) : hs2 (mask (hiE zeroData M) zeroData.K) ≤ 0 := by
  apply le_of_eq
  apply weak_hs2_zero
  intro i j
  dsimp only [mask]
  split_ifs <;> first | exact zeroData_K i j | rfl

/-- **G14.** Zero tail with zero rate. -/
theorem zeroRate : TailRate (fun _ _ _ => 0) (fun _ _ => 0) := by
  unfold TailRate
  intro ε γ
  refine ⟨le_refl _, fun M _ => ?_⟩
  show (0 : ℝ) ≤ 0 / M
  rw [zero_div]

/-- **G14.** An explicit witness of the weak inputs, for any `E = Emod`. -/
noncomputable def weakWitness (E : ℝ → ℝ → ℝ → ℝ) : H5bWeakInputs E E where
  nA := fun _ _ _ => 1
  nB := fun _ _ _ => 1
  D := fun _ _ _ => zeroData
  F := fun _ _ _ _ => 0
  disc := fun _ _ _ => 0
  cutoff := by intro ε γ L; simp
  discVanish := by
    intro ε γ _ _ η hη
    refine ⟨0, fun L hL => ?_⟩
    show (0 : ℝ) ≤ η * L
    exact mul_nonneg hη.le hL
  Cm := fun _ _ => 0
  Ck := fun _ _ => 0
  hCm := fun _ _ => le_refl 0
  pde := fun _ _ L => zeroData_pde L
  τ := fun _ _ _ => 0
  tail := fun _ _ M _ => zeroData_tail M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  m := fun _ _ _ => 0
  lowMass := lowMass_satisfiable
  Λ0 := fun _ _ => 0
  hΛ0 := fun _ _ => le_refl 0
  lam := fun _ _ _ _ => 0
  hlam := fun _ _ _ _ => le_refl 0
  lipHi := by intro ε γ M L i j _; simp
  lipLo := by intro ε γ M L i j _; simp
  lamVanish := fun _ _ _ _ _ _ hη => ⟨0, fun _ _ => hη.le⟩

/-- **G14.** The weak inputs are satisfiable. -/
theorem weakWitness_nonempty (E : ℝ → ℝ → ℝ → ℝ) : Nonempty (H5bWeakInputs E E) :=
  ⟨weakWitness E⟩

/-- **G14 audit.** Both replacement rows (`TailRate`, `LowMass`) hold for explicit data while
`H5bTarget` fails for `E = 2L`, `Emod = 0`: neither is the target in disguise. -/
theorem weak_rows_not_target :
    TailRate (fun _ _ M => 1 / M) (fun _ _ => 1) ∧
      LowMass (nA := fun _ _ _ => 1) (nB := fun _ _ _ => 1)
        (fun _ _ _ => zeroData) (fun _ _ _ => 0) ∧
      ¬ H5bTarget (fun _ _ L => 2 * L) (fun _ _ _ => 0) :=
  ⟨invRate, lowMass_satisfiable, not_target_double⟩

/-- From the target alone: empty cutoff, `disc = |E − Emod|`, all other inputs zero. -/
noncomputable def weakOfTarget {E Emod : ℝ → ℝ → ℝ → ℝ} (h : H5bTarget E Emod) :
    H5bWeakInputs E Emod where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => emptyData
  F := fun _ _ _ _ => 0
  disc := fun ε γ L => |E ε γ L - Emod ε γ L|
  cutoff := by intro ε γ L; simp
  discVanish := fun ε γ hε hγ η hη => h ε γ hε hγ η hη
  Cm := fun _ _ => 0
  Ck := fun _ _ => 0
  hCm := fun _ _ => le_refl 0
  pde := fun _ _ _ => ⟨by simp [hs2], by simp [hs2]⟩
  τ := fun _ _ _ => 0
  tail := by intro ε γ M L; simp [hs2]
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ i => Fin.elim0 i
  hb := fun _ _ _ j => Fin.elim0 j
  m := fun _ _ _ => 0
  lowMass := by
    unfold LowMass
    intro ε γ M L
    simp [hs2]
  Λ0 := fun _ _ => 0
  hΛ0 := fun _ _ => le_refl 0
  lam := fun _ _ _ _ => 0
  hlam := fun _ _ _ _ => le_refl 0
  lipHi := fun _ _ _ _ i => Fin.elim0 i
  lipLo := fun _ _ _ _ i => Fin.elim0 i
  lamVanish := fun _ _ _ _ _ _ hη => ⟨0, fun _ _ => hη.le⟩

/-- **G14 audit.** As for F1, the weak inputs hold exactly when the target holds: the cutoff row
with empty data carries the whole target, and no other field mentions `E` or `Emod`. -/
theorem weak_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bWeakInputs E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨W⟩ => h5b_of_weak W, fun h => ⟨weakOfTarget h⟩⟩

end SteklovAudit.H5WeakAudit
