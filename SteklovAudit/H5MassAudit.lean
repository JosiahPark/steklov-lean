import Mathlib
import SteklovAudit.H5CountAudit
import SteklovAudit.H5MissingMass

/-!
# G27: audit of the missing-mass H5b inputs `H5bMassInputs` (G26)

Roadmap item G27.

* `massWitness : H5bMassInputs 0 0`, `massWitness_nonempty`: the structure is not vacuous (G24's
  empty family `zData`, profile `arctan`, `Φ = 2`, `m1 = m2 = 0`).
* `mass_stronger_than_defect`: `⌈L⌉₊` true eigenvalues all at `L`, `J = 0`, `φ = arctan`. The G23
  row-completeness row holds with `k1 = 0` (`arctan 0 = 0`), while the missing row mass is `⌈L⌉₊`, so no
  vanishing `m1` meets the G26 row `rowMiss`. The missing-mass row is a stronger, profile-free
  sufficient form of the completeness row, not a weaker one.

What this file does NOT prove: no count, missing-mass, completeness or Bessel row is proved for the
Steklov operator of the tetrahedron (or for any concrete operator); the empty family and the
`⌈L⌉₊` example are consistency checks, not models of the spectrum; no Dirichlet-to-Neumann operator is
constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5MassAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows SteklovAudit.H5CountAudit SteklovAudit.H5MissingMass

theorem z_rowMiss : ∑ i : Fin 0, (1 - ∑ j : Fin 0, zData.J i j ^ 2) ≤ 0 := by
  first | exact (Fin.sum_univ_zero _).le | simp

theorem z_colMiss : ∑ j : Fin 0, (1 - ∑ i : Fin 0, zData.J i j ^ 2) ≤ 0 := by
  first | exact (Fin.sum_univ_zero _).le | simp

/-- **G27.** An explicit witness of the missing-mass inputs with `E = Emod = 0`. -/
noncomputable def massWitness : H5bMassInputs (fun _ _ _ => 0) (fun _ _ _ => 0) where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => zData
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  e1 := fun _ _ _ => 0
  trueCount := z_trueCount (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound
  e1Vanish := zeroDisc_vanish
  m1 := fun _ _ _ => 0
  rowMiss := fun _ _ _ => z_rowMiss
  m1Vanish := zeroDisc_vanish
  e2 := fun _ _ _ => 0
  modelCount := z_modelCount (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound
  e2Vanish := zeroDisc_vanish
  m2 := fun _ _ _ => 0
  colMiss := fun _ _ _ => z_colMiss
  m2Vanish := zeroDisc_vanish
  colBessel := fun _ _ _ j => z_colBessel j
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  bessel := fun _ _ _ i => z_bessel i
  count := fun _ _ L => z_count L
  defect := fun _ _ L => z_defect L
  τ := fun _ _ _ => 0
  tail := fun _ _ M _ => z_tail M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 1
  lowCount := fun _ _ M _ => z_lowCount M

theorem massWitness_nonempty :
    Nonempty (H5bMassInputs (fun _ _ _ => 0) (fun _ _ _ => 0)) :=
  ⟨massWitness⟩

/-- G27 example, completeness row: eigenvalues at `L`, `J = 0`; the profile vanishes there, so the
G23 row-completeness sum is `0`. -/
theorem atL_rowDefect (L : ℝ) :
    ∑ i : Fin ⌈L⌉₊, |arctanProfile.φ ((fun _ : Fin ⌈L⌉₊ => L) i - L)| *
      (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) ≤ 0 := by
  apply le_of_eq
  refine Finset.sum_eq_zero fun i _ => ?_
  show |Real.arctan (L - L)| * _ = 0
  rw [sub_self, Real.arctan_zero, abs_zero, zero_mul]

/-- G27 example: with `J = 0` every row misses its full mass, so the missing row mass is `⌈L⌉₊`. -/
theorem atL_rowMass (L : ℝ) :
    ∑ i : Fin ⌈L⌉₊,
      (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) = (⌈L⌉₊ : ℝ) := by
  have h : ∀ i : Fin ⌈L⌉₊,
      (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) = 1 := by
    intro i
    first | (simp; done) | norm_num
  rw [Finset.sum_congr rfl (fun i _ => h i), SteklovAudit.H5CountAudit.const_sum_fin, mul_one]

/-- G27 example: no vanishing `m1` meets the missing-mass row. -/
theorem atL_rowMiss_fails :
    ¬ ∃ m1 : ℝ → ℝ → ℝ → ℝ,
      (∀ ε γ L : ℝ, ∑ i : Fin ⌈L⌉₊,
        (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) ≤ m1 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        m1 ε γ L ≤ η * L) := by
  rintro ⟨m1, hs, hv⟩
  obtain ⟨L₀, hL₀⟩ := hv 1 1 one_pos one_pos (1 / 2) (by norm_num)
  have hL1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  have h1 := hL₀ (max L₀ 1) (le_max_left _ _)
  have h2 : (⌈max L₀ 1⌉₊ : ℝ) ≤ m1 1 1 (max L₀ 1) :=
    (atL_rowMass (max L₀ 1)).symm.le.trans (hs 1 1 (max L₀ 1))
  have hc : max L₀ 1 ≤ (⌈max L₀ 1⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-- **G27.** The missing-mass row is stronger than the completeness row it replaces: in the example
(`⌈L⌉₊` true eigenvalues at `L`, `J = 0`, `φ = arctan`) the G23 row-completeness row holds with
`k1 = 0`, the missing row mass is `⌈L⌉₊`, and no vanishing `m1` meets `rowMiss`. -/
theorem mass_stronger_than_defect :
    (∀ L : ℝ, ∑ i : Fin ⌈L⌉₊, |arctanProfile.φ ((fun _ : Fin ⌈L⌉₊ => L) i - L)| *
      (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) ≤ 0) ∧
    (∀ L : ℝ, ∑ i : Fin ⌈L⌉₊,
      (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) = (⌈L⌉₊ : ℝ)) ∧
    ¬ ∃ m1 : ℝ → ℝ → ℝ → ℝ,
      (∀ ε γ L : ℝ, ∑ i : Fin ⌈L⌉₊,
        (1 - ∑ j : Fin 1, (fun (_ : Fin ⌈L⌉₊) (_ : Fin 1) => (0 : ℝ)) i j ^ 2) ≤ m1 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        m1 ε γ L ≤ η * L) :=
  ⟨atL_rowDefect, atL_rowMass, atL_rowMiss_fails⟩

end SteklovAudit.H5MassAudit
