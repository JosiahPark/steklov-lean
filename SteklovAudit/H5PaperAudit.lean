import Mathlib
import SteklovAudit.H5PaperRows
import SteklovAudit.H5WeakAudit
import SteklovAudit.H5WindowWitness

/-!
# G17: F2-style audit of `H5bPaperInputs` (G16)

Roadmap item G17.

* `paperOfCutoff E Emod disc hcut hvan`: every field of `H5bPaperInputs E Emod` other than
  `cutoff`/`discVanish` is filled by one fixed family that does not depend on `E` or `Emod`
  (zero energies, zero coupling, one eigenvalue on the `A` side for `L ≥ 0`, window profile
  `arctan` from G8). Only a bound `|E − Emod| ≤ disc` and the vanishing of `disc` are taken as input.
* `paperWitness E : H5bPaperInputs E E` and `paperWitness_nonempty`: the structure is not vacuous;
  `paperWitness_nonjunk`: its test is non-constant and its `A` side is nonempty for `L ≥ 0`.
* `paper_rows_not_target`: for `E = 2L`, `Emod = 0` (where `H5bTarget` fails, G9) the same fixed
  rows hold, so no `disc` satisfies both the cutoff bound and `discVanish`: all of the
  "target in disguise" content sits in the cutoff row (G2, G3, G14).
* `paper_iff_target`: `Nonempty (H5bPaperInputs E Emod) ↔ H5bTarget E Emod`.

Remark: the Weyl `count` row `card ≤ Cm (1 + L) ^ 2` holds for all real `L`, so at `L = -1` it
forces an empty `A` side; the witness therefore takes `nA = 0` for `L < 0`. Only `L → ∞` matters.

What this file does NOT prove: no field of `H5bPaperInputs` is proved for the Steklov operator of
the tetrahedron; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and
Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5PaperAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness

/-- Size of the `A` side of the witness: one eigenvalue for `L ≥ 0`, none for `L < 0`. -/
noncomputable def wN (L : ℝ) : ℕ := if 0 ≤ L then 1 else 0

theorem wN_le_one (L : ℝ) : wN L ≤ 1 := by
  unfold wN
  split_ifs <;> omega

/-- Zero energies and zero coupling, on `Fin n × Fin 1`. -/
noncomputable def wData (n : ℕ) : Data (Fin n) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => 0

theorem wData_K (n : ℕ) (i : Fin n) (j : Fin 1) : (wData n).K i j = 0 := by
  first
  | simp [Data.K, wData]
  | (show ((0 : ℝ) - 0) * 0 = 0; ring)

theorem wData_sum (φ : ℝ → ℝ) (n : ℕ) (L : ℝ) :
    ∑ i, ∑ j, (φ ((wData n).a i - L) - φ ((wData n).b j - L)) * (wData n).J i j ^ 2 = 0 := by
  simp [wData]

theorem wData_bessel (n : ℕ) (i : Fin n) : ∑ j, (wData n).J i j ^ 2 ≤ 1 := by
  simp [wData]

theorem wData_count (L : ℝ) : (Fintype.card (Fin (wN L)) : ℝ) ≤ 1 * (1 + L) ^ 2 := by
  simp only [Fintype.card_fin]
  unfold wN
  split_ifs with h
  · push_cast
    nlinarith [sq_nonneg L]
  · push_cast
    nlinarith [sq_nonneg (1 + L)]

theorem wData_defect (n : ℕ) (L : ℝ) : hs2 (wData n).K ≤ (0 : ℝ) ^ 2 * (1 + L) ^ 2 := by
  rw [weak_hs2_zero _ (wData_K n)]
  simp

theorem wData_tail (n : ℕ) (M : ℝ) : hs2 (mask (hiE (wData n) M) (wData n).K) ≤ 0 := by
  apply le_of_eq
  apply weak_hs2_zero
  intro i j
  dsimp only [mask]
  split_ifs <;> first | exact wData_K n i j | rfl

theorem wData_lowCount (L M : ℝ) :
    ((Finset.univ.filter fun i => (wData (wN L)).a i ≤ M).card : ℝ) ≤ 1 := by
  have h1 : (Finset.univ.filter fun i => (wData (wN L)).a i ≤ M).card ≤ wN L := by
    calc (Finset.univ.filter fun i => (wData (wN L)).a i ≤ M).card
        ≤ (Finset.univ : Finset (Fin (wN L))).card := Finset.card_filter_le _ _
      _ = wN L := by simp
  exact_mod_cast le_trans h1 (wN_le_one L)

theorem w_cutoff (E Emod disc : ℝ → ℝ → ℝ → ℝ)
    (hcut : ∀ ε γ L : ℝ, |E ε γ L - Emod ε γ L| ≤ disc ε γ L) (ε γ L : ℝ) :
    |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j, (arctanProfile.φ ((wData (wN L)).a i - L)
      - arctanProfile.φ ((wData (wN L)).b j - L)) * (wData (wN L)).J i j ^ 2| ≤ disc ε γ L := by
  rw [wData_sum, sub_zero]
  exact hcut ε γ L

/-- **G17.** All rows except `cutoff`/`discVanish` are filled by one family independent of
`E`, `Emod`; only `|E − Emod| ≤ disc` and the vanishing of `disc` are inputs. -/
noncomputable def paperOfCutoff (E Emod disc : ℝ → ℝ → ℝ → ℝ)
    (hcut : ∀ ε γ L : ℝ, |E ε γ L - Emod ε γ L| ≤ disc ε γ L)
    (hvan : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      disc ε γ L ≤ η * L) : H5bPaperInputs E Emod where
  nA := fun _ _ L => wN L
  nB := fun _ _ _ => 1
  D := fun _ _ L => wData (wN L)
  P := arctanProfile
  disc := disc
  cutoff := w_cutoff E Emod disc hcut
  discVanish := hvan
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  bessel := fun _ _ L i => wData_bessel (wN L) i
  count := fun _ _ L => wData_count L
  defect := fun _ _ L => wData_defect (wN L) L
  τ := fun _ _ _ => 0
  tail := fun _ _ M L => wData_tail (wN L) M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 1
  lowCount := fun _ _ M L => wData_lowCount L M

/-- **G17.** An explicit witness of the paper-form inputs, for any `E = Emod`. -/
noncomputable def paperWitness (E : ℝ → ℝ → ℝ → ℝ) : H5bPaperInputs E E :=
  paperOfCutoff E E (fun _ _ _ => 0) (fun ε γ L => by simp)
    (fun _ _ _ _ η hη => ⟨0, fun L hL => show (0 : ℝ) ≤ η * L from mul_nonneg hη.le hL⟩)

theorem paperWitness_nonempty (E : ℝ → ℝ → ℝ → ℝ) : Nonempty (H5bPaperInputs E E) :=
  ⟨paperWitness E⟩

/-- **G17.** The witness is not junk: its test is non-constant and its `A` side has one
eigenvalue for every `L ≥ 0`. -/
theorem paperWitness_nonjunk (E : ℝ → ℝ → ℝ → ℝ) :
    (paperWitness E).P.φ 1 - (paperWitness E).P.φ 0 ≠ 0 ∧
      ∀ ε γ L : ℝ, 0 ≤ L → (paperWitness E).nA ε γ L = 1 := by
  refine ⟨arctan_profile_nonjunk, fun ε γ L hL => ?_⟩
  show wN L = 1
  unfold wN
  rw [if_pos hL]

/-- **G17 audit.** With every non-cutoff row held fixed (they hold for this family whatever `E`,
`Emod` are), the target fails for `E = 2L`, `Emod = 0`, so no `disc` meets both the cutoff bound
and `discVanish`: the whole "target in disguise" content is in the cutoff row. -/
theorem paper_rows_not_target :
    ¬ ∃ disc : ℝ → ℝ → ℝ → ℝ, (∀ ε γ L : ℝ, |2 * L - 0| ≤ disc ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        disc ε γ L ≤ η * L) := by
  rintro ⟨disc, hc, hv⟩
  exact SteklovAudit.H5TailRate.not_target_double
    (h5b_of_paper (paperOfCutoff (fun _ _ L => 2 * L) (fun _ _ _ => 0) disc hc hv))

/-- **G17 audit.** As for F1 and G14: the paper-form inputs hold exactly when the target holds. -/
theorem paper_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (H5bPaperInputs E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨W⟩ => h5b_of_paper W, fun h => ⟨paperOfCutoff E Emod
    (fun ε γ L => |E ε γ L - Emod ε γ L|) (fun _ _ _ => le_refl _)
    (fun ε γ hε hγ η hη => h ε γ hε hγ η hη)⟩⟩

end SteklovAudit.H5PaperAudit
