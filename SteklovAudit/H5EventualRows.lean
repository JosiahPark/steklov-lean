import Mathlib
import SteklovAudit.H5Reindex
import SteklovAudit.H5SmoothedIdent
import SteklovAudit.H5CountAudit

/-!
# G51: the E-free rows of the smoothed route, required only for `1 ≤ L`

Roadmap item G51. `H5bSmoothedEvInputs` is `H5bSmoothedInputs` (G40) with every E-free row
(`rowMiss`, `colMiss`, `bessel`, `colBessel`, `count`, `defect`, `tail`, `ha`, `hb`, `lowCount`)
guarded by `1 ≤ L →`; the rates and their vanishing conditions are unchanged. `ofSmoothed` shows the
old form implies the new one.

Glued data (used by G52): `evN`, `evNB` are the truncation sizes for `1 ≤ L` and `0` otherwise;
`evD` is `W.D` reindexed along `finCongr` for `1 ≤ L` and G24's empty `zData` otherwise.

* `evN_pos`, `evNB_pos`, `evN_neg`, `evNB_neg`: the size equations used for reindexing;
* `evD_pos`: the `dif_pos` unfolding of `evD`;
* `tau_nonneg`, `c_nonneg`: `0 ≤ τ ε γ M` and `0 ≤ c ε γ M`, from the rows at `L = 1`.

What this file does NOT prove: no row (count, defect, tail, low count, missing mass, Bessel) is
proved for the Steklov operator of the tetrahedron or for any actual coupling; that the paper's
`E`, `Emod` are smoothed counts is not proved; no Dirichlet-to-Neumann operator is constructed;
(7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5EventualRows

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WindowProfile SteklovAudit.H5SmoothedIdent

/-- **G51.** The E-free rows of `H5bSmoothedInputs`, each required only for `1 ≤ L`. -/
structure H5bSmoothedEvInputs where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  m1 : ℝ → ℝ → ℝ → ℝ
  rowMiss : ∀ ε γ L : ℝ, 1 ≤ L → ∑ i, (1 - ∑ j, (D ε γ L).J i j ^ 2) ≤ m1 ε γ L
  m1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m1 ε γ L ≤ η * L
  m2 : ℝ → ℝ → ℝ → ℝ
  colMiss : ∀ ε γ L : ℝ, 1 ≤ L → ∑ j, (1 - ∑ i, (D ε γ L).J i j ^ 2) ≤ m2 ε γ L
  m2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m2 ε γ L ≤ η * L
  colBessel : ∀ ε γ L, 1 ≤ L → ∀ j, ∑ i, (D ε γ L).J i j ^ 2 ≤ 1
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  bessel : ∀ ε γ L, 1 ≤ L → ∀ i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1
  count : ∀ ε γ L : ℝ, 1 ≤ L → (Fintype.card (Fin (nA ε γ L)) : ℝ) ≤ Cm ε γ * (1 + L) ^ 2
  defect : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D ε γ L).K ≤ Ck ε γ ^ 2 * (1 + L) ^ 2
  τ : ℝ → ℝ → ℝ → ℝ
  tail : ∀ ε γ M L : ℝ, 1 ≤ L → hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M
  Cτ : ℝ → ℝ → ℝ
  tailRate : SteklovAudit.H5TailRate.TailRate τ Cτ
  ha : ∀ ε γ L, 1 ≤ L → ∀ i, 0 ≤ (D ε γ L).a i
  hb : ∀ ε γ L, 1 ≤ L → ∀ j, 0 ≤ (D ε γ L).b j
  c : ℝ → ℝ → ℝ → ℝ
  lowCount : ∀ ε γ M L : ℝ, 1 ≤ L →
    ((Finset.univ.filter fun i => (D ε γ L).a i ≤ M).card : ℝ) ≤ c ε γ M

/-- **G51.** The old form implies the new one (forget the guards). -/
noncomputable def ofSmoothed (V : H5bSmoothedInputs) : H5bSmoothedEvInputs where
  nA := V.nA
  nB := V.nB
  D := V.D
  P := V.P
  Φ := V.Φ
  hΦ := V.hΦ
  profBound := V.profBound
  m1 := V.m1
  rowMiss := fun ε γ L _ => V.rowMiss ε γ L
  m1Vanish := V.m1Vanish
  m2 := V.m2
  colMiss := fun ε γ L _ => V.colMiss ε γ L
  m2Vanish := V.m2Vanish
  colBessel := fun ε γ L _ => V.colBessel ε γ L
  Cm := V.Cm
  Ck := V.Ck
  hCm := V.hCm
  bessel := fun ε γ L _ => V.bessel ε γ L
  count := fun ε γ L _ => V.count ε γ L
  defect := fun ε γ L _ => V.defect ε γ L
  τ := V.τ
  tail := fun ε γ M L _ => V.tail ε γ M L
  Cτ := V.Cτ
  tailRate := V.tailRate
  ha := fun ε γ L _ => V.ha ε γ L
  hb := fun ε γ L _ => V.hb ε γ L
  c := V.c
  lowCount := fun ε γ M L _ => V.lowCount ε γ M L

variable (W : H5bSmoothedEvInputs)

/-- **G51.** Glued true truncation size: `nA` for `1 ≤ L`, `0` otherwise. -/
noncomputable def evN (ε γ L : ℝ) : ℕ := if 1 ≤ L then W.nA ε γ L else 0

/-- **G51.** Glued model truncation size: `nB` for `1 ≤ L`, `0` otherwise. -/
noncomputable def evNB (ε γ L : ℝ) : ℕ := if 1 ≤ L then W.nB ε γ L else 0

theorem evN_pos {ε γ L : ℝ} (h : 1 ≤ L) : W.nA ε γ L = evN W ε γ L := by
  unfold evN; rw [if_pos h]

theorem evNB_pos {ε γ L : ℝ} (h : 1 ≤ L) : W.nB ε γ L = evNB W ε γ L := by
  unfold evNB; rw [if_pos h]

theorem evN_neg {ε γ L : ℝ} (h : ¬ 1 ≤ L) : 0 = evN W ε γ L := by
  unfold evN; rw [if_neg h]

theorem evNB_neg {ε γ L : ℝ} (h : ¬ 1 ≤ L) : 0 = evNB W ε γ L := by
  unfold evNB; rw [if_neg h]

/-- **G51.** Glued data: `W.D` for `1 ≤ L`, the empty `zData` otherwise. -/
noncomputable def evD (ε γ L : ℝ) : Data (Fin (evN W ε γ L)) (Fin (evNB W ε γ L)) :=
  if h : 1 ≤ L then
    (W.D ε γ L).reindex (finCongr (evN_pos W h)) (finCongr (evNB_pos W h))
  else
    Data.reindex SteklovAudit.H5CountAudit.zData (finCongr (evN_neg W h)) (finCongr (evNB_neg W h))

/-- **G51.** For `1 ≤ L` the glued data are `W.D` reindexed. -/
theorem evD_pos {ε γ L : ℝ} (h : 1 ≤ L) :
    evD W ε γ L = (W.D ε γ L).reindex (finCongr (evN_pos W h)) (finCongr (evNB_pos W h)) := by
  first
    | (unfold evD; rw [dif_pos h])
    | simp only [evD, dif_pos h]

/-- **G51.** The tail rate is nonnegative (the tail row at `L = 1`). -/
theorem tau_nonneg (ε γ M : ℝ) : 0 ≤ W.τ ε γ M :=
  le_trans (hs2_nonneg _) (W.tail ε γ M 1 le_rfl)

/-- **G51.** The low-count bound is nonnegative (the low-count row at `L = 1`). -/
theorem c_nonneg (ε γ M : ℝ) : 0 ≤ W.c ε γ M :=
  le_trans (Nat.cast_nonneg _) (W.lowCount ε γ M 1 le_rfl)

end SteklovAudit.H5EventualRows
