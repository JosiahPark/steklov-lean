import Mathlib
import SteklovAudit.H5Compare

/-!
# G50: reindexing spectral data along equivalences (bookkeeping for G51)

Roadmap item G50. `Data.reindex D e f` transports spectral data `D : Data ι κ` along index
equivalences `e : ι ≃ ι'`, `f : κ ≃ κ'`. Every quantity used by the E-free rows of
`H5bSmoothedInputs` (G40) is invariant under it:

* `reindex_rowSq`, `reindex_colSq`: row and column square sums of `J` (pointwise, transported);
* `reindex_rowMass`, `reindex_colMass`: the missing-mass sums;
* `reindex_hs2K`: `hs2` of the defect `K`;
* `reindex_tail`: `hs2` of the high-energy part of `K` at every split energy `M`;
* `reindex_lowCount`: the number of eigenvalues `≤ M`;
* `reindex_smoothedA`, `reindex_smoothedB`: smoothed counts `∑ φ (a i - L)`, `∑ φ (b j - L)`.

All proofs are `Equiv.sum_comp`.

What this file does NOT prove: it is bookkeeping for G51/G52 only and moves no row of the F table
by itself. No row (count, defect, tail, low count, missing mass, Bessel) is proved for the Steklov
operator of the tetrahedron or for any actual coupling; no Dirichlet-to-Neumann operator is
constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.AbstractTransfer

/-- **G50.** Spectral data transported along index equivalences `e`, `f`. -/
def Data.reindex {ι κ ι' κ' : Type*} (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') : Data ι' κ' :=
  ⟨D.a ∘ e.symm, D.b ∘ f.symm, fun i j => D.J (e.symm i) (f.symm j)⟩

end SteklovAudit.AbstractTransfer

namespace SteklovAudit.H5Reindex

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

variable {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

theorem reindex_a (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (i : ι') :
    (D.reindex e f).a i = D.a (e.symm i) := rfl

theorem reindex_b (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (j : κ') :
    (D.reindex e f).b j = D.b (f.symm j) := rfl

theorem reindex_J (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (i : ι') (j : κ') :
    (D.reindex e f).J i j = D.J (e.symm i) (f.symm j) := rfl

theorem reindex_K (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (i : ι') (j : κ') :
    (D.reindex e f).K i j = D.K (e.symm i) (f.symm j) := rfl

/-- Double sums are invariant under reindexing both indices. -/
theorem sum_sum_reindex (g : ι → κ → ℝ) (e : ι ≃ ι') (f : κ ≃ κ') :
    ∑ i, ∑ j, g (e.symm i) (f.symm j) = ∑ i, ∑ j, g i j := by
  calc ∑ i, ∑ j, g (e.symm i) (f.symm j) = ∑ i, ∑ j, g (e.symm i) j :=
        Finset.sum_congr rfl (fun i _ => Equiv.sum_comp f.symm (fun j => g (e.symm i) j))
    _ = ∑ i, ∑ j, g i j := Equiv.sum_comp e.symm (fun i => ∑ j, g i j)

/-- `hs2` is invariant under reindexing. -/
theorem hs2_reindex (M : ι → κ → ℝ) (e : ι ≃ ι') (f : κ ≃ κ') :
    hs2 (fun i j => M (e.symm i) (f.symm j)) = hs2 M := by
  unfold hs2
  exact sum_sum_reindex (fun i j => M i j ^ 2) e f

/-- **G50.** Row square sums, transported. -/
theorem reindex_rowSq (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (i : ι') :
    ∑ j, (D.reindex e f).J i j ^ 2 = ∑ j, D.J (e.symm i) j ^ 2 :=
  Equiv.sum_comp f.symm (fun j => D.J (e.symm i) j ^ 2)

/-- **G50.** Column square sums, transported. -/
theorem reindex_colSq (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (j : κ') :
    ∑ i, (D.reindex e f).J i j ^ 2 = ∑ i, D.J i (f.symm j) ^ 2 :=
  Equiv.sum_comp e.symm (fun i => D.J i (f.symm j) ^ 2)

/-- **G50.** The row missing mass is unchanged. -/
theorem reindex_rowMass (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') :
    ∑ i, (1 - ∑ j, (D.reindex e f).J i j ^ 2) = ∑ i, (1 - ∑ j, D.J i j ^ 2) := by
  calc ∑ i, (1 - ∑ j, (D.reindex e f).J i j ^ 2) = ∑ i, (1 - ∑ j, D.J (e.symm i) j ^ 2) :=
        Finset.sum_congr rfl (fun i _ => by rw [reindex_rowSq])
    _ = ∑ i, (1 - ∑ j, D.J i j ^ 2) := Equiv.sum_comp e.symm (fun i => 1 - ∑ j, D.J i j ^ 2)

/-- **G50.** The column missing mass is unchanged. -/
theorem reindex_colMass (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') :
    ∑ j, (1 - ∑ i, (D.reindex e f).J i j ^ 2) = ∑ j, (1 - ∑ i, D.J i j ^ 2) := by
  calc ∑ j, (1 - ∑ i, (D.reindex e f).J i j ^ 2) = ∑ j, (1 - ∑ i, D.J i (f.symm j) ^ 2) :=
        Finset.sum_congr rfl (fun j _ => by rw [reindex_colSq])
    _ = ∑ j, (1 - ∑ i, D.J i j ^ 2) := Equiv.sum_comp f.symm (fun j => 1 - ∑ i, D.J i j ^ 2)

/-- **G50.** `hs2` of the defect is unchanged. -/
theorem reindex_hs2K (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') :
    hs2 (D.reindex e f).K = hs2 D.K :=
  hs2_reindex D.K e f

/-- **G50.** The high-energy part of the defect has the same `hs2` at every split energy. -/
theorem reindex_tail (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (M : ℝ) :
    hs2 (mask (hiE (D.reindex e f) M) (D.reindex e f).K) = hs2 (mask (hiE D M) D.K) := by
  first
    | exact hs2_reindex (mask (hiE D M) D.K) e f
    | (rw [← hs2_reindex (mask (hiE D M) D.K) e f]; rfl)

/-- **G50.** The number of true eigenvalues `≤ M` is unchanged. -/
theorem reindex_lowCount (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (M : ℝ) :
    (Finset.univ.filter fun i => (D.reindex e f).a i ≤ M).card
      = (Finset.univ.filter fun i => D.a i ≤ M).card := by
  first
    | (rw [Finset.card_filter, Finset.card_filter]
       exact Equiv.sum_comp e.symm (fun i => if D.a i ≤ M then 1 else 0))
    | (simp only [Finset.card_filter]
       exact Equiv.sum_comp e.symm (fun i => if D.a i ≤ M then 1 else 0))

/-- **G50.** The smoothed count of the true spectrum is unchanged. -/
theorem reindex_smoothedA (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (φ : ℝ → ℝ) (L : ℝ) :
    ∑ i, φ ((D.reindex e f).a i - L) = ∑ i, φ (D.a i - L) :=
  Equiv.sum_comp e.symm (fun i => φ (D.a i - L))

/-- **G50.** The smoothed count of the model spectrum is unchanged. -/
theorem reindex_smoothedB (D : Data ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (φ : ℝ → ℝ) (L : ℝ) :
    ∑ j, φ ((D.reindex e f).b j - L) = ∑ j, φ (D.b j - L) :=
  Equiv.sum_comp f.symm (fun j => φ (D.b j - L))

end SteklovAudit.H5Reindex
