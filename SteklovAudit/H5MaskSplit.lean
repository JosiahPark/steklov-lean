import Mathlib
import SteklovAudit.H5Compare

/-!
# G85: splitting a masked Hilbert–Schmidt norm into high and low parts

Roadmap item G85. Two inequalities that merging the high- and low-energy parts of the (7.29)
assembly needs:

* `hs2_mask_add_compl`: `hs2 (mask p M) + hs2 (mask (¬ p) M) = hs2 M`;
* `sqrt_mul_add_sqrt_mul_le`: `√(a₁ b₁) + √(a₂ b₂) ≤ √((a₁ + a₂)(b₁ + b₂))` for nonnegative reals;
* `split_le_unsplit`: hence the split defect/overlap products are bounded by the unsplit one.

What this file does NOT prove: these are finite-dimensional facts about coefficient arrays. Nothing
is proved about the Steklov operator of the tetrahedron; no DtN operator is constructed; no row of
the F table is proved for the operator; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5MaskSplit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- **G85.** A mask and its complement split the squared Hilbert–Schmidt norm. -/
theorem hs2_mask_add_compl {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → κ → Prop)
    [∀ i j, Decidable (p i j)] (M : ι → κ → ℝ) :
    hs2 (mask p M) + hs2 (mask (fun i j => ¬ p i j) M) = hs2 M := by
  dsimp only [hs2, mask]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : p i j <;> simp [h]

/-- **G85.** Cauchy–Schwarz for two terms under square roots. -/
theorem sqrt_mul_add_sqrt_mul_le {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    Real.sqrt (a₁ * b₁) + Real.sqrt (a₂ * b₂) ≤ Real.sqrt ((a₁ + a₂) * (b₁ + b₂)) := by
  have hs : 0 ≤ Real.sqrt (a₁ * b₁) + Real.sqrt (a₂ * b₂) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq hs]
  apply Real.sqrt_le_sqrt
  have e1 : Real.sqrt (a₁ * b₁) ^ 2 = a₁ * b₁ := Real.sq_sqrt (mul_nonneg ha₁ hb₁)
  have e2 : Real.sqrt (a₂ * b₂) ^ 2 = a₂ * b₂ := Real.sq_sqrt (mul_nonneg ha₂ hb₂)
  have e3 : Real.sqrt (a₁ * b₂) ^ 2 = a₁ * b₂ := Real.sq_sqrt (mul_nonneg ha₁ hb₂)
  have e4 : Real.sqrt (a₂ * b₁) ^ 2 = a₂ * b₁ := Real.sq_sqrt (mul_nonneg ha₂ hb₁)
  have e5 : Real.sqrt (a₁ * b₁) * Real.sqrt (a₂ * b₂)
      = Real.sqrt (a₁ * b₂) * Real.sqrt (a₂ * b₁) := by
    rw [← Real.sqrt_mul (mul_nonneg ha₁ hb₁), ← Real.sqrt_mul (mul_nonneg ha₁ hb₂)]
    congr 1
    ring
  nlinarith [sq_nonneg (Real.sqrt (a₁ * b₂) - Real.sqrt (a₂ * b₁))]

/-- **G85.** The split defect/overlap products are bounded by the unsplit product. -/
theorem split_le_unsplit {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → κ → Prop)
    [∀ i j, Decidable (p i j)] (K J : ι → κ → ℝ) :
    Real.sqrt (hs2 (mask p K) * hs2 (mask p J))
      + Real.sqrt (hs2 (mask (fun i j => ¬ p i j) K) * hs2 (mask (fun i j => ¬ p i j) J))
      ≤ Real.sqrt (hs2 K * hs2 J) := by
  have h := sqrt_mul_add_sqrt_mul_le (hs2_nonneg (mask p K))
    (hs2_nonneg (mask (fun i j => ¬ p i j) K)) (hs2_nonneg (mask p J))
    (hs2_nonneg (mask (fun i j => ¬ p i j) J))
  rw [hs2_mask_add_compl p K, hs2_mask_add_compl p J] at h
  exact h

end SteklovAudit.H5MaskSplit
