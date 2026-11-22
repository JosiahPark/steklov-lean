import SteklovAudit.ReviewCandidates
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Six additions to the seven proofs in ReviewCandidates.lean at upstream 1130bc7.
These derive moment certificates from an operator, control fixed HS tails, and
bound centered traces with a second-order remainder. The actual DtN operator,
its eigenbasis, boundary integration, Taylor remainder from regularity, and
the localized PDE estimates remain separate obligations.
-/

namespace SteklovAudit.ReviewExtensions

open SteklovAudit.ReviewCandidates
open Filter
open scoped Topology

section Parseval
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The spectral mass and squared defect follow from vectors in the domain of a symmetric
operator and their geometric norms. No spectral sum is assumed. The construction of the
actual DtN operator, its eigenbasis and the geometric norm identities remains separate. -/
theorem spectral_sums_of_operator {κ : Type*} [Fintype κ]
    (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (hA : ∀ u v : D, inner ℝ (A u) (v : H) = inner ℝ (u : H) (A v))
    (b : HilbertBasis ι ℝ H) (hb : ∀ i, b i ∈ D)
    (lam : ι → ℝ) (he : ∀ i, A ⟨b i, hb i⟩ = lam i • b i)
    (u : κ → D) (mu : κ → ℝ) (M E : ℝ)
    (hmass : ∑ j, ‖(u j : H)‖ ^ 2 = M)
    (henergy : ∑ j, ‖A (u j) - mu j • (u j : H)‖ ^ 2 = E) :
    HasSum (fun p : ι × κ => (inner ℝ (b p.1) (u p.2 : H)) ^ 2) M ∧
      HasSum (fun p : ι × κ =>
        (lam p.1 - mu p.2) ^ 2 * (inner ℝ (b p.1) (u p.2 : H)) ^ 2) E := by
  constructor
  · simpa only [hmass] using finite_probe_hasSum b (fun j => (u j : H))
  · have hr : ∀ i j, inner ℝ (b i) (A (u j) - mu j • (u j : H)) =
        (lam i - mu j) * inner ℝ (b i) (u j : H) := by
      intro i j
      exact residual_coordinate D A hA ⟨b i, hb i⟩ (u j) (lam i) (mu j) (he i)
    simpa only [hr, mul_pow, henergy] using
      finite_probe_hasSum b (fun j => A (u j) - mu j • (u j : H))


end Parseval

section Tail

variable {ι : Type*}

theorem summable_energy_tail (c energy : ι → ℝ) (hc : Summable c) :
    Tendsto (fun R : ℝ => ∑' i, if R < energy i then c i else 0) atTop (𝓝 0) := by
  classical
  have hlim : ∀ i, Tendsto (fun R : ℝ => if R < energy i then c i else 0) atTop (𝓝 0) := by
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (energy i)] with R hR
    simp [not_lt.mpr hR]
  have hbound : ∀ᶠ R : ℝ in atTop,
      ∀ i, ‖(if R < energy i then c i else 0)‖ ≤ ‖c i‖ := by
    exact Eventually.of_forall fun R i => by split_ifs <;> simp
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hc.norm hlim hbound

end Tail

section StrongTail

variable {𝕜 H K α ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- Uniformly bounded, strongly vanishing operators kill a square-summable family in
the summed squared norm. This is dominated convergence, with no rate asserted. -/
theorem square_sum_strong_tail (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (T : α → H →L[𝕜] H) (l : Filter α) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t, ‖T t‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun t => T t x) l (𝓝 0)) :
    Tendsto (fun t => ∑' i, ‖T t (v i)‖ ^ 2) l (𝓝 0) := by
  have hlim : ∀ i, Tendsto (fun t => ‖T t (v i)‖ ^ 2) l (𝓝 0) := by
    intro i
    simpa using ((hstrong (v i)).norm.pow 2)
  have hdom : ∀ᶠ t in l, ∀ i, ‖‖T t (v i)‖ ^ 2‖ ≤ C ^ 2 * ‖v i‖ ^ 2 := by
    apply Eventually.of_forall
    intro t i
    have ht : ‖T t (v i)‖ ≤ C * ‖v i‖ :=
      (T t).le_opNorm (v i) |>.trans
        (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hs := mul_nonneg (sub_nonneg.mpr ht)
      (add_nonneg (mul_nonneg hC (norm_nonneg (v i))) (norm_nonneg (T t (v i))))
    nlinarith
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence (hv.mul_left (C ^ 2)) hlim hdom

variable [CompleteSpace H] [CompleteSpace K]

/-- A coordinate form of the fixed Hilbert-Schmidt tail theorem, valid without a pure-point
spectrum for the multiplying operator. The summability hypothesis expresses that `F` is HS
using a fixed target basis. Right composition needs strong convergence of the ADJOINTS.
For the real spectral multipliers in the preprint those multipliers are self-adjoint. -/
theorem hs_right_tail_of_adjoint_strong (b : HilbertBasis ι 𝕜 K) (F : H →L[𝕜] K)
    (hF : Summable (fun i => ‖F.adjoint (b i)‖ ^ 2))
    (T : α → H →L[𝕜] H) (l : Filter α) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t, ‖(T t).adjoint‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun t => (T t).adjoint x) l (𝓝 0)) :
    Tendsto (fun t => ∑' i, ‖(F.comp (T t)).adjoint (b i)‖ ^ 2) l (𝓝 0) := by
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] using
    square_sum_strong_tail (fun i => F.adjoint (b i)) hF (fun t => (T t).adjoint)
      l C hC hbound hstrong

end StrongTail

section CenteredTrace

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem centered_second_order_bound (lam : ι → ℝ) (mu : κ → ℝ)
    (w : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j) (F dF : ℝ → ℝ) (C : ℝ)
    (hc : ∀ j, ∑ i, (lam i - mu j) * w i j = 0)
    (hrem : ∀ i j, |F (lam i) - F (mu j) - dF (mu j) * (lam i - mu j)|
      ≤ C * (lam i - mu j) ^ 2) :
    |∑ j, ∑ i, (F (lam i) - F (mu j)) * w i j|
      ≤ C * ∑ j, ∑ i, (lam i - mu j) ^ 2 * w i j := by
  have he : ∀ j, ∑ i, (F (lam i) - F (mu j)) * w i j =
      ∑ i, (F (lam i) - F (mu j) - dF (mu j) * (lam i - mu j)) * w i j := by
    intro j
    have hz : ∑ i, dF (mu j) * ((lam i - mu j) * w i j) = 0 := by
      rw [← Finset.mul_sum, hc, mul_zero]
    calc
      _ = (∑ i, (F (lam i) - F (mu j)) * w i j) -
          ∑ i, dF (mu j) * ((lam i - mu j) * w i j) := by rw [hz, sub_zero]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  simp_rw [he]
  calc
    _ ≤ ∑ j, |∑ i, (F (lam i) - F (mu j) - dF (mu j) * (lam i - mu j)) * w i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ i, C * ((lam i - mu j) ^ 2 * w i j) := by
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i j)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hrem i j) (hw i j)
    _ = _ := by simp only [Finset.mul_sum]

end CenteredTrace

/-- Countable version of the centered remainder estimate. Apply with
`value = (F lam - F mu) * w`, `linear = F' mu * (lam - mu) * w`,
`energy = (lam - mu)^2 * w`, and `C = Lip(F') / 2` after establishing Taylor's
remainder inequality. Absolute convergence of the full trace is part of the conclusion. -/
theorem countable_centered_remainder_bound {ι : Type*}
    (value linear energy : ι → ℝ) (C E : ℝ)
    (hlinear : HasSum linear 0) (henergy : HasSum energy E)
    (hrem : ∀ i, |value i - linear i| ≤ C * energy i) :
    Summable value ∧ |∑' i, value i| ≤ C * E := by
  have hbound : ∀ i, ‖value i - linear i‖ ≤ C * energy i := by
    simpa only [Real.norm_eq_abs] using hrem
  have hr : Summable (fun i => value i - linear i) :=
    Summable.of_norm_bounded (henergy.summable.mul_left C) hbound
  have hv : Summable value := by
    convert hr.add hlinear.summable using 1
    ext i
    ring
  refine ⟨hv, ?_⟩
  have heq : (∑' i, (value i - linear i)) = ∑' i, value i := by
    rw [hv.tsum_sub hlinear.summable, hlinear.tsum_eq, sub_zero]
  calc
    |∑' i, value i| = ‖∑' i, (value i - linear i)‖ := by rw [heq, Real.norm_eq_abs]
    _ ≤ ∑' i, ‖value i - linear i‖ := norm_tsum_le_tsum_norm hr.norm
    _ ≤ ∑' i, C * energy i := hr.norm.tsum_le_tsum hbound (henergy.summable.mul_left C)
    _ = C * E := (henergy.mul_left C).tsum_eq


end SteklovAudit.ReviewExtensions
