import Mathlib
import SteklovAudit.AffineWitnessFromOperator
import SteklovAudit.TaylorRemainder

/-!
# The whole centered trace on the affine probes (roadmap item G126)

The cutoff results (G114/G115) bound only the part of the centered trace above a cutoff. With residual
orthogonality `⟨u_j, A u_j − μ_j u_j⟩ = 0` (named hypothesis `ResidualOrth`), every first moment
`∑ᵢ (λᵢ − μ_j) Jᵢⱼ²` vanishes (`ReviewCandidates.residual_first_moment`), which removes the linear Taylor
term. With the `C¹,¹` remainder of G125 and the squared defect `16/a²` derived in G124,
`ReviewExtensions.countable_centered_remainder_bound` gives absolute convergence and

  `|∑_{i,j} (F λᵢ − F μ_j) Jᵢⱼ²| ≤ (B/2) · 16/a² = 8B/a²`        (`affine_full_trace_le`).

What this file does NOT prove: the operator data or residual orthogonality for the actual
Dirichlet-to-Neumann operator (for a tetrahedron–wedge identification orthogonality is not automatic),
the rate `B_L E_L = o(L)` a growing family would need, (7.29), H5, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.AffineFullTrace

open SteklovAudit.AffineCutoffTail SteklovAudit.AffineWitnessFromOperator
  SteklovAudit.ReviewCandidates SteklovAudit.ReviewExtensions SteklovAudit.TaylorRemainder

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {a : ℝ}

/-- Overlap `⟨b i, u j⟩`. -/
noncomputable def ovl (O : AffineOperatorData H ι a) (i : ι) (j : Fin 4) : ℝ :=
  inner ℝ (O.b i) (O.u j : H)

/-- Named hypothesis: each probe is orthogonal to its own residual. -/
def ResidualOrth (O : AffineOperatorData H ι a) : Prop :=
  ∀ j, inner ℝ (O.u j : H) (O.A (O.u j) - muVec a j • (O.u j : H)) = 0

/-- The first moment of each probe vanishes. -/
theorem first_moment (O : AffineOperatorData H ι a) (hO : ResidualOrth O) (j : Fin 4) :
    HasSum (fun i => (O.lam i - muVec a j) * ovl O i j ^ 2) 0 :=
  residual_first_moment O.b (O.u j : H) (O.A (O.u j) - muVec a j • (O.u j : H)) O.lam (muVec a j)
    (fun i => residual_coordinate O.D O.A O.symm ⟨O.b i, O.mem i⟩ (O.u j) (O.lam i) (muVec a j)
      (O.eig i))
    (hO j)

/-- Weighted first-moment summand on `ι × Fin 4`. -/
noncomputable def lin (O : AffineOperatorData H ι a) (c : Fin 4 → ℝ) (p : ι × Fin 4) : ℝ :=
  c p.2 * ((O.lam p.1 - muVec a p.2) * ovl O p.1 p.2 ^ 2)

/-- Weighted first moments vanish jointly on `ι × Fin 4`. -/
theorem weighted_first_moment (O : AffineOperatorData H ι a) (hO : ResidualOrth O)
    (c : Fin 4 → ℝ) : HasSum (lin O c) 0 := by
  classical
  have hj : ∀ j : Fin 4,
      HasSum (fun p : ι × Fin 4 => if p.2 = j then lin O c p else 0) 0 := by
    intro j
    have hinj : Function.Injective (fun i : ι => (i, j)) := fun i i' h => (Prod.mk.inj h).1
    have hf : ∀ x ∉ Set.range (fun i : ι => (i, j)),
        (fun p : ι × Fin 4 => if p.2 = j then lin O c p else 0) x = 0 := by
      rintro ⟨i, k⟩ hk
      have hkj : k ≠ j := by
        rintro rfl
        exact hk ⟨i, rfl⟩
      simp [hkj]
    refine (hinj.hasSum_iff hf).1 ?_
    have e : ((fun p : ι × Fin 4 => if p.2 = j then lin O c p else 0) ∘ fun i : ι => (i, j)) =
        fun i => c j * ((O.lam i - muVec a j) * ovl O i j ^ 2) := by
      funext i
      simp [lin]
    first
      | (rw [e]; exact (first_moment O hO j).mul_left (c j))
      | simpa [Function.comp_def, lin] using (first_moment O hO j).mul_left (c j)
  have hs := hasSum_sum (s := Finset.univ) (fun j _ => hj j)
  simpa using hs

/-- **G126.** The whole centered trace on the four affine probes is absolutely summable and at most
`8B/a²`, given operator data, residual orthogonality and a `B`-Lipschitz derivative `F'`. -/
theorem affine_full_trace_le (O : AffineOperatorData H ι a) (hO : ResidualOrth O)
    (F F' : ℝ → ℝ) (B : ℝ) (hd : ∀ x, HasDerivAt F (F' x) x)
    (hL : ∀ x y, |F' x - F' y| ≤ B * |x - y|) :
    Summable (fun p : ι × Fin 4 => (F (O.lam p.1) - F (muVec a p.2)) * ovl O p.1 p.2 ^ 2) ∧
      |∑' p : ι × Fin 4, (F (O.lam p.1) - F (muVec a p.2)) * ovl O p.1 p.2 ^ 2|
        ≤ 8 * B / a ^ 2 := by
  have hlin := weighted_first_moment O hO (fun j => F' (muVec a j))
  have hen : HasSum (fun p : ι × Fin 4 => (O.lam p.1 - muVec a p.2) ^ 2 * ovl O p.1 p.2 ^ 2)
      (16 / a ^ 2) := (sums_of_data O).2
  have hrem : ∀ p : ι × Fin 4,
      |(F (O.lam p.1) - F (muVec a p.2)) * ovl O p.1 p.2 ^ 2 - lin O (fun j => F' (muVec a j)) p|
        ≤ B / 2 * ((O.lam p.1 - muVec a p.2) ^ 2 * ovl O p.1 p.2 ^ 2) := by
    intro p
    have ht := taylor_remainder_of_lipschitz_deriv F F' B hd hL (O.lam p.1) (muVec a p.2)
    have hw : 0 ≤ ovl O p.1 p.2 ^ 2 := sq_nonneg _
    have e : (F (O.lam p.1) - F (muVec a p.2)) * ovl O p.1 p.2 ^ 2 -
        lin O (fun j => F' (muVec a j)) p =
        (F (O.lam p.1) - F (muVec a p.2) - F' (muVec a p.2) * (O.lam p.1 - muVec a p.2)) *
          ovl O p.1 p.2 ^ 2 := by
      simp only [lin]
      ring
    rw [e, abs_mul, abs_of_nonneg hw]
    calc _ ≤ B / 2 * (O.lam p.1 - muVec a p.2) ^ 2 * ovl O p.1 p.2 ^ 2 :=
          mul_le_mul_of_nonneg_right ht hw
      _ = _ := by ring
  have h := countable_centered_remainder_bound
    (fun p : ι × Fin 4 => (F (O.lam p.1) - F (muVec a p.2)) * ovl O p.1 p.2 ^ 2)
    (lin O (fun j => F' (muVec a j)))
    (fun p : ι × Fin 4 => (O.lam p.1 - muVec a p.2) ^ 2 * ovl O p.1 p.2 ^ 2)
    (B / 2) (16 / a ^ 2) hlin hen hrem
  refine ⟨h.1, ?_⟩
  have e : B / 2 * (16 / a ^ 2) = 8 * B / a ^ 2 := by ring
  rw [← e]
  exact h.2

end SteklovAudit.AffineFullTrace
