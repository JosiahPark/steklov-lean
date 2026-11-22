import Mathlib
import SteklovAudit.CountableCutoffTail

/-!
# Affine specialization of the countable cutoff tail (roadmap item G115)

For the solid regular tetrahedron of edge `a > 0` put `t = a / (2√2)` and `μaff = 1 / (√3 t)`.
The four affine probes `φ₀ = 1`, `φⱼ = √3 xⱼ` have comparison values `0, μaff, μaff, μaff`, and
`docs/affine-dtn-cutoff.md` computes their summed squared defect `0 + 3 · 2/(3t²) = 2/t² = 16/a²`.

Proved here: the arithmetic `2/t² = 16/a²`, `μaff = 2√2/(√3 a)`, `μaff > 0`, the residual sum
`0 + 3 · (2/(3t²)) = 16/a²` and the pairing value `2 (√3)²/(9t²) = 2/(3t²)`; and, GIVEN Parseval for
the four probes as the named hypothesis `AffineProbeParseval`, the cutoff bound
`|S − S≤L| ≤ 16 · Lip(F) / (a² (L − μaff))` for `L > μaff` (via `CountableCutoffTail.Cert.cutoff_tail_le`).

What this file does NOT prove: Parseval for the probes, the residual identities as statements about the
Dirichlet-to-Neumann operator (see `TetraAffineFlux.lean` for the finite midpoint identities), the existence
of a Steklov eigenbasis, or any of the open gaps (7.2), (7.29), (7.38)/(7.45), (9.1) or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.AffineCutoffTail

open SteklovAudit.CountableCutoffTail

/-- `t = a / (2√2)`. -/
noncomputable def tPar (a : ℝ) : ℝ := a / (2 * Real.sqrt 2)

/-- The affine Ritz value `μaff = 1 / (√3 t)`. -/
noncomputable def muAff (a : ℝ) : ℝ := 1 / (Real.sqrt 3 * tPar a)

theorem tPar_pos (a : ℝ) (ha : 0 < a) : 0 < tPar a := by
  unfold tPar
  exact div_pos ha (by positivity)

theorem muAff_pos (a : ℝ) (ha : 0 < a) : 0 < muAff a := by
  unfold muAff
  exact one_div_pos.mpr (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (tPar_pos a ha))

theorem tPar_sq (a : ℝ) : tPar a ^ 2 = a ^ 2 / 8 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold tPar
  rw [div_pow, mul_pow, h2]
  norm_num

/-- `2 / t² = 16 / a²`. -/
theorem affine_two_over_t_sq (a : ℝ) : 2 / tPar a ^ 2 = 16 / a ^ 2 := by
  rw [tPar_sq, div_div_eq_mul_div]
  ring

/-- `μaff = 2√2 / (√3 a)`. -/
theorem affine_mu_eq (a : ℝ) (ha : 0 < a) : muAff a = 2 * Real.sqrt 2 / (Real.sqrt 3 * a) := by
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ha' : a ≠ 0 := ha.ne'
  have h2' : Real.sqrt 2 ≠ 0 := h2.ne'
  have h3' : Real.sqrt 3 ≠ 0 := h3.ne'
  unfold muAff tPar
  first
    | (field_simp; done)
    | (field_simp; ring)
    | (rw [div_eq_div_iff (by positivity) (by positivity)]; field_simp; ring)

/-- The doc's residual pairing at `φⱼ = √3 xⱼ`: `2 (√3)² / (9 t²) = 2 / (3 t²)`. -/
theorem residual_pairing_phi (a : ℝ) (ha : 0 < a) :
    2 * Real.sqrt 3 ^ 2 / (9 * tPar a ^ 2) = 2 / (3 * tPar a ^ 2) := by
  have ht : tPar a ^ 2 ≠ 0 := (pow_pos (tPar_pos a ha) 2).ne'
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  first
    | (field_simp; done)
    | (field_simp; ring)

/-- The four residuals: `‖Rφ₀‖² = 0` and `‖Rφⱼ‖² = 2/(3t²)`, summing to `16/a²`. -/
theorem affine_residual_sum (a : ℝ) (ha : 0 < a) :
    0 + 3 * (2 / (3 * tPar a ^ 2)) = 16 / a ^ 2 := by
  have ht : tPar a ^ 2 ≠ 0 := (pow_pos (tPar_pos a ha) 2).ne'
  have e : 0 + 3 * (2 / (3 * tPar a ^ 2)) = 2 / tPar a ^ 2 := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  rw [e, affine_two_over_t_sq]

/-- Comparison values of the four probes: `0, μaff, μaff, μaff`. -/
noncomputable def muVec (a : ℝ) : Fin 4 → ℝ := ![0, muAff a, muAff a, muAff a]

theorem muVec_le (a : ℝ) (ha : 0 < a) (j : Fin 4) : muVec a j ≤ muAff a := by
  have h := (muAff_pos a ha).le
  fin_cases j <;> simp [muVec, h]

/-- Named hypothesis (NOT proved): Parseval for the four affine probes against a real orthonormal
Steklov eigenbasis with eigenvalues `lam` and overlaps `J i j = ⟨ψᵢ, φⱼ⟩`. -/
structure AffineProbeParseval {ι : Type*} (lam : ι → ℝ) (J : ι → Fin 4 → ℝ) (a : ℝ) : Prop where
  mass : HasSum (fun p : ι × Fin 4 => J p.1 p.2 ^ 2) 4
  defect : HasSum (fun p : ι × Fin 4 => (lam p.1 - muVec a p.2) ^ 2 * J p.1 p.2 ^ 2) (16 / a ^ 2)

variable {ι : Type*} {lam : ι → ℝ} {J : ι → Fin 4 → ℝ} {a : ℝ}

/-- The finite certificates obtained from Parseval (`M = 4`, `E = 16/a²`). -/
noncomputable def certOf (P : AffineProbeParseval lam J a) : Cert ι (Fin 4) where
  lam := lam
  mu := muVec a
  w := fun i j => J i j ^ 2
  M := 4
  E := 16 / a ^ 2
  hw := fun i j => sq_nonneg _
  hM := fun s => sum_le_hasSum s (fun p _ => sq_nonneg _) P.mass
  hE := fun s => sum_le_hasSum s (fun p _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) P.defect

/-- **G115.** Given Parseval for the four probes, the cutoff discrepancy above `L > μaff` is at most
`16 · Lip(F) / (a² (L − μaff))`. -/
theorem affine_cutoff_tail (P : AffineProbeParseval lam J a) (ha : 0 < a) (F : ℝ → ℝ) (Lf : ℝ)
    (hLf : 0 ≤ Lf) (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (L : ℝ) (hL : muAff a < L) :
    |(certOf P).S F - (certOf P).Sle F L| ≤ 16 * Lf / (a ^ 2 * (L - muAff a)) := by
  have h := (certOf P).cutoff_tail_le F Lf hLf hF (muAff a) L (fun j => muVec_le a ha j) hL
  have e : Lf * (certOf P).E / (L - muAff a) = 16 * Lf / (a ^ 2 * (L - muAff a)) := by
    show Lf * (16 / a ^ 2) / (L - muAff a) = 16 * Lf / (a ^ 2 * (L - muAff a))
    ring
  rw [e] at h
  exact h

end SteklovAudit.AffineCutoffTail
