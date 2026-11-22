import Mathlib

/-!
# Countable cutoff tail from finite certificates (roadmap items G113, G114)

Abstract setting for the passage from the finite-sum certificate of `docs/affine-dtn-cutoff.md` §3 to a
countable eigenbasis. Indices: `ι` (eigenbasis), `κ` (probes); neither needs to be finite. Weights
`w i j ≥ 0` stand for `|J i j|²`, `lam i` for eigenvalues, `mu j` for comparison values.

A `Cert` packages finite certificates: every finite partial sum of the weights is `≤ M` and every
finite partial sum of the squared defects `(lam i − mu j)² w i j` is `≤ E`.

Proved here:
* G113: both series are summable with sums `≤ M` and `≤ E`; for Lipschitz `F` the centered series
  `∑ (F (lam i) − F (mu j)) w i j` is absolutely summable (`summable_centered`), using
  `|d| ≤ (1 + d²)/2`.
* G114: for `mu j ≤ muStar < L`, the part of the centered series with `lam i > L` is at most
  `Lip(F) · E / (L − muStar)` in absolute value (`cutoff_tail_le`).

What this file does NOT prove: anything about the Dirichlet-to-Neumann operator, its spectrum or
eigenbasis, Parseval for any probe family, the value `E = 16/a²`, or any of the open gaps
(7.2), (7.29), (7.38)/(7.45), (9.1) or Theorem 1.3 / 11.1. The certificates are hypotheses.
-/

namespace SteklovAudit.CountableCutoffTail

/-- Finite certificates for weights `w`, eigenvalues `lam` and comparison values `mu`. -/
structure Cert (ι : Type*) (κ : Type*) where
  lam : ι → ℝ
  mu : κ → ℝ
  w : ι → κ → ℝ
  M : ℝ
  E : ℝ
  hw : ∀ i j, 0 ≤ w i j
  hM : ∀ s : Finset (ι × κ), ∑ p ∈ s, w p.1 p.2 ≤ M
  hE : ∀ s : Finset (ι × κ), ∑ p ∈ s, (lam p.1 - mu p.2) ^ 2 * w p.1 p.2 ≤ E

end SteklovAudit.CountableCutoffTail

namespace SteklovAudit.CountableCutoffTail.Cert

variable {ι κ : Type*} (X : Cert ι κ)

/-- Mass summand `w i j`. -/
def mass (p : ι × κ) : ℝ := X.w p.1 p.2

/-- Second-moment summand `(lam i − mu j)² w i j`. -/
def moment (p : ι × κ) : ℝ := (X.lam p.1 - X.mu p.2) ^ 2 * X.w p.1 p.2

/-- Centered Lipschitz summand `(F (lam i) − F (mu j)) w i j`. -/
def centered (F : ℝ → ℝ) (p : ι × κ) : ℝ := (F (X.lam p.1) - F (X.mu p.2)) * X.w p.1 p.2

/-- The full centered series. -/
noncomputable def S (F : ℝ → ℝ) : ℝ := ∑' p, X.centered F p

/-- The centered series restricted to `lam i ≤ L`. -/
noncomputable def Sle (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∑' p : ι × κ, if X.lam p.1 ≤ L then X.centered F p else 0

theorem mass_nonneg (p : ι × κ) : 0 ≤ X.mass p := X.hw p.1 p.2

theorem moment_nonneg (p : ι × κ) : 0 ≤ X.moment p :=
  mul_nonneg (sq_nonneg _) (X.hw p.1 p.2)

theorem M_nonneg : 0 ≤ X.M := by simpa using X.hM ∅

theorem E_nonneg : 0 ≤ X.E := by simpa using X.hE ∅

/-- G113: the weights are summable. -/
theorem summable_mass : Summable X.mass :=
  summable_of_sum_le (fun p => X.mass_nonneg p) (fun s => X.hM s)

/-- G113: the total mass is at most `M`. -/
theorem tsum_mass_le : ∑' p, X.mass p ≤ X.M := by
  first
    | exact tsum_le_of_sum_le' X.M_nonneg (fun s => X.hM s)
    | exact X.summable_mass.tsum_le_of_sum_le (fun s => X.hM s)
    | exact tsum_le_of_sum_le X.summable_mass (fun s => X.hM s)

/-- G113: the squared defects are summable. -/
theorem summable_moment : Summable X.moment :=
  summable_of_sum_le (fun p => X.moment_nonneg p) (fun s => X.hE s)

/-- G113: the summed squared defect is at most `E`. -/
theorem tsum_moment_le : ∑' p, X.moment p ≤ X.E := by
  first
    | exact tsum_le_of_sum_le' X.E_nonneg (fun s => X.hE s)
    | exact X.summable_moment.tsum_le_of_sum_le (fun s => X.hE s)
    | exact tsum_le_of_sum_le X.summable_moment (fun s => X.hE s)

end SteklovAudit.CountableCutoffTail.Cert

namespace SteklovAudit.CountableCutoffTail

/-- `|d| ≤ (1 + d²) / 2`. -/
theorem abs_le_half_one_add_sq (d : ℝ) : |d| ≤ (1 + d ^ 2) / 2 := by
  nlinarith [sq_nonneg (|d| - 1), sq_abs d]

end SteklovAudit.CountableCutoffTail

namespace SteklovAudit.CountableCutoffTail.Cert

variable {ι κ : Type*} (X : Cert ι κ)

/-- The summable majorant `Lf · (w + (lam − mu)² w) / 2`. -/
noncomputable def bound (Lf : ℝ) (p : ι × κ) : ℝ := Lf * ((X.mass p + X.moment p) / 2)

theorem bound_nonneg (Lf : ℝ) (hLf : 0 ≤ Lf) (p : ι × κ) : 0 ≤ X.bound Lf p :=
  mul_nonneg hLf (div_nonneg (add_nonneg (X.mass_nonneg p) (X.moment_nonneg p)) (by norm_num))

theorem summable_bound (Lf : ℝ) : Summable (X.bound Lf) :=
  ((X.summable_mass.add X.summable_moment).div_const 2).mul_left Lf

/-- Termwise bound: `|(F λ − F μ) w| ≤ Lf · (w + (λ − μ)² w) / 2`. -/
theorem centered_abs_le (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (p : ι × κ) :
    |X.centered F p| ≤ X.bound Lf p := by
  have hwp : 0 ≤ X.w p.1 p.2 := X.hw p.1 p.2
  unfold centered bound mass moment
  rw [abs_mul, abs_of_nonneg hwp]
  have h3 : |F (X.lam p.1) - F (X.mu p.2)| ≤ Lf * ((1 + (X.lam p.1 - X.mu p.2) ^ 2) / 2) :=
    (hF _ _).trans (mul_le_mul_of_nonneg_left (abs_le_half_one_add_sq _) hLf)
  calc |F (X.lam p.1) - F (X.mu p.2)| * X.w p.1 p.2
      ≤ Lf * ((1 + (X.lam p.1 - X.mu p.2) ^ 2) / 2) * X.w p.1 p.2 :=
        mul_le_mul_of_nonneg_right h3 hwp
    _ = Lf * ((X.w p.1 p.2 + (X.lam p.1 - X.mu p.2) ^ 2 * X.w p.1 p.2) / 2) := by ring

/-- Summability from a nonnegative summable majorant of the absolute values. -/
theorem summable_of_abs_le {f g : ι × κ → ℝ} (hg : Summable g) (h : ∀ p, |f p| ≤ g p) :
    Summable f := by
  have h' : ∀ p, ‖f p‖ ≤ g p := fun p => by rw [Real.norm_eq_abs]; exact h p
  first
    | exact Summable.of_norm_bounded hg h'
    | exact Summable.of_norm_bounded g hg h'
    | exact hg.of_norm_bounded h'

/-- **G113.** The centered Lipschitz series is absolutely summable. -/
theorem summable_centered (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) : Summable (X.centered F) :=
  summable_of_abs_le (X.summable_bound Lf) (X.centered_abs_le F Lf hLf hF)

theorem summable_le_part (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (L : ℝ) :
    Summable (fun p : ι × κ => if X.lam p.1 ≤ L then X.centered F p else 0) := by
  refine summable_of_abs_le (X.summable_bound Lf) (fun p => ?_)
  by_cases h : X.lam p.1 ≤ L
  · rw [if_pos h]; exact X.centered_abs_le F Lf hLf hF p
  · rw [if_neg h, abs_zero]; exact X.bound_nonneg Lf hLf p

theorem summable_gt_part (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (L : ℝ) :
    Summable (fun p : ι × κ => if L < X.lam p.1 then X.centered F p else 0) := by
  refine summable_of_abs_le (X.summable_bound Lf) (fun p => ?_)
  by_cases h : L < X.lam p.1
  · rw [if_pos h]; exact X.centered_abs_le F Lf hLf hF p
  · rw [if_neg h, abs_zero]; exact X.bound_nonneg Lf hLf p

/-- G114: the full series minus its part below `L` is its part above `L`. -/
theorem S_sub_Sle (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (L : ℝ) :
    X.S F - X.Sle F L = ∑' p : ι × κ, if L < X.lam p.1 then X.centered F p else 0 := by
  have hs := X.summable_centered F Lf hLf hF
  have hle := X.summable_le_part F Lf hLf hF L
  have e : ∀ p : ι × κ, (X.centered F p - (if X.lam p.1 ≤ L then X.centered F p else 0)) =
      (if L < X.lam p.1 then X.centered F p else 0) := by
    intro p
    by_cases h : X.lam p.1 ≤ L
    · rw [if_pos h, if_neg (not_lt.mpr h), sub_self]
    · rw [if_neg h, if_pos (not_le.mp h), sub_zero]
  have hsub : ∑' p : ι × κ, (X.centered F p - (if X.lam p.1 ≤ L then X.centered F p else 0)) =
      X.S F - X.Sle F L := by
    unfold S Sle
    first
      | exact Summable.tsum_sub hs hle
      | exact tsum_sub hs hle
  rw [← hsub]
  exact tsum_congr e

/-- G114, termwise: above the cutoff, `|(F λ − F μ) w| ≤ Lf / (L − μ*) · (λ − μ)² w`. -/
theorem tail_term_le (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (muStar L : ℝ) (hmu : ∀ j, X.mu j ≤ muStar)
    (hL : muStar < L) (p : ι × κ) (hp : L < X.lam p.1) :
    |X.centered F p| ≤ Lf / (L - muStar) * X.moment p := by
  have hwp : 0 ≤ X.w p.1 p.2 := X.hw p.1 p.2
  unfold centered moment
  rw [abs_mul, abs_of_nonneg hwp]
  have hd : L - muStar ≤ X.lam p.1 - X.mu p.2 := by linarith [hmu p.2]
  have hg : 0 < L - muStar := by linarith
  have hdpos : 0 < X.lam p.1 - X.mu p.2 := lt_of_lt_of_le hg hd
  have h1 : |F (X.lam p.1) - F (X.mu p.2)| ≤ Lf * (X.lam p.1 - X.mu p.2) := by
    have h := hF (X.lam p.1) (X.mu p.2)
    rwa [abs_of_pos hdpos] at h
  have hdd : (X.lam p.1 - X.mu p.2) * (L - muStar) ≤ (X.lam p.1 - X.mu p.2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hd hdpos.le
    nlinarith [this]
  have h2 : X.lam p.1 - X.mu p.2 ≤ (X.lam p.1 - X.mu p.2) ^ 2 / (L - muStar) := by
    first
      | exact (le_div_iff₀ hg).2 hdd
      | exact (le_div_iff hg).2 hdd
  calc |F (X.lam p.1) - F (X.mu p.2)| * X.w p.1 p.2
      ≤ Lf * (X.lam p.1 - X.mu p.2) * X.w p.1 p.2 := mul_le_mul_of_nonneg_right h1 hwp
    _ ≤ Lf * ((X.lam p.1 - X.mu p.2) ^ 2 / (L - muStar)) * X.w p.1 p.2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hLf) hwp
    _ = Lf / (L - muStar) * ((X.lam p.1 - X.mu p.2) ^ 2 * X.w p.1 p.2) := by ring

/-- **G114.** Cutoff tail bound: `|S F − Sle F L| ≤ Lf · E / (L − μ*)` whenever every `mu j ≤ μ* < L`. -/
theorem cutoff_tail_le (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (muStar L : ℝ) (hmu : ∀ j, X.mu j ≤ muStar)
    (hL : muStar < L) :
    |X.S F - X.Sle F L| ≤ Lf * X.E / (L - muStar) := by
  have hg : 0 < L - muStar := by linarith
  have hc : 0 ≤ Lf / (L - muStar) := div_nonneg hLf hg.le
  have hT := X.summable_gt_part F Lf hLf hF L
  have hb : Summable (fun p : ι × κ => Lf / (L - muStar) * X.moment p) :=
    X.summable_moment.mul_left _
  have hpt : ∀ p : ι × κ, |(if L < X.lam p.1 then X.centered F p else 0)| ≤
      Lf / (L - muStar) * X.moment p := by
    intro p
    by_cases h : L < X.lam p.1
    · rw [if_pos h]; exact X.tail_term_le F Lf hLf hF muStar L hmu hL p h
    · rw [if_neg h, abs_zero]; exact mul_nonneg hc (X.moment_nonneg p)
  have hup : (∑' p : ι × κ, if L < X.lam p.1 then X.centered F p else 0) ≤
      ∑' p : ι × κ, Lf / (L - muStar) * X.moment p := by
    first
      | exact Summable.tsum_le_tsum (fun p => (abs_le.mp (hpt p)).2) hT hb
      | exact tsum_le_tsum (fun p => (abs_le.mp (hpt p)).2) hT hb
  have hlo : (∑' p : ι × κ, -(Lf / (L - muStar) * X.moment p)) ≤
      ∑' p : ι × κ, if L < X.lam p.1 then X.centered F p else 0 := by
    first
      | exact Summable.tsum_le_tsum (fun p => (abs_le.mp (hpt p)).1) hb.neg hT
      | exact tsum_le_tsum (fun p => (abs_le.mp (hpt p)).1) hb.neg hT
  rw [tsum_neg] at hlo
  have hmul : ∑' p : ι × κ, Lf / (L - muStar) * X.moment p =
      Lf / (L - muStar) * ∑' p : ι × κ, X.moment p := by
    first
      | exact tsum_mul_left
      | exact X.summable_moment.tsum_mul_left _
  have hB : ∑' p : ι × κ, Lf / (L - muStar) * X.moment p ≤ Lf * X.E / (L - muStar) := by
    rw [hmul]
    calc Lf / (L - muStar) * ∑' p : ι × κ, X.moment p ≤ Lf / (L - muStar) * X.E :=
          mul_le_mul_of_nonneg_left X.tsum_moment_le hc
      _ = Lf * X.E / (L - muStar) := by ring
  rw [X.S_sub_Sle F Lf hLf hF L]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SteklovAudit.CountableCutoffTail.Cert

namespace SteklovAudit.CountableCutoffTail

end SteklovAudit.CountableCutoffTail
