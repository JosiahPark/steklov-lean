import Mathlib
import SteklovAudit.AbstractTransfer
import SteklovAudit.AbstractTransferB2

/-!
# R3: trace of the localized propagator difference (R27.2 in spectral coordinates)

At a finite cutoff with a common index type, `U(t) = e^{itA} J - J e^{itB}` has coefficients
`U i j = (exp(i t a_i) - exp(i t b_j)) J i j` (the order of the two exponentials only changes the
sign, not the norms used here). For the coordinate projection `P` onto a finite set `s` of rank
`r = s.card`, `Tr(P U(t) P) = Σ_{i ∈ s} U i i`, and

  `|Tr(P U(t) P)| ≤ √r · |t| · ‖K‖_HS`        (`propagator_trace`),

with squared form `propagator_trace_sq`. The proof is the Cauchy–Schwarz step of
`trace_rank_amplification` (`SpectralCounting.lean`) applied to the entrywise Duhamel bound
`duhamel_entry_sq` (B2). `propagator_trace_of_inputs` inserts the named Lemma 7.1' input.

What this file does NOT prove:
* It constructs no Dirichlet-to-Neumann operator and no unitary group on a Hilbert space; the
  eigenvalues and coefficients are arbitrary finite data.
* It gives no bound on `‖K‖_HS`; Lemma 7.1' enters only as the named hypothesis
  `PDEInputs.defect`.
* The factor `√r` is not removed: with `r ~ L²` this bound alone does not give the o(L) trace
  comparison (7.29), and it proves none of `[H1]`–`[H6]` nor the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.PropagatorTrace

open SteklovAudit.AbstractTransfer
open Finset

variable {ι : Type*} [Fintype ι]

/-- Coefficients of `U(t) = e^{itA} J - J e^{itB}` in the two eigenbases. -/
noncomputable def U (D : Data ι ι) (t : ℝ) (i j : ι) : ℂ :=
  (Complex.exp (Complex.I * ((t * D.a i : ℝ) : ℂ)) -
    Complex.exp (Complex.I * ((t * D.b j : ℝ) : ℂ))) * ((D.J i j : ℝ) : ℂ)

/-- The diagonal of the defect over `s` is bounded by the full squared HS norm. -/
theorem diag_K_le_hs2 (D : Data ι ι) (s : Finset ι) :
    ∑ i ∈ s, D.K i i ^ 2 ≤ hs2 D.K := by
  unfold hs2
  calc ∑ i ∈ s, D.K i i ^ 2 ≤ ∑ i, D.K i i ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun i _ _ => sq_nonneg _)
    _ ≤ ∑ i, ∑ j, D.K i j ^ 2 := by
        apply sum_le_sum
        intro i _
        exact single_le_sum (f := fun j => D.K i j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)

/-- R3, squared form: `|Tr(P U(t) P)|² ≤ rank P · t² · ‖K‖²_HS`. -/
theorem propagator_trace_sq (D : Data ι ι) (t : ℝ) (s : Finset ι) :
    ‖∑ i ∈ s, U D t i i‖ ^ 2 ≤ (s.card : ℝ) * (t ^ 2 * hs2 D.K) := by
  have h1 : ‖∑ i ∈ s, U D t i i‖ ≤ ∑ i ∈ s, ‖U D t i i‖ := norm_sum_le _ _
  have h2 : (∑ i ∈ s, ‖U D t i i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖U D t i i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ i ∈ s, ‖U D t i i‖ ^ 2 ≤ t ^ 2 * hs2 D.K := by
    calc ∑ i ∈ s, ‖U D t i i‖ ^ 2 ≤ ∑ i ∈ s, t ^ 2 * D.K i i ^ 2 :=
          sum_le_sum (fun i _ => duhamel_entry_sq D t i i)
      _ = t ^ 2 * ∑ i ∈ s, D.K i i ^ 2 := by rw [mul_sum]
      _ ≤ t ^ 2 * hs2 D.K := mul_le_mul_of_nonneg_left (diag_K_le_hs2 D s) (sq_nonneg t)
  have h0 : 0 ≤ ‖∑ i ∈ s, U D t i i‖ := norm_nonneg _
  have hc : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have h4 : ‖∑ i ∈ s, U D t i i‖ ^ 2 ≤ (∑ i ∈ s, ‖U D t i i‖) ^ 2 := by
    nlinarith [h0, h1]
  calc ‖∑ i ∈ s, U D t i i‖ ^ 2 ≤ (∑ i ∈ s, ‖U D t i i‖) ^ 2 := h4
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖U D t i i‖ ^ 2 := h2
    _ ≤ (s.card : ℝ) * (t ^ 2 * hs2 D.K) := mul_le_mul_of_nonneg_left h3 hc

/-- R3 (R27.2 in coordinates): `|Tr(P U(t) P)| ≤ √(rank P) · |t| · ‖K‖_HS`. -/
theorem propagator_trace (D : Data ι ι) (t : ℝ) (s : Finset ι) :
    ‖∑ i ∈ s, U D t i i‖ ≤ Real.sqrt (s.card : ℝ) * |t| * Real.sqrt (hs2 D.K) := by
  have h := propagator_trace_sq D t s
  have e : Real.sqrt ((s.card : ℝ) * (t ^ 2 * hs2 D.K)) =
      Real.sqrt (s.card : ℝ) * |t| * Real.sqrt (hs2 D.K) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
    try ring
  rw [← e, ← Real.sqrt_sq (norm_nonneg (∑ i ∈ s, U D t i i))]
  exact Real.sqrt_le_sqrt h

/-- R3 with the named Lemma 7.1' input `PDEInputs.defect` (not proved here):
`|Tr(P U(t) P)|² ≤ rank P · t² · Ck² (1 + L)²`. -/
theorem propagator_trace_of_inputs (D : Data ι ι) (t L Cm Ck : ℝ) (s : Finset ι)
    (H : PDEInputs D L Cm Ck) :
    ‖∑ i ∈ s, U D t i i‖ ^ 2 ≤ (s.card : ℝ) * (t ^ 2 * (Ck ^ 2 * (1 + L) ^ 2)) := by
  have h := propagator_trace_sq D t s
  have h2 : t ^ 2 * hs2 D.K ≤ t ^ 2 * (Ck ^ 2 * (1 + L) ^ 2) :=
    mul_le_mul_of_nonneg_left H.defect (sq_nonneg t)
  exact le_trans h (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))

end SteklovAudit.PropagatorTrace
