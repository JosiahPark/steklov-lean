import Mathlib
import SteklovAudit.AbstractTransfer

/-!
# Spectral leakage and counting transfer at a finite cutoff (continuations 25–43, compiled)

The hourly continuations 25–43 proved several finite-dimensional facts on paper and recorded only
scalar Lean fragments. This module states and proves the operator-level versions in the spectral
coordinates of `SteklovAudit.AbstractTransfer` (`Data`, `Data.K`, `hs2`): eigenvalues `a i` of `A`,
`b j` of `B`, identification coefficients `J i j`, defect `K i j = (a i - b j) J i j`.

* `window_gap_leakage` (continuation 25): for spectral windows at distance `≥ δ`,
  `δ² ‖P_Q J P_I‖²_HS ≤ ‖P_Q K P_I‖²_HS`.
* `weighted_leakage` (continuation 42): `‖(A - L)_+ J 1_{B ≤ L}‖²_HS ≤ ‖K 1_{B ≤ L}‖²_HS`.
* `counting_transfer` (continuations 30, 39): if every row of `J` has norm `≤ 1`
  (implied by `‖J‖ ≤ 1`), then
  `N_B(L) ≤ N_A(L + δ) + Σ_{b_j ≤ L} (1 - ‖J e_j‖²) + δ⁻² ‖K 1_{B ≤ L}‖²_HS`.
* `counting_two_sided` (continuation 32): the same with the roles of `A` and `B` exchanged.
* `threshold_instability` (continuation 33): with `J = I` and `‖K‖²_HS = 1/n`, the two counts at
  the same threshold differ by `n`, so the spectral shift `δ > 0` in the transfer cannot be removed.
* `trace_rank_amplification` (continuation 27): `|Tr(P T P)|² ≤ rank P · ‖T P‖²_HS`, so a uniform
  HS bound costs a factor `√rank` when converted to a trace bound.

The finite-dimensional Lipschitz transfer of continuation 43 is already
`SteklovAudit.AbstractTransfer.transfer_hs`.

What this module does NOT prove: anything about the tetrahedral Steklov operator. No
Dirichlet-to-Neumann operator, identification `J` or defect bound for the tetrahedron is constructed;
the operators are arbitrary finite spectral data, and the passage to infinite dimensions is not
formalized.
-/

namespace SteklovAudit.AbstractTransfer

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Number of eigenvalues `≤ L`: the counting function at a finite cutoff. -/
noncomputable def count {τ : Type*} [Fintype τ] (e : τ → ℝ) (L : ℝ) : ℕ :=
  (univ.filter (fun t => e t ≤ L)).card

/-- Spectral-window leakage (continuation 25). -/
theorem window_gap_leakage (D : Data ι κ) (sQ : Finset ι) (sI : Finset κ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgap : ∀ i ∈ sQ, ∀ j ∈ sI, δ ≤ |D.a i - D.b j|) :
    δ ^ 2 * ∑ j ∈ sI, ∑ i ∈ sQ, D.J i j ^ 2 ≤ ∑ j ∈ sI, ∑ i ∈ sQ, D.K i j ^ 2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have h := hgap i hi j hj
  have hsq : δ ^ 2 ≤ (D.a i - D.b j) ^ 2 := by
    nlinarith [abs_nonneg (D.a i - D.b j), sq_abs (D.a i - D.b j)]
  unfold Data.K
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- Weighted spectral leakage (continuation 42). -/
theorem weighted_leakage (D : Data ι κ) (L : ℝ) :
    ∑ j ∈ univ.filter (fun j => D.b j ≤ L), ∑ i, (max (D.a i - L) 0) ^ 2 * D.J i j ^ 2
      ≤ ∑ j ∈ univ.filter (fun j => D.b j ≤ L), ∑ i, D.K i j ^ 2 := by
  apply sum_le_sum
  intro j hj
  have hb : D.b j ≤ L := (mem_filter.mp hj).2
  apply sum_le_sum
  intro i _
  have hsq : (max (D.a i - L) 0) ^ 2 ≤ (D.a i - D.b j) ^ 2 := by
    rcases le_total (D.a i - L) 0 with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (D.a i - D.b j)]
    · rw [max_eq_left h]
      have h2 : 0 ≤ 2 * D.a i - D.b j - L := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hb) h2]
  unfold Data.K
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- One-sided counting transfer (continuations 30, 39). The hypothesis `hrow` says every row of
`J` has norm at most one, which holds when `J` is a contraction. -/
theorem counting_transfer (D : Data ι κ) (L δ : ℝ) (hδ : 0 < δ)
    (hrow : ∀ i, ∑ j, D.J i j ^ 2 ≤ 1) :
    (count D.b L : ℝ) ≤ count D.a (L + δ)
      + ∑ j ∈ univ.filter (fun j => D.b j ≤ L), (1 - ∑ i, D.J i j ^ 2)
      + (∑ j ∈ univ.filter (fun j => D.b j ≤ L), ∑ i, D.K i j ^ 2) / δ ^ 2 := by
  have hcardP : (count D.b L : ℝ) = ∑ j ∈ univ.filter (fun j => D.b j ≤ L), (1 : ℝ) := by
    unfold count
    rw [sum_const, nsmul_eq_mul, mul_one]
  have hcardQ : (count D.a (L + δ) : ℝ) = ∑ i ∈ univ.filter (fun i => D.a i ≤ L + δ), (1 : ℝ) := by
    unfold count
    rw [sum_const, nsmul_eq_mul, mul_one]
  have hsplit : ∀ j, ∑ i, D.J i j ^ 2 =
      ∑ i ∈ univ.filter (fun i => D.a i ≤ L + δ), D.J i j ^ 2
        + ∑ i ∈ univ.filter (fun i => ¬ D.a i ≤ L + δ), D.J i j ^ 2 := fun j =>
    (sum_filter_add_sum_filter_not univ (fun i => D.a i ≤ L + δ) (fun i => D.J i j ^ 2)).symm
  have hlow : ∑ j ∈ univ.filter (fun j => D.b j ≤ L),
      ∑ i ∈ univ.filter (fun i => D.a i ≤ L + δ), D.J i j ^ 2
        ≤ ∑ i ∈ univ.filter (fun i => D.a i ≤ L + δ), (1 : ℝ) := by
    rw [sum_comm]
    apply sum_le_sum
    intro i _
    calc ∑ j ∈ univ.filter (fun j => D.b j ≤ L), D.J i j ^ 2 ≤ ∑ j, D.J i j ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => sq_nonneg _)
      _ ≤ 1 := hrow i
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hhigh : ∑ j ∈ univ.filter (fun j => D.b j ≤ L),
      ∑ i ∈ univ.filter (fun i => ¬ D.a i ≤ L + δ), D.J i j ^ 2
        ≤ (∑ j ∈ univ.filter (fun j => D.b j ≤ L), ∑ i, D.K i j ^ 2) / δ ^ 2 := by
    rw [le_div_iff₀ hδ2, sum_mul]
    apply sum_le_sum
    intro j hj
    have hb : D.b j ≤ L := (mem_filter.mp hj).2
    rw [sum_mul]
    calc ∑ i ∈ univ.filter (fun i => ¬ D.a i ≤ L + δ), D.J i j ^ 2 * δ ^ 2
        ≤ ∑ i ∈ univ.filter (fun i => ¬ D.a i ≤ L + δ), D.K i j ^ 2 := by
          apply sum_le_sum
          intro i hi
          have ha : ¬ D.a i ≤ L + δ := (mem_filter.mp hi).2
          push_neg at ha
          have hpos : δ ≤ D.a i - D.b j := by linarith
          have hsq : δ ^ 2 ≤ (D.a i - D.b j) ^ 2 := by nlinarith
          unfold Data.K
          rw [mul_pow, mul_comm (D.J i j ^ 2)]
          exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ ≤ ∑ i, D.K i j ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => sq_nonneg _)
  have hid : (count D.b L : ℝ) =
      ∑ j ∈ univ.filter (fun j => D.b j ≤ L), (1 - ∑ i, D.J i j ^ 2)
        + (∑ j ∈ univ.filter (fun j => D.b j ≤ L),
            ∑ i ∈ univ.filter (fun i => D.a i ≤ L + δ), D.J i j ^ 2
          + ∑ j ∈ univ.filter (fun j => D.b j ≤ L),
            ∑ i ∈ univ.filter (fun i => ¬ D.a i ≤ L + δ), D.J i j ^ 2) := by
    rw [hcardP, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rw [← hsplit j]
    ring
  rw [hid, hcardQ]
  linarith

/-- Exchange the roles of `A` and `B`. -/
def Data.swap (D : Data ι κ) : Data κ ι := ⟨D.b, D.a, fun j i => D.J i j⟩

theorem swap_K_sq (D : Data ι κ) (j : κ) (i : ι) : D.swap.K j i ^ 2 = D.K i j ^ 2 := by
  unfold Data.K Data.swap
  ring

/-- Two-sided counting transfer (continuation 32). Only the model side needs a Weyl law to
conclude one for the other side. -/
theorem counting_two_sided (D : Data ι κ) (L δ : ℝ) (hδ : 0 < δ)
    (hrow : ∀ i, ∑ j, D.J i j ^ 2 ≤ 1) (hcol : ∀ j, ∑ i, D.J i j ^ 2 ≤ 1) :
    (count D.b L : ℝ) ≤ count D.a (L + δ)
        + ∑ j ∈ univ.filter (fun j => D.b j ≤ L), (1 - ∑ i, D.J i j ^ 2)
        + (∑ j ∈ univ.filter (fun j => D.b j ≤ L), ∑ i, D.K i j ^ 2) / δ ^ 2 ∧
      (count D.a L : ℝ) ≤ count D.b (L + δ)
        + ∑ i ∈ univ.filter (fun i => D.a i ≤ L), (1 - ∑ j, D.J i j ^ 2)
        + (∑ i ∈ univ.filter (fun i => D.a i ≤ L), ∑ j, D.K i j ^ 2) / δ ^ 2 := by
  refine ⟨counting_transfer D L δ hδ hrow, ?_⟩
  have h := counting_transfer D.swap L δ hδ hcol
  simp only [swap_K_sq] at h
  exact h

/-- Threshold instability (continuation 33): an exact unitary identification with
`‖K‖²_HS = 1/n` still moves `n` eigenvalues across the threshold `0`. -/
theorem threshold_instability (n : ℕ) (hn : 0 < n) :
    ∃ D : Data (Fin n) (Fin n),
      hs2 D.K = 1 / n ∧ (∀ i, ∑ j, D.J i j ^ 2 = 1) ∧ (∀ j, ∑ i, D.J i j ^ 2 = 1) ∧
      count D.b 0 = n ∧ count D.a 0 = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpos : (0 : ℝ) < 1 / n := by positivity
  refine ⟨⟨fun _ => 1 / n, fun _ => 0, fun i j => if i = j then 1 else 0⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have hrow : ∀ i : Fin n, ∑ j : Fin n, ((1 / (n : ℝ) - 0) * (if i = j then (1 : ℝ) else 0)) ^ 2
        = (1 / (n : ℝ)) ^ 2 := by
      intro i
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    show ∑ i : Fin n, ∑ j : Fin n, ((1 / (n : ℝ) - 0) * (if i = j then (1 : ℝ) else 0)) ^ 2 = 1 / (n : ℝ)
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, div_pow, one_pow, mul_one_div, sq, ← div_div, div_self hn']
  · intro i
    show ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) ^ 2 = 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · intro j
    show ∑ i : Fin n, (if i = j then (1 : ℝ) else 0) ^ 2 = 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · show (univ.filter (fun _ : Fin n => (0 : ℝ) ≤ 0)).card = n
    simp
  · show (univ.filter (fun _ : Fin n => (1 : ℝ) / n ≤ 0)).card = 0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    exact not_le.mpr hpos

/-- Trace-rank amplification (continuation 27): `|Tr(P T P)|² ≤ rank P · ‖T P‖²_HS`, with `P` the
coordinate projection onto `s`. -/
theorem trace_rank_amplification (T : ι → ι → ℝ) (s : Finset ι) :
    (∑ j ∈ s, T j j) ^ 2 ≤ s.card * ∑ j ∈ s, ∑ i, T i j ^ 2 := by
  calc (∑ j ∈ s, T j j) ^ 2 ≤ s.card * ∑ j ∈ s, T j j ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ s.card * ∑ j ∈ s, ∑ i, T i j ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j _
      exact single_le_sum (f := fun i => T i j ^ 2) (fun i _ => sq_nonneg _) (mem_univ j)

end SteklovAudit.AbstractTransfer
