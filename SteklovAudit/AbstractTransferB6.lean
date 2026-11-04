import Mathlib
import SteklovAudit.AbstractTransfer

/-!
# Abstract transfer layer, step B6: band part of Lemma 5.1 in spectral coordinates

Window counting from band and off-band pieces. At a finite cutoff, let W be a set of window
eigenvalues of A (|a_i - L| ≤ w) and split the model eigenvalues b_j into a band and an
off-band part (b_j ≤ L/2 or b_j ≥ 2L). If every window row of J has unit mass (a named
hypothesis: J is isometric on the window), then
  #W ≤ (band mass of J on W) + 16 Ck² (1 + L + w)² / L²,
where Ck² (1 + L + w)² bounds the off-band defect on the window rows (Lemma 7.1', named).
The off-band entries are controlled through the spectral gap window_offband_gap, which is
the entrywise form of offband_window_bound.

What this file does NOT prove:
* It does not construct the Dirichlet-to-Neumann operator or the model operator; the
  eigenvalues and coefficients are arbitrary finite data.
* The unit row mass of J on the window (hrow) and the defect bound (hK) are hypotheses,
  not theorems; they stand for the paper's (2.2)/(5.5) and Lemma 7.1'.
* It does not count the band part itself (the model edge law), and it does not prove
  Lemma 5.1, (7.29) or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.AbstractTransfer

/-- B6, entrywise: a window eigenvalue a and an off-band model eigenvalue b satisfy
J² L² ≤ 16 ((a - b) J)². -/
theorem offband_entry_mul (a b L w J : ℝ) (hL : 0 < L) (hw : 4 * w ≤ L)
    (ha : |a - L| ≤ w) (hb : b ≤ L / 2 ∨ 2 * L ≤ b) :
    J ^ 2 * L ^ 2 ≤ 16 * ((a - b) * J) ^ 2 := by
  have g := window_offband_gap a b L w hL.le hw ha hb
  have h0 : 0 ≤ L / 4 := by linarith
  have hgg := mul_le_mul g g h0 (abs_nonneg (a - b))
  have hsq : L ^ 2 ≤ 16 * (a - b) ^ 2 := by
    nlinarith [sq_abs (a - b), abs_nonneg (a - b)]
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg J)
  nlinarith [hm]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- B6, off-band piece: on window rows, the off-band mass of J is at most
16 Ck² (1 + L + w)² / L², given the off-band defect bound hK (Lemma 7.1', named). -/
theorem offband_window_mass (D : Data ι κ) (band : κ → Prop) [DecidablePred band]
    (W : Finset ι) (L w Ck : ℝ) (hL : 0 < L) (hw : 4 * w ≤ L)
    (hW : ∀ i ∈ W, |D.a i - L| ≤ w)
    (hoff : ∀ j, ¬ band j → D.b j ≤ L / 2 ∨ 2 * L ≤ D.b j)
    (hK : ∑ i ∈ W, ∑ j, (if band j then 0 else D.K i j ^ 2) ≤ Ck ^ 2 * (1 + L + w) ^ 2) :
    ∑ i ∈ W, ∑ j, (if band j then 0 else D.J i j ^ 2)
      ≤ 16 * Ck ^ 2 * (1 + L + w) ^ 2 / L ^ 2 := by
  rw [le_div_iff₀ (pow_pos hL 2)]
  calc (∑ i ∈ W, ∑ j, (if band j then 0 else D.J i j ^ 2)) * L ^ 2
      = ∑ i ∈ W, ∑ j, (if band j then 0 else D.J i j ^ 2 * L ^ 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        split_ifs <;> ring
    _ ≤ ∑ i ∈ W, ∑ j, (if band j then 0 else 16 * D.K i j ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j _
        by_cases hb : band j
        · simp [hb]
        · rw [if_neg hb, if_neg hb]
          unfold Data.K
          exact offband_entry_mul (D.a i) (D.b j) L w (D.J i j) hL hw (hW i hi) (hoff j hb)
    _ = 16 * ∑ i ∈ W, ∑ j, (if band j then 0 else D.K i j ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        split_ifs <;> ring
    _ ≤ 16 * (Ck ^ 2 * (1 + L + w) ^ 2) := mul_le_mul_of_nonneg_left hK (by norm_num)
    _ = 16 * Ck ^ 2 * (1 + L + w) ^ 2 := by ring

/-- B6. Window counting from band and off-band pieces: if J has unit mass on every window
row (named hypothesis hrow), the number of window eigenvalues is at most the band mass
plus the O(1) off-band term 16 Ck² (1 + L + w)² / L². -/
theorem window_count_band (D : Data ι κ) (band : κ → Prop) [DecidablePred band]
    (W : Finset ι) (L w Ck : ℝ) (hL : 0 < L) (hw : 4 * w ≤ L)
    (hW : ∀ i ∈ W, |D.a i - L| ≤ w)
    (hoff : ∀ j, ¬ band j → D.b j ≤ L / 2 ∨ 2 * L ≤ D.b j)
    (hrow : ∀ i ∈ W, ∑ j, D.J i j ^ 2 = 1)
    (hK : ∑ i ∈ W, ∑ j, (if band j then 0 else D.K i j ^ 2) ≤ Ck ^ 2 * (1 + L + w) ^ 2) :
    (W.card : ℝ) ≤ ∑ i ∈ W, ∑ j, (if band j then D.J i j ^ 2 else 0)
      + 16 * Ck ^ 2 * (1 + L + w) ^ 2 / L ^ 2 := by
  have hcard : (W.card : ℝ) = ∑ i ∈ W, ∑ j, D.J i j ^ 2 := by
    rw [Finset.sum_congr rfl hrow]
    simp
  have hsplit : ∑ i ∈ W, ∑ j, D.J i j ^ 2 =
      ∑ i ∈ W, ∑ j, (if band j then D.J i j ^ 2 else 0) +
        ∑ i ∈ W, ∑ j, (if band j then 0 else D.J i j ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  have hoffm := offband_window_mass D band W L w Ck hL hw hW hoff hK
  linarith

end SteklovAudit.AbstractTransfer
