import Mathlib
import SteklovAudit.AbstractTransfer
import SteklovAudit.AbstractTransferB2

/-!
# R4: multi-chart trace comparison (R21.2 in spectral coordinates)

At a finite cutoff, `A` is diagonal with eigenvalues `a i` (`i : ι`), and each chart `c : χ` has
spectral data `D c : Data ι κ` with the same `A`-eigenvalues (`hA`) and model eigenvalues
`(D c).b j`. The partition of unity `Σ_c J_cᵀ J_c = I` enters only through its diagonal
`Σ_c Σ_j (J_c i j)² = 1` for every `i` (`hP`), which it implies. Then

  `|Tr e^{itA} − Σ_c Tr(J_cᵀ e^{itB_c} J_c)| ≤ |t| · √(dim) · (Σ_c ‖K_c‖²_HS)^{1/2}`
                                                                 (`multichart_trace`),

with `Tr(J_cᵀ e^{itB_c} J_c) = Σ_i Σ_j e^{itb_j} (J_c i j)²` (`trB`). The proof is entrywise Duhamel
(`duhamel_entry`, B2) and one Cauchy–Schwarz step. `sharp_example_trace` and `sharp_example_hs2`
give the example `A = 0`, `B = I`, `J = I` on `Fin n`, one chart: the discrepancy is
`n · |1 − e^{it}|` and the bound is `n · |t|`, so the factor `√dim` cannot be dropped.

What this file does NOT prove:
* It constructs no Dirichlet-to-Neumann operator, no charts and no unitary groups; all
  eigenvalues and coefficients are arbitrary finite data.
* It gives no bound on any `‖K_c‖_HS` (Lemma 7.1' is not used or proved here).
* With `dim ~ L²` the bound is not o(L); it proves none of `[H1]`–`[H6]`, not (7.29), and not the
  main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.MultiChartTrace

open SteklovAudit.AbstractTransfer

variable {ι χ κ : Type*} [Fintype ι] [Fintype χ] [Fintype κ]

/-- `Tr e^{itA}` for `A` diagonal with eigenvalues `a`. -/
noncomputable def trA (a : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i, Complex.exp (Complex.I * ((t * a i : ℝ) : ℂ))

/-- `Σ_c Tr(J_cᵀ e^{itB_c} J_c)` in spectral coordinates. -/
noncomputable def trB (D : χ → Data ι κ) (t : ℝ) : ℂ :=
  ∑ c, ∑ i, ∑ j, Complex.exp (Complex.I * ((t * (D c).b j : ℝ) : ℂ)) * (((D c).J i j ^ 2 : ℝ) : ℂ)

theorem trA_eq (a : ι → ℝ) (D : χ → Data ι κ) (hP : ∀ i, ∑ c, ∑ j, (D c).J i j ^ 2 = 1) (t : ℝ) :
    trA a t = ∑ i, ∑ c, ∑ j, Complex.exp (Complex.I * ((t * a i : ℝ) : ℂ)) *
      (((D c).J i j ^ 2 : ℝ) : ℂ) := by
  unfold trA
  apply Finset.sum_congr rfl
  intro i _
  have h1 : (∑ c, ∑ j, (((D c).J i j ^ 2 : ℝ) : ℂ)) = 1 := by
    calc (∑ c, ∑ j, (((D c).J i j ^ 2 : ℝ) : ℂ)) = (((∑ c, ∑ j, (D c).J i j ^ 2 : ℝ)) : ℂ) := by
          first | (push_cast; done) | (push_cast; rfl) | simp [Complex.ofReal_sum]
      _ = 1 := by rw [hP i, Complex.ofReal_one]
  calc Complex.exp (Complex.I * ((t * a i : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((t * a i : ℝ) : ℂ)) * 1 := (mul_one _).symm
    _ = Complex.exp (Complex.I * ((t * a i : ℝ) : ℂ)) * ∑ c, ∑ j, (((D c).J i j ^ 2 : ℝ) : ℂ) := by
        rw [h1]
    _ = _ := by simp_rw [Finset.mul_sum]

/-- R4 (R21.2 in coordinates). -/
theorem multichart_trace (a : ι → ℝ) (D : χ → Data ι κ) (hA : ∀ c i, (D c).a i = a i)
    (hP : ∀ i, ∑ c, ∑ j, (D c).J i j ^ 2 = 1) (t : ℝ) :
    ‖trA a t - trB D t‖ ≤
      |t| * (Real.sqrt (Fintype.card ι : ℝ) * Real.sqrt (∑ c, hs2 (D c).K)) := by
  have hB : trB D t = ∑ i, ∑ c, ∑ j, Complex.exp (Complex.I * ((t * (D c).b j : ℝ) : ℂ)) *
      (((D c).J i j ^ 2 : ℝ) : ℂ) := by
    unfold trB; exact Finset.sum_comm
  have hdiff : trA a t - trB D t = ∑ i, ∑ c, ∑ j,
      (Complex.exp (Complex.I * ((t * a i : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * (D c).b j : ℝ) : ℂ))) * (((D c).J i j ^ 2 : ℝ) : ℂ) := by
    rw [trA_eq a D hP t, hB]
    simp only [sub_mul, Finset.sum_sub_distrib]
  have hent : ∀ i c j, ‖(Complex.exp (Complex.I * ((t * a i : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * (D c).b j : ℝ) : ℂ))) * (((D c).J i j ^ 2 : ℝ) : ℂ)‖
      ≤ |t| * (|(D c).K i j| * |(D c).J i j|) := by
    intro i c j
    have hd := duhamel_entry (D c) t i j
    rw [hA c i] at hd
    have hc : (((D c).J i j ^ 2 : ℝ) : ℂ) = ((D c).J i j : ℂ) * ((D c).J i j : ℂ) := by
      push_cast; ring
    have hn : ‖(((D c).J i j : ℝ) : ℂ)‖ = |(D c).J i j| := by simp
    rw [hc, ← mul_assoc, norm_mul, hn]
    calc _ ≤ (|t| * |(D c).K i j|) * |(D c).J i j| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      _ = |t| * (|(D c).K i j| * |(D c).J i j|) := by ring
  have h1 : ‖trA a t - trB D t‖ ≤ |t| * ∑ i, ∑ c, ∑ j, |(D c).K i j| * |(D c).J i j| := by
    rw [hdiff]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ => norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ =>
      Finset.sum_le_sum fun j _ => hent i c j) ?_
    apply le_of_eq
    simp only [Finset.mul_sum]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × χ × κ))
    (fun p => |(D p.2.1).K p.1 p.2.2|) (fun p => |(D p.2.1).J p.1 p.2.2|)
  simp only [Fintype.sum_prod_type, sq_abs] at cs
  have hJ : (∑ i, ∑ c, ∑ j, (D c).J i j ^ 2) = (Fintype.card ι : ℝ) := by
    first
      | simp only [hP, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      | simp [hP]
  have hK : (∑ i, ∑ c, ∑ j, (D c).K i j ^ 2) = ∑ c, hs2 (D c).K := by
    unfold hs2; exact Finset.sum_comm
  rw [hJ, hK] at cs
  have hT0 : 0 ≤ ∑ i, ∑ c, ∑ j, |(D c).K i j| * |(D c).J i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hT : ∑ i, ∑ c, ∑ j, |(D c).K i j| * |(D c).J i j| ≤
      Real.sqrt (Fintype.card ι : ℝ) * Real.sqrt (∑ c, hs2 (D c).K) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_sq hT0]
    apply Real.sqrt_le_sqrt
    calc _ ≤ (∑ c, hs2 (D c).K) * (Fintype.card ι : ℝ) := cs
      _ = _ := mul_comm _ _
  exact le_trans h1 (mul_le_mul_of_nonneg_left hT (abs_nonneg t))

/-! ## Sharpness: `A = 0`, `B = I`, `J = I` on `Fin n`, one chart -/

/-- The example's single chart. -/
def exD (n : ℕ) : Unit → Data (Fin n) (Fin n) :=
  fun _ => ⟨fun _ => 0, fun _ => 1, fun i j => if i = j then 1 else 0⟩

theorem ex_row {n : ℕ} (i : Fin n) : ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) ^ 2 = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ex_partition (n : ℕ) : ∀ i, ∑ c, ∑ j, (exD n c).J i j ^ 2 = 1 := by
  intro i
  show ∑ _c : Unit, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) ^ 2 = 1
  simp only [ex_row]
  simp

/-- Here `Σ_c ‖K_c‖²_HS = n`, so the bound of `multichart_trace` is `n · |t|`. -/
theorem sharp_example_hs2 (n : ℕ) : hs2 (exD n ()).K = n := by
  show ∑ i : Fin n, ∑ j : Fin n, ((0 - 1) * (if i = j then (1 : ℝ) else 0)) ^ 2 = n
  have h : ∀ i j : Fin n, ((0 - 1) * (if i = j then (1 : ℝ) else 0)) ^ 2 =
      (if i = j then (1 : ℝ) else 0) ^ 2 := by intro i j; ring
  simp only [h, ex_row]
  simp

/-- The discrepancy in the example is `n (1 − e^{it})`. -/
theorem sharp_example_trace (n : ℕ) (t : ℝ) :
    trA (fun _ : Fin n => (0 : ℝ)) t - trB (exD n) t =
      (n : ℂ) * (1 - Complex.exp (Complex.I * ((t * 1 : ℝ) : ℂ))) := by
  have hrow : ∀ i : Fin n, ∑ j : Fin n, Complex.exp (Complex.I * ((t * 1 : ℝ) : ℂ)) *
      (((if i = j then (1 : ℝ) else 0) ^ 2 : ℝ) : ℂ) =
        Complex.exp (Complex.I * ((t * 1 : ℝ) : ℂ)) := by
    intro i
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, ex_row i, Complex.ofReal_one, mul_one]
  show (∑ _i : Fin n, Complex.exp (Complex.I * ((t * 0 : ℝ) : ℂ))) -
      ∑ _c : Unit, ∑ i : Fin n, ∑ j : Fin n, Complex.exp (Complex.I * ((t * 1 : ℝ) : ℂ)) *
        (((if i = j then (1 : ℝ) else 0) ^ 2 : ℝ) : ℂ) =
      (n : ℂ) * (1 - Complex.exp (Complex.I * ((t * 1 : ℝ) : ℂ)))
  simp only [hrow]
  simp
  try ring

theorem sharp_example_norm (n : ℕ) (t : ℝ) :
    ‖trA (fun _ : Fin n => (0 : ℝ)) t - trB (exD n) t‖ =
      n * ‖1 - Complex.exp (Complex.I * ((t * 1 : ℝ) : ℂ))‖ := by
  rw [sharp_example_trace, norm_mul]
  simp

end SteklovAudit.MultiChartTrace
