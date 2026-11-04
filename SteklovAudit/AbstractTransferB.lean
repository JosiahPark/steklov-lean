import Mathlib
import SteklovAudit
import SteklovAudit.AbstractTransfer

/-!
# Abstract transfer layer, steps B2–B5: from the time factor to the sharp law

Continues `SteklovAudit.AbstractTransfer` (spectral coordinates at a finite cutoff).

* **B2 (Duhamel with the time factor).** The wave-group factors `cos(t·)` and `sin(t·)` are
  `|t|`-Lipschitz, so `‖cos(tA) J - J cos(tB)‖²_HS ≤ t² ‖K‖²_HS` (and likewise for `sin`).
* **B3 (energy splitting).** For any split of the spectral pairs into a set `p` and its
  complement, with separate Lipschitz-type bounds `Λ` and `λ` for the counting test function
  on the two parts, the localized trace comparison is at most
  `Λ ‖K_p‖ ‖J_p‖ + λ ‖K_¬p‖ ‖J_¬p‖` (Cauchy–Schwarz on each part).
* **B4 (cumulative transfer bound).** With named hypotheses for the high-energy defect tail
  `τ`, the localized masses and the low-energy defect, the comparison is at most
  `Λ √(τ · m_high) + λ √(κ² · m_low)`.
* **B5 (ordered limits).** If the bound has the form `A · σ(M) · (1 + L) + E(M, L)` with a
  vanishing tail `σ(M) → 0` and `E(M, L) = o(L)` for each fixed `M`, the comparison is `o(L)`;
  combined with a sharp law for the model it gives the sharp law for the actual count
  (via `SteklovAudit.sharp_count_of_smoothed_and_unsmoothing`).

What this module does NOT prove: it constructs no Dirichlet-to-Neumann operator or wave
group, works at a finite spectral cutoff (the continuous model spectrum is discretized and the
limit is not formalized), and takes every analytic estimate as an explicit hypothesis: the
Lipschitz-type bounds for the smoothed counting function, the vanishing high-energy tail of
the Hilbert–Schmidt defect, the localized spectral-mass bounds, and the low-energy estimate.
It does not prove (7.29) or Theorem 1.3 / 11.1; it proves that they follow from those inputs.
-/

namespace SteklovAudit.AbstractTransfer

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### B2: Duhamel with the time factor -/

/-- `x ↦ cos (t x)` is `|t|`-Lipschitz. -/
theorem cos_time_lipschitz (t x y : ℝ) :
    |Real.cos (t * x) - Real.cos (t * y)| ≤ |t| * |x - y| := by
  calc |Real.cos (t * x) - Real.cos (t * y)| ≤ |t * x - t * y| :=
        Real.abs_cos_sub_cos_le _ _
    _ = |t| * |x - y| := by rw [← mul_sub, abs_mul]

/-- `x ↦ sin (t x)` is `|t|`-Lipschitz. -/
theorem sin_time_lipschitz (t x y : ℝ) :
    |Real.sin (t * x) - Real.sin (t * y)| ≤ |t| * |x - y| := by
  calc |Real.sin (t * x) - Real.sin (t * y)| ≤ |t * x - t * y| :=
        Real.abs_sin_sub_sin_le _ _
    _ = |t| * |x - y| := by rw [← mul_sub, abs_mul]

/-- Duhamel with the time factor, cosine part: `‖cos(tA) J - J cos(tB)‖²_HS ≤ t² ‖K‖²_HS`. -/
theorem duhamel_cos_hs (D : Data ι κ) (t : ℝ) :
    hs2 (fun i j => (Real.cos (t * D.a i) - Real.cos (t * D.b j)) * D.J i j)
      ≤ |t| ^ 2 * hs2 D.K :=
  transfer_hs D (fun x => Real.cos (t * x)) |t| (fun x y => cos_time_lipschitz t x y)

/-- Duhamel with the time factor, sine part: `‖sin(tA) J - J sin(tB)‖²_HS ≤ t² ‖K‖²_HS`. -/
theorem duhamel_sin_hs (D : Data ι κ) (t : ℝ) :
    hs2 (fun i j => (Real.sin (t * D.a i) - Real.sin (t * D.b j)) * D.J i j)
      ≤ |t| ^ 2 * hs2 D.K :=
  transfer_hs D (fun x => Real.sin (t * x)) |t| (fun x y => sin_time_lipschitz t x y)

/-! ### B3: energy splitting with Cauchy–Schwarz -/

/-- Restriction of a coefficient array to the pairs satisfying `p`. -/
def mask (p : ι → κ → Prop) [∀ i j, Decidable (p i j)] (M : ι → κ → ℝ) : ι → κ → ℝ :=
  fun i j => if p i j then M i j else 0

/-- Cauchy–Schwarz for double sums. -/
theorem cs_double (x y : ι → κ → ℝ) :
    (∑ i, ∑ j, x i j * y i j) ^ 2 ≤ hs2 x * hs2 y := by
  unfold hs2
  rw [← Fintype.sum_prod_type' (fun a b => x a b * y a b),
    ← Fintype.sum_prod_type' (fun a b => x a b ^ 2),
    ← Fintype.sum_prod_type' (fun a b => y a b ^ 2)]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun q : ι × κ => x q.1 q.2)
    (fun q : ι × κ => y q.1 q.2)

/-- `Σ |x| |y| ≤ √(‖x‖²_HS ‖y‖²_HS)`. -/
theorem abs_pair_le_sqrt (x y : ι → κ → ℝ) :
    ∑ i, ∑ j, |x i j| * |y i j| ≤ Real.sqrt (hs2 x * hs2 y) := by
  apply Real.le_sqrt_of_sq_le
  have h := cs_double (fun i j => |x i j|) (fun i j => |y i j|)
  have ex : hs2 (fun i j => |x i j|) = hs2 x := by
    unfold hs2
    simp only [sq_abs]
  have ey : hs2 (fun i j => |y i j|) = hs2 y := by
    unfold hs2
    simp only [sq_abs]
  rw [ex, ey] at h
  exact h

/-- One term of the trace comparison, bounded by the defect. -/
theorem term_le (D : Data ι κ) (F : ℝ → ℝ) (c : ℝ) (i : ι) (j : κ)
    (h : |F (D.a i) - F (D.b j)| ≤ c * |D.a i - D.b j|) :
    |(F (D.a i) - F (D.b j)) * D.J i j ^ 2| ≤ c * (|D.K i j| * |D.J i j|) := by
  have e1 : |(F (D.a i) - F (D.b j)) * D.J i j ^ 2|
      = |F (D.a i) - F (D.b j)| * (|D.J i j| * |D.J i j|) := by
    rw [abs_mul, sq, abs_mul]
  have e2 : |D.K i j| = |D.a i - D.b j| * |D.J i j| := by
    unfold Data.K
    exact abs_mul _ _
  rw [e1, e2]
  have hJ : 0 ≤ |D.J i j| * |D.J i j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |F (D.a i) - F (D.b j)| * (|D.J i j| * |D.J i j|)
      ≤ c * |D.a i - D.b j| * (|D.J i j| * |D.J i j|) := mul_le_mul_of_nonneg_right h hJ
    _ = c * (|D.a i - D.b j| * |D.J i j| * |D.J i j|) := by ring

/-- B3. Energy splitting: separate Lipschitz-type bounds on `p` and on its complement. -/
theorem split_trace_bound (D : Data ι κ) (F : ℝ → ℝ) (p : ι → κ → Prop)
    [∀ i j, Decidable (p i j)] (Λ lam : ℝ)
    (hhi : ∀ i j, p i j → |F (D.a i) - F (D.b j)| ≤ Λ * |D.a i - D.b j|)
    (hlo : ∀ i j, ¬ p i j → |F (D.a i) - F (D.b j)| ≤ lam * |D.a i - D.b j|) :
    |∑ i, ∑ j, (F (D.a i) - F (D.b j)) * D.J i j ^ 2|
      ≤ Λ * ∑ i, ∑ j, |mask p D.K i j| * |mask p D.J i j|
        + lam * ∑ i, ∑ j, |mask (fun i j => ¬ p i j) D.K i j|
            * |mask (fun i j => ¬ p i j) D.J i j| := by
  calc |∑ i, ∑ j, (F (D.a i) - F (D.b j)) * D.J i j ^ 2|
      ≤ ∑ i, |∑ j, (F (D.a i) - F (D.b j)) * D.J i j ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(F (D.a i) - F (D.b j)) * D.J i j ^ 2| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (Λ * (|mask p D.K i j| * |mask p D.J i j|)
          + lam * (|mask (fun i j => ¬ p i j) D.K i j|
              * |mask (fun i j => ¬ p i j) D.J i j|)) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hp : p i j
        · have h := term_le D F Λ i j (hhi i j hp)
          simp only [mask, hp, not_true_eq_false, if_true, if_false, abs_zero, mul_zero,
            add_zero]
          exact h
        · have h := term_le D F lam i j (hlo i j hp)
          simp only [mask, hp, not_false_eq_true, if_true, if_false, abs_zero, mul_zero,
            zero_add]
          exact h
    _ = Λ * ∑ i, ∑ j, |mask p D.K i j| * |mask p D.J i j|
        + lam * ∑ i, ∑ j, |mask (fun i j => ¬ p i j) D.K i j|
            * |mask (fun i j => ¬ p i j) D.J i j| := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-! ### B4: the cumulative transfer bound from named inputs -/

/-- B4. Cumulative transfer bound. The hypotheses are the analytic inputs, by name:
* `hhi`, `hlo`: Lipschitz-type bounds for the smoothed counting test on the two parts
  (in the paper, `Λ = S‖ρ₁‖∞` overall and a rapidly decreasing constant away from `L`);
* `htail`: the high-energy tail of the Hilbert–Schmidt defect (vanishing as the split
  energy grows, by Lemma 7.1);
* `hmassHi`, `hmassLo`: localized spectral-mass bounds (2.2) on the two parts;
* `hdefLo`: the low-energy defect bound. -/
theorem cumulative_transfer_bound (D : Data ι κ) (F : ℝ → ℝ) (p : ι → κ → Prop)
    [∀ i j, Decidable (p i j)] (Λ lam τ mHi κ2 mLo : ℝ) (hΛ : 0 ≤ Λ) (hlam : 0 ≤ lam)
    (hhi : ∀ i j, p i j → |F (D.a i) - F (D.b j)| ≤ Λ * |D.a i - D.b j|)
    (hlo : ∀ i j, ¬ p i j → |F (D.a i) - F (D.b j)| ≤ lam * |D.a i - D.b j|)
    (htail : hs2 (mask p D.K) ≤ τ) (hmassHi : hs2 (mask p D.J) ≤ mHi)
    (hdefLo : hs2 (mask (fun i j => ¬ p i j) D.K) ≤ κ2)
    (hmassLo : hs2 (mask (fun i j => ¬ p i j) D.J) ≤ mLo) :
    |∑ i, ∑ j, (F (D.a i) - F (D.b j)) * D.J i j ^ 2|
      ≤ Λ * Real.sqrt (τ * mHi) + lam * Real.sqrt (κ2 * mLo) := by
  have hs := split_trace_bound D F p Λ lam hhi hlo
  have h1 := abs_pair_le_sqrt (mask p D.K) (mask p D.J)
  have h2 := abs_pair_le_sqrt (mask (fun i j => ¬ p i j) D.K)
    (mask (fun i j => ¬ p i j) D.J)
  have n1 := hs2_nonneg (mask p D.K)
  have n2 := hs2_nonneg (mask p D.J)
  have n3 := hs2_nonneg (mask (fun i j => ¬ p i j) D.K)
  have n4 := hs2_nonneg (mask (fun i j => ¬ p i j) D.J)
  have s1 : Real.sqrt (hs2 (mask p D.K) * hs2 (mask p D.J)) ≤ Real.sqrt (τ * mHi) :=
    Real.sqrt_le_sqrt (mul_le_mul htail hmassHi n2 (le_trans n1 htail))
  have s2 : Real.sqrt (hs2 (mask (fun i j => ¬ p i j) D.K)
        * hs2 (mask (fun i j => ¬ p i j) D.J)) ≤ Real.sqrt (κ2 * mLo) :=
    Real.sqrt_le_sqrt (mul_le_mul hdefLo hmassLo n4 (le_trans n3 hdefLo))
  have t1 := mul_le_mul_of_nonneg_left (le_trans h1 s1) hΛ
  have t2 := mul_le_mul_of_nonneg_left (le_trans h2 s2) hlam
  linarith

/-! ### B5: ordered limits give o(L), and the sharp law transfers -/

/-- B5. Ordered-limit step of (7.29): a bound of the form
`|Δ(L)| ≤ A σ(M) (1 + L) + E(M, L)` with a vanishing tail `σ` and, for each fixed `M`,
`E(M, L) = o(L)`, gives `Δ(L) = o(L)`. The split energy `M` is chosen first, then `L`. -/
theorem little_o_of_vanishing_tail (Δ : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A) (σ : ℝ → ℝ)
    (E : ℝ → ℝ → ℝ) (hσ : ∀ M, 0 ≤ σ M)
    (hbound : ∀ M L, 1 ≤ L → |Δ L| ≤ A * σ M * (1 + L) + E M L)
    (htail : ∀ ε, 0 < ε → ∃ M, σ M ≤ ε)
    (hlow : ∀ M ε, 0 < ε → ∃ L0, ∀ L, L0 ≤ L → E M L ≤ ε * L) :
    ∀ δ, 0 < δ → ∃ L0, ∀ L, L0 ≤ L → |Δ L| ≤ δ * L := by
  intro δ hδ
  have hA1 : 0 < A + 1 := by linarith
  obtain ⟨M, hM⟩ := htail (δ / (4 * (A + 1))) (by positivity)
  obtain ⟨L1, hL1⟩ := hlow M (δ / 4) (by positivity)
  refine ⟨max L1 1, fun L hL => ?_⟩
  have hL1' : L1 ≤ L := le_trans (le_max_left _ _) hL
  have hLone : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hb := hbound M L hLone
  have he := hL1 L hL1'
  have hσM := hσ M
  have h3 : (A + 1) * (δ / (4 * (A + 1))) = δ / 4 := by
    field_simp
    all_goals ring
  have h2 : (A + 1) * σ M ≤ (A + 1) * (δ / (4 * (A + 1))) :=
    mul_le_mul_of_nonneg_left hM hA1.le
  have hAs : A * σ M ≤ δ / 4 := by nlinarith
  have hprod : A * σ M * (1 + L) ≤ δ / 4 * (2 * L) :=
    mul_le_mul hAs (by linarith) (by linarith) (by linarith)
  nlinarith

/-- B5, conclusion: if the model count `NB` satisfies the sharp two-term law and the
cumulative comparison `NA - NB` is `o(L)`, then the actual count `NA` satisfies the same law. -/
theorem transfer_sharp_law (NA NB : ℝ → ℝ) (A B : ℝ) (hB : HasSharpRealLaw NB A B)
    (hΔ : ∀ δ, 0 < δ → ∃ L0, ∀ L, L0 ≤ L → |NA L - NB L| ≤ δ * L) :
    HasSharpRealLaw NA A B := by
  apply sharp_count_of_smoothed_and_unsmoothing NA NB A B hB
  intro δ hδ
  obtain ⟨L0, hL0⟩ := hΔ δ hδ
  refine ⟨max L0 0, le_max_right _ _, fun L hL => ?_⟩
  have h := hL0 L (le_trans (le_max_left _ _) hL)
  simpa [realWeylPolynomial] using h

end SteklovAudit.AbstractTransfer
