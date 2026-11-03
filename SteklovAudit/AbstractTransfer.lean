import Mathlib

/-!
# Abstract transfer layer, step B1: spectral coordinates at a finite cutoff

This module starts the "abstract operator layer" for the tetrahedral Steklov paper.
After truncating to finite spectral windows, the actual DtN operator `A` and the model
operator `B` are diagonal in orthonormal eigenbases, with eigenvalues `a i` and `b j`.
The identification `J` becomes a coefficient array `J i j`, and the intertwining defect
`K = A J - J B` has coefficients `(a i - b j) * J i j` (the spectral Sylvester identity).
Squared Hilbert–Schmidt norms are sums of squared coefficients.

Proved here, with no analytic input:
* Lipschitz functional calculus moves the defect entrywise (`transfer_entry`, `transfer_hs`);
* the localized trace comparison `Tr J* f(A) J - Tr f(B) J* J` is bounded by
  `Lip(f) * Σ |K i j| |J i j|` (`trace_transfer`);
* off-band coefficients are bounded by the defect over the spectral gap (`offband_hs`),
  which is the diagonal form of the paper's series (7.46), and gives the O(1) bound
  of Section 7.8 from the defect bound (`offband_window_bound`).

The paper's PDE estimates enter only through the named hypotheses in `PDEInputs`
(the localized spectral mass (2.2) and the uniform localized HS bound, Lemma 7.1').

What this module does NOT do:
* It does not construct any Dirichlet-to-Neumann operator. Eigenvalues and coefficients
  are arbitrary data.
* The model operator `B` has continuous spectrum. Here it is replaced by a finite
  discretization; passing to the limit is not formalized.
* `trace_transfer_naive` shows that Lipschitz transfer plus the PDE inputs only gives an
  O(L^2) trace comparison. The paper's (7.29) needs o(L); that requires the Duhamel time
  factor and the vanishing-tail hypothesis, which are later steps (see ROADMAP.md).
-/

namespace SteklovAudit.AbstractTransfer

/-- Spectral data at one finite cutoff: eigenvalues of `A` and `B`, and the coefficients
of the identification `J` in the two eigenbases. -/
structure Data (ι κ : Type*) where
  a : ι → ℝ
  b : κ → ℝ
  J : ι → κ → ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The intertwining defect `K = A J - J B` in spectral coordinates. -/
def Data.K (D : Data ι κ) (i : ι) (j : κ) : ℝ := (D.a i - D.b j) * D.J i j

/-- Squared Hilbert–Schmidt norm of a coefficient array. -/
def hs2 (M : ι → κ → ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

theorem hs2_nonneg (M : ι → κ → ℝ) : 0 ≤ hs2 M :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (M i j)))

/-- Lipschitz functional calculus moves the defect entrywise:
`|(f(a) - f(b)) J| ≤ Lip(f) |K|`. -/
theorem transfer_entry (D : Data ι κ) (f : ℝ → ℝ) (Lf : ℝ)
    (hf : ∀ x y, |f x - f y| ≤ Lf * |x - y|) (i : ι) (j : κ) :
    |(f (D.a i) - f (D.b j)) * D.J i j| ≤ Lf * |D.K i j| := by
  unfold Data.K
  rw [abs_mul, abs_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hf _ _) (abs_nonneg _)

/-- Hilbert–Schmidt form: `‖f(A) J - J f(B)‖²_HS ≤ Lip(f)² ‖K‖²_HS`. -/
theorem transfer_hs (D : Data ι κ) (f : ℝ → ℝ) (Lf : ℝ)
    (hf : ∀ x y, |f x - f y| ≤ Lf * |x - y|) :
    hs2 (fun i j => (f (D.a i) - f (D.b j)) * D.J i j) ≤ Lf ^ 2 * hs2 D.K := by
  unfold hs2
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := transfer_entry D f Lf hf i j
  have h0 : 0 ≤ |(f (D.a i) - f (D.b j)) * D.J i j| := abs_nonneg _
  have hsq : |(f (D.a i) - f (D.b j)) * D.J i j| ^ 2 ≤ (Lf * |D.K i j|) ^ 2 := by
    nlinarith [h, h0]
  calc ((f (D.a i) - f (D.b j)) * D.J i j) ^ 2
      = |(f (D.a i) - f (D.b j)) * D.J i j| ^ 2 := (sq_abs _).symm
    _ ≤ (Lf * |D.K i j|) ^ 2 := hsq
    _ = Lf ^ 2 * D.K i j ^ 2 := by rw [mul_pow, sq_abs]

/-- Localized trace comparison in spectral coordinates:
`Tr J* f(A) J - Tr f(B) J* J = Σ (f(a i) - f(b j)) J i j²`, bounded by `Lip(f) Σ |K||J|`. -/
theorem trace_transfer (D : Data ι κ) (f : ℝ → ℝ) (Lf : ℝ)
    (hf : ∀ x y, |f x - f y| ≤ Lf * |x - y|) :
    |∑ i, ∑ j, (f (D.a i) - f (D.b j)) * D.J i j ^ 2|
      ≤ Lf * ∑ i, ∑ j, |D.K i j| * |D.J i j| := by
  calc |∑ i, ∑ j, (f (D.a i) - f (D.b j)) * D.J i j ^ 2|
      ≤ ∑ i, |∑ j, (f (D.a i) - f (D.b j)) * D.J i j ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(f (D.a i) - f (D.b j)) * D.J i j ^ 2| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, Lf * (|D.K i j| * |D.J i j|) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have h := transfer_entry D f Lf hf i j
        have hJ : 0 ≤ |D.J i j| := abs_nonneg _
        calc |(f (D.a i) - f (D.b j)) * D.J i j ^ 2|
            = |(f (D.a i) - f (D.b j)) * D.J i j| * |D.J i j| := by
              rw [sq, ← mul_assoc, abs_mul]
          _ ≤ Lf * |D.K i j| * |D.J i j| := mul_le_mul_of_nonneg_right h hJ
          _ = Lf * (|D.K i j| * |D.J i j|) := by ring
    _ = Lf * ∑ i, ∑ j, |D.K i j| * |D.J i j| := by
        simp_rw [Finset.mul_sum]

/-- Off-band coefficients are controlled by the defect over the spectral gap:
if every pair is separated by `g > 0`, then `‖J‖²_HS ≤ ‖K‖²_HS / g²`. -/
theorem offband_hs (D : Data ι κ) (g : ℝ) (hg : 0 < g)
    (hgap : ∀ i j, g ≤ |D.a i - D.b j|) : hs2 D.J ≤ hs2 D.K / g ^ 2 := by
  have hg2 : 0 < g ^ 2 := by positivity
  rw [le_div_iff₀ hg2]
  unfold hs2
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have h := hgap i j
  have h1 : g ^ 2 ≤ (D.a i - D.b j) ^ 2 := by
    rw [← sq_abs (D.a i - D.b j)]
    nlinarith [h, hg]
  unfold Data.K
  calc D.J i j ^ 2 * g ^ 2 ≤ D.J i j ^ 2 * (D.a i - D.b j) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = ((D.a i - D.b j) * D.J i j) ^ 2 := by ring

/-- The spectral gap used in Section 7.8: a window eigenvalue `|a - L| ≤ w` and an
off-band model eigenvalue (`b ≤ L/2` or `b ≥ 2L`) are separated by at least `L/4`
once `4w ≤ L`. -/
theorem window_offband_gap (a b L w : ℝ) (hL : 0 ≤ L) (hw : 4 * w ≤ L)
    (ha : |a - L| ≤ w) (hb : b ≤ L / 2 ∨ 2 * L ≤ b) : L / 4 ≤ |a - b| := by
  rcases abs_le.mp ha with ⟨h1, h2⟩
  rcases hb with hb | hb
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonpos (by linarith)]
    linarith

/-- Diagonal form of the off-band bound in Section 7.8: if the window defect satisfies
Lemma 7.1' and all pairs are off-band, the off-band block is O(1) in HS norm
(squared bound `16 Ck² (1+L+w)² / L²`). -/
theorem offband_window_bound (D : Data ι κ) (L w Ck : ℝ) (hL : 0 < L)
    (hgap : ∀ i j, L / 4 ≤ |D.a i - D.b j|)
    (hK : hs2 D.K ≤ Ck ^ 2 * (1 + L + w) ^ 2) :
    hs2 D.J ≤ 16 * Ck ^ 2 * (1 + L + w) ^ 2 / L ^ 2 := by
  have hg : 0 < L / 4 := by linarith
  have h := offband_hs D (L / 4) hg hgap
  have hden : 0 < (L / 4) ^ 2 := by positivity
  calc hs2 D.J ≤ hs2 D.K / (L / 4) ^ 2 := h
    _ ≤ Ck ^ 2 * (1 + L + w) ^ 2 / (L / 4) ^ 2 := by
        gcongr
    _ = 16 * Ck ^ 2 * (1 + L + w) ^ 2 / L ^ 2 := by
        field_simp
        ring

/-- The paper's analytic inputs at one cutoff `L`, as named hypotheses.
Nothing here is proved in Lean: these are exactly the PDE estimates a referee must check.
* `mass`: the localized spectral mass bound (2.2) for the identification;
* `defect`: the uniform localized Hilbert–Schmidt bound, Lemma 7.1' (squared form). -/
structure PDEInputs (D : Data ι κ) (L Cm Ck : ℝ) : Prop where
  mass : hs2 D.J ≤ Cm * (1 + L) ^ 2
  defect : hs2 D.K ≤ Ck ^ 2 * (1 + L) ^ 2

/-- What Lipschitz transfer plus the PDE inputs give on their own: an O(L²) bound on the
localized trace comparison. The sharp law needs o(L), so this is the bound the
Duhamel time factor and the tail hypothesis must improve (ROADMAP steps B2–B4). -/
theorem trace_transfer_naive (D : Data ι κ) (f : ℝ → ℝ) (Lf L Cm Ck : ℝ) (hLf : 0 ≤ Lf)
    (hf : ∀ x y, |f x - f y| ≤ Lf * |x - y|) (H : PDEInputs D L Cm Ck) :
    |∑ i, ∑ j, (f (D.a i) - f (D.b j)) * D.J i j ^ 2|
      ≤ Lf * ((Ck ^ 2 + Cm) * (1 + L) ^ 2) / 2 := by
  have h1 := trace_transfer D f Lf hf
  have h2 : ∑ i, ∑ j, |D.K i j| * |D.J i j| ≤ (hs2 D.K + hs2 D.J) / 2 := by
    unfold hs2
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (|D.K i j| - |D.J i j|), sq_abs (D.K i j), sq_abs (D.J i j)]
  have e : (Ck ^ 2 + Cm) * (1 + L) ^ 2 = Ck ^ 2 * (1 + L) ^ 2 + Cm * (1 + L) ^ 2 := by ring
  have h3 : (hs2 D.K + hs2 D.J) / 2 ≤ ((Ck ^ 2 + Cm) * (1 + L) ^ 2) / 2 := by
    have hm := H.mass
    have hk := H.defect
    linarith
  calc |∑ i, ∑ j, (f (D.a i) - f (D.b j)) * D.J i j ^ 2|
      ≤ Lf * ∑ i, ∑ j, |D.K i j| * |D.J i j| := h1
    _ ≤ Lf * ((hs2 D.K + hs2 D.J) / 2) := mul_le_mul_of_nonneg_left h2 hLf
    _ ≤ Lf * (((Ck ^ 2 + Cm) * (1 + L) ^ 2) / 2) := mul_le_mul_of_nonneg_left h3 hLf
    _ = Lf * ((Ck ^ 2 + Cm) * (1 + L) ^ 2) / 2 := by ring

end SteklovAudit.AbstractTransfer
