import Mathlib
import SteklovAudit

/-!
# E6: asymptotic counting transfer (continuations 33/34), abstract-scale form

Roadmap item E6. `SpectralCounting.counting_two_sided` (E1) gives, at each finite cutoff and each
shift `δ > 0`, `N_B(L) ≤ N_A(L + δ) + E + δ⁻² ‖K P‖²_HS` and the same with `A`, `B` exchanged. Here
the two inequalities are taken as hypotheses `hup`, `hdown` for a scale `δ = δ(L)` (with
`G(L)` the HS term `δ⁻² ‖K P‖²_HS` at that scale and `E(L)` the isometry defect), and proved:

* `poly_shift`: `|P(L + s) − P(L)| ≤ (3|A| + |B|) · L · |s|` for `L ≥ 1`, `|s| ≤ 1`, where
  `P = realWeylPolynomial A B`;
* `sharp_law_transfer`: if `N_A = A L² + B L + o(L)`, `δ(L) → 0` with `0 < δ ≤ 1`, and
  `E = o(L)`, `G = o(L)`, then `N_B = A L² + B L + o(L)`.

`hdown` is the second half of `counting_two_sided` applied at threshold `L − δ(L)`; `E` and `G`
must bound the defects there as well.

What this file does NOT prove: the choice `δ = L^(−β)`, `0 < β < (1 − α)/2`, which makes
`G = δ⁻² O(L^α) = o(L)` (roadmap E8); that the tetrahedral data satisfy any of these hypotheses;
or the main theorem.
-/

namespace SteklovAudit.SharpLawTransfer

open SteklovAudit

/-- Shifting the comparison polynomial by `s` costs `(3|A| + |B|) L |s|`. -/
theorem poly_shift (A B L s : ℝ) (hL : 1 ≤ L) (hs : |s| ≤ 1) :
    |realWeylPolynomial A B (L + s) - realWeylPolynomial A B L| ≤ (3 * |A| + |B|) * L * |s| := by
  have e : realWeylPolynomial A B (L + s) - realWeylPolynomial A B L =
      s * (A * (2 * L + s) + B) := by
    unfold realWeylPolynomial
    ring
  rw [e, abs_mul]
  have h0 : |2 * L + s| ≤ 2 * L + |s| := by
    calc |2 * L + s| ≤ |2 * L| + |s| := abs_add_le _ _
      _ = 2 * L + |s| := by rw [abs_of_nonneg (by linarith)]
  have h1 : |A * (2 * L + s) + B| ≤ |A| * (2 * L + |s|) + |B| := by
    calc |A * (2 * L + s) + B| ≤ |A * (2 * L + s)| + |B| := abs_add_le _ _
      _ = |A| * |2 * L + s| + |B| := by rw [abs_mul]
      _ ≤ |A| * (2 * L + |s|) + |B| :=
          add_le_add_right (mul_le_mul_of_nonneg_left h0 (abs_nonneg A)) _
  have h2 : |A| * (2 * L + |s|) + |B| ≤ (3 * |A| + |B|) * L := by
    have ha := mul_le_mul_of_nonneg_left (show |s| ≤ L by linarith) (abs_nonneg A)
    have hb := mul_le_mul_of_nonneg_left hL (abs_nonneg B)
    nlinarith [abs_nonneg A, abs_nonneg B]
  calc |s| * |A * (2 * L + s) + B| ≤ |s| * ((3 * |A| + |B|) * L) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg s)
    _ = (3 * |A| + |B|) * L * |s| := by ring

/-- E6. Sharp-law transfer at an abstract scale `δ(L) → 0`. -/
theorem sharp_law_transfer (NA NB E G δ : ℝ → ℝ) (A B : ℝ)
    (hA : HasSharpRealLaw NA A B)
    (hδpos : ∀ L, 1 ≤ L → 0 < δ L) (hδle : ∀ L, 1 ≤ L → δ L ≤ 1)
    (hδo : ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → δ L ≤ η)
    (hE : ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |E L| ≤ η * L)
    (hG : ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |G L| ≤ η * L)
    (hup : ∀ L, 1 ≤ L → NB L ≤ NA (L + δ L) + E L + G L)
    (hdown : ∀ L, 1 ≤ L → NA (L - δ L) ≤ NB L + E L + G L) :
    HasSharpRealLaw NB A B := by
  intro ε hε
  have hM0 : 0 ≤ 3 * |A| + |B| := by positivity
  have hM1 : 0 < 3 * |A| + |B| + 1 := by linarith
  obtain ⟨L1, _, h1⟩ := hA (ε / 8) (by positivity)
  obtain ⟨L2, h2⟩ := hE (ε / 8) (by positivity)
  obtain ⟨L3, h3⟩ := hG (ε / 8) (by positivity)
  obtain ⟨L4, h4⟩ := hδo (ε / (8 * (3 * |A| + |B| + 1))) (by positivity)
  refine ⟨max (max (L1 + 1) L2) (max L3 (max L4 1)),
    le_trans zero_le_one (le_trans (le_max_right L4 1)
      (le_trans (le_max_right L3 _) (le_max_right _ _))), ?_⟩
  intro L hL
  have hLa : L1 + 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLb : L2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLc : L3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLd : L4 ≤ L :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hL
  have hL1 : 1 ≤ L :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hL
  have hd0 := hδpos L hL1
  have hd1 := hδle L hL1
  have hd := h4 L hLd
  have hp := h1 (L + δ L) (by linarith)
  have hm := h1 (L - δ L) (by linarith)
  have he := h2 L hLb
  have hg := h3 L hLc
  have hu := hup L hL1
  have hw := hdown L hL1
  have sp := poly_shift A B L (δ L) hL1 (by rw [abs_of_pos hd0]; exact hd1)
  have sm := poly_shift A B L (-δ L) hL1 (by rw [abs_neg, abs_of_pos hd0]; exact hd1)
  rw [abs_of_pos hd0] at sp
  rw [abs_neg, abs_of_pos hd0, ← sub_eq_add_neg] at sm
  have hMd : (3 * |A| + |B|) * L * δ L ≤ ε / 8 * L := by
    have hL0 : 0 ≤ L := by linarith
    calc (3 * |A| + |B|) * L * δ L ≤ (3 * |A| + |B| + 1) * L * δ L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hL0) hd0.le
      _ ≤ (3 * |A| + |B| + 1) * L * (ε / (8 * (3 * |A| + |B| + 1))) :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hM1.le hL0)
      _ = ε / 8 * L := by
          first | (field_simp; ring) | field_simp | (rw [mul_div_assoc']; field_simp; ring)
  have hεd : ε / 8 * δ L ≤ ε / 8 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hεd0 : 0 ≤ ε / 8 * δ L := mul_nonneg (by positivity) hd0.le
  have hεL : 0 ≤ ε * L := mul_nonneg hε.le (by linarith)
  rw [abs_le] at hp hm he hg sp sm
  rw [abs_le]
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hm1, hm2⟩ := hm
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨sp1, sp2⟩ := sp
  obtain ⟨sm1, sm2⟩ := sm
  constructor
  · linarith
  · linarith

end SteklovAudit.SharpLawTransfer
