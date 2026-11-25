import Mathlib
import SteklovAudit.WindowLocalMassBounded

/-!
# Window route with local mass `o(L²)` (roadmap item G158)

Row 3 of the priority table (abstract cumulative budget refinement). G146
(`WindowLocalMassBounded.littleO_of_window_bounded_defect`) shows that the window bound
`|r L| ≤ C L / T + K T ε₀ √(Mloc L)` with a BOUNDED defect `ε₀` gives `r = o(L)`. Here the local
spectral mass `Mloc L` is replaced by any `m L` with `m L = o(L²)`, which is strictly weaker than
`O(L)` (see G159). The conclusion is unchanged.

* `littleO_of_window_littleO_mass`: window bound with local mass `o(L²)` and bounded defect gives
  `r = o(L)` (`η`-form).
* `linear_mass_littleO_sq`: local mass `≤ Mloc L` is `o(L²)`.
* `window_bounded_defect_of_littleO`: G146's conclusion re-derived from the new theorem, so the new
  input is implied by the old one.

What this file does NOT prove: the local mass bound (neither `O(L)` nor `o(L²)`) for the actual
operator, the window bound for the localized tetrahedron–wedge error, the boundedness of the HS
defect (Lemma 7.1′ / (7.2)), Proposition 7.3, (7.29), H5, or Theorem 1.3 / 11.1. Everything here is
real analysis of scalar functions; every analytic input is an explicit hypothesis.
-/

namespace SteklovAudit.WindowLittleOMass

open Filter

/-- **G158.** Window bound with local mass `m L = o(L²)` and a bounded defect `ε₀`: if for every
window `T > 0`, eventually `|r L| ≤ C L / T + K T ε₀ √(m L)`, then `r = o(L)` (`η`-form). -/
theorem littleO_of_window_littleO_mass (r m : ℝ → ℝ) (C K ε₀ : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hε₀ : 0 ≤ ε₀) (_hm0 : ∀ᶠ L in atTop, 0 ≤ m L)
    (hm : ∀ δ : ℝ, 0 < δ → ∀ᶠ L in atTop, m L ≤ δ * L ^ 2)
    (hr : ∀ T : ℝ, 0 < T → ∀ᶠ L in atTop,
      |r L| ≤ C * L / T + K * T * ε₀ * Real.sqrt (m L)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L := by
  intro η hη
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 2 * (C + 1) / η := ⟨_, rfl⟩
  have hT : 0 < T := by rw [hTdef]; exact div_pos (by linarith) hη
  have hTη : T * η = 2 * (C + 1) := by
    rw [hTdef]
    exact div_mul_cancel₀ _ (ne_of_gt hη)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = K * T * ε₀ := ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [hAdef]; exact mul_nonneg (mul_nonneg hK hT.le) hε₀
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (η / 2) / (A + 1) := ⟨_, rfl⟩
  have hq : 0 < q := by rw [hqdef]; exact div_pos (by linarith) hA1
  have hqA : q * (A + 1) = η / 2 := by
    rw [hqdef]
    exact div_mul_cancel₀ _ (ne_of_gt hA1)
  filter_upwards [hr T hT, hm (q ^ 2) (pow_pos hq 2), eventually_ge_atTop (0 : ℝ)]
    with L h1 h3 hL
  -- first term
  have hb : η * L / 2 * T = L * (C + 1) := by
    rw [show η * L / 2 * T = L * (T * η) / 2 by ring, hTη]
    ring
  have t1 : C * L / T ≤ η * L / 2 := by
    have key : C * L ≤ η * L / 2 * T := by rw [hb]; nlinarith
    first
      | exact (div_le_iff₀ hT).2 key
      | exact (div_le_iff hT).2 key
  -- second term
  have hqL : 0 ≤ q * L := mul_nonneg hq.le hL
  have hmq : m L ≤ (q * L) ^ 2 := by
    have e : (q * L) ^ 2 = q ^ 2 * L ^ 2 := by ring
    rw [e]; exact h3
  have hs : Real.sqrt (m L) ≤ q * L := by
    calc Real.sqrt (m L) ≤ Real.sqrt ((q * L) ^ 2) := Real.sqrt_le_sqrt hmq
      _ = q * L := Real.sqrt_sq hqL
  have t2 : K * T * ε₀ * Real.sqrt (m L) ≤ η * L / 2 := by
    have s1 : K * T * ε₀ * Real.sqrt (m L) ≤ A * (q * L) := by
      rw [hAdef]; exact mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg hK hT.le) hε₀)
    have e1 : A * (q * L) + q * L = q * (A + 1) * L := by ring
    have e2 : q * (A + 1) * L = η * L / 2 := by rw [hqA]; ring
    linarith
  linarith

/-- **G158.** Local mass `≤ Mloc L` is `o(L²)`. -/
theorem linear_mass_littleO_sq {Mloc : ℝ} (_hM : 0 ≤ Mloc) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ L in atTop, Mloc * L ≤ δ * L ^ 2 := by
  intro δ hδ
  filter_upwards [eventually_ge_atTop (Mloc / δ), eventually_ge_atTop (0 : ℝ)] with L h1 h2
  have h3 : Mloc ≤ L * δ := by
    first
      | exact (div_le_iff₀ hδ).1 h1
      | exact (div_le_iff hδ).1 h1
  have h4 : Mloc * L ≤ L * δ * L := mul_le_mul_of_nonneg_right h3 h2
  have e : δ * L ^ 2 = L * δ * L := by ring
  linarith

/-- **G158.** G146's conclusion re-derived from `littleO_of_window_littleO_mass` with
`m L := Mloc * L`: the `o(L²)` input is implied by the `O(L)` input. -/
theorem window_bounded_defect_of_littleO (r : ℝ → ℝ) (C K ε₀ Mloc : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hε₀ : 0 ≤ ε₀) (hM : 0 ≤ Mloc)
    (hr : ∀ T : ℝ, 0 < T → ∀ᶠ L in atTop,
      |r L| ≤ C * L / T + K * T * ε₀ * Real.sqrt (Mloc * L)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L := by
  have hm0 : ∀ᶠ L in atTop, 0 ≤ (fun L : ℝ => Mloc * L) L := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact mul_nonneg hM hL
  exact littleO_of_window_littleO_mass r (fun L => Mloc * L) C K ε₀ hC hK hε₀ hm0
    (linear_mass_littleO_sq hM) hr

end SteklovAudit.WindowLittleOMass
