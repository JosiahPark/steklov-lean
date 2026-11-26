import Mathlib
import SteklovAudit.WindowLittleOMass

/-!
# Localized mass `o(L²)` from a leading-order local Weyl law on shrinking collars (roadmap item H1)

Priority 1 of Josiah's 2026-11-26 review: obtain the weakened local-mass input of G158,
`m L = o(L²)`, without the sharper `O(L)` estimate. The proposed route: a LEADING-ORDER local
Weyl law for collars of each FIXED width, plus monotonicity of the localized mass in the collar,
already forces `o(L²)` for collars whose width shrinks to `0`.

`M v L` is the spectral mass up to frequency `L` localized to the collar of width `v`, and
`w L` is the collar width used at frequency `L`.

* `mass_littleO_of_local_weyl`: if `M` is monotone in the width, obeys the per-width upper bound
  `M v L ≤ (κ v + η) L²` eventually (one density constant `κ ≥ 0` for all widths) and `w L → 0⁺`,
  then `M (w L) L = o(L²)` in the `δ`-form used by G158.
* `window_littleO_of_local_weyl`: chained into `WindowLittleOMass.littleO_of_window_littleO_mass`.
* `uniform_density_needed`: the density must be uniform in the width. `M v L = L²` satisfies
  monotonicity and a per-width bound with constant `1 / v` (so `κ(v) · v = 1`), but is not `o(L²)`.

What this file does NOT prove: the local Weyl law `M v L ≤ (κ v + η) L²` for the tetrahedron's
Dirichlet-to-Neumann eigenfunctions (an explicit named hypothesis here), the monotonicity of the
actual localized mass (proved for finite spectral sums in a separate item, H2), the window bound
of G158 for the actual operator, (7.29), H5, or Theorem 1.3 / 11.1. This is a proposed research
direction made precise, not a result about the actual spectral data.
-/

namespace SteklovAudit.LocalMassShrinkingCollar

open Filter

/-- **H1.** Leading-order local Weyl law on fixed collars + monotonicity in the collar + shrinking
collars give localized mass `o(L²)`. -/
theorem mass_littleO_of_local_weyl (M : ℝ → ℝ → ℝ) (w : ℝ → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hmono : ∀ L : ℝ, 0 ≤ L → ∀ v₁ v₂ : ℝ, 0 < v₁ → v₁ ≤ v₂ → M v₁ L ≤ M v₂ L)
    (hweyl : ∀ v : ℝ, 0 < v → ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, M v L ≤ (κ * v + η) * L ^ 2)
    (hw : ∀ v : ℝ, 0 < v → ∀ᶠ L in atTop, 0 < w L ∧ w L ≤ v) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ L in atTop, M (w L) L ≤ δ * L ^ 2 := by
  intro δ hδ
  have hκ1 : (0 : ℝ) < 2 * (κ + 1) := by linarith
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = δ / (2 * (κ + 1)) := ⟨_, rfl⟩
  have hv : 0 < v := by rw [hvdef]; exact div_pos hδ hκ1
  have hvδ : v * (2 * (κ + 1)) = δ := by
    rw [hvdef]
    exact div_mul_cancel₀ _ (ne_of_gt hκ1)
  have hδe : δ = 2 * (κ * v) + 2 * v := by rw [← hvδ]; ring
  have hκv : κ * v + δ / 2 ≤ δ := by
    first
      | linarith
      | nlinarith
  filter_upwards [hweyl v hv (δ / 2) (by linarith), hw v hv, eventually_ge_atTop (0 : ℝ)]
    with L h1 h2 hL
  have hm : M (w L) L ≤ M v L := hmono L hL (w L) v h2.1 h2.2
  have hsq : (κ * v + δ / 2) * L ^ 2 ≤ δ * L ^ 2 :=
    mul_le_mul_of_nonneg_right hκv (sq_nonneg L)
  linarith

/-- **H1.** The local Weyl route feeds G158: with a window bound whose local mass is the
shrinking-collar mass, the remainder is `o(L)`. -/
theorem window_littleO_of_local_weyl (r : ℝ → ℝ) (M : ℝ → ℝ → ℝ) (w : ℝ → ℝ)
    (κ C K ε₀ : ℝ) (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hε₀ : 0 ≤ ε₀)
    (hm0 : ∀ᶠ L in atTop, 0 ≤ M (w L) L)
    (hmono : ∀ L : ℝ, 0 ≤ L → ∀ v₁ v₂ : ℝ, 0 < v₁ → v₁ ≤ v₂ → M v₁ L ≤ M v₂ L)
    (hweyl : ∀ v : ℝ, 0 < v → ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, M v L ≤ (κ * v + η) * L ^ 2)
    (hw : ∀ v : ℝ, 0 < v → ∀ᶠ L in atTop, 0 < w L ∧ w L ≤ v)
    (hr : ∀ T : ℝ, 0 < T → ∀ᶠ L in atTop,
      |r L| ≤ C * L / T + K * T * ε₀ * Real.sqrt (M (w L) L)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |r L| ≤ η * L :=
  SteklovAudit.WindowLittleOMass.littleO_of_window_littleO_mass r (fun L => M (w L) L) C K ε₀
    hC hK hε₀ hm0 (mass_littleO_of_local_weyl M w κ hκ hmono hweyl hw) hr

/-- **H1.** The density constant must be uniform in the width: `M v L = L²` is monotone in `v`
and obeys `M v L ≤ ((1 / v) * v + η) L²` for every fixed `v > 0`, yet it is not `o(L²)`. -/
theorem uniform_density_needed :
    (∀ L : ℝ, 0 ≤ L → ∀ v₁ v₂ : ℝ, 0 < v₁ → v₁ ≤ v₂ → L ^ 2 ≤ L ^ 2) ∧
    (∀ v : ℝ, 0 < v → ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, L ^ 2 ≤ ((1 / v) * v + η) * L ^ 2) ∧
    ¬ (∀ δ : ℝ, 0 < δ → ∀ᶠ L in atTop, L ^ 2 ≤ δ * L ^ 2) := by
  refine ⟨fun _ _ _ _ _ _ => le_rfl, fun v hv η hη => ?_, fun H => ?_⟩
  · filter_upwards with L
    have hv0 : v ≠ 0 := ne_of_gt hv
    have e : (1 / v) * v = 1 := by
      first
        | exact one_div_mul_cancel hv0
        | field_simp
    rw [e]
    nlinarith [sq_nonneg L, mul_nonneg hη.le (sq_nonneg L)]
  · obtain ⟨L, hL, hL1⟩ := ((H (1 / 2) (by norm_num)).and (eventually_ge_atTop (1 : ℝ))).exists
    nlinarith [sq_nonneg L]

end SteklovAudit.LocalMassShrinkingCollar
