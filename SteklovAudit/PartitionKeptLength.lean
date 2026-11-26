import Mathlib
import SteklovAudit.PartitionProfile

/-!
# Kept edge length of the tetrahedral partition: the three pieces (roadmap item K7a)

Second step of the explicit partition of `∂T_a` (Josiah's construction, 2026-11-26), toward ledger
input H3 (edge length) of `MainConditional.lean`. Along an edge `0 ≤ z ≤ a` the edge cutoff is
`q_ε z = sin(β(z/ε)) · sin(β((a − z)/ε))` (`edgeCut`), for a profile `β` (`PartitionProfile.IsProfile`).
For `0 < ε` and `4ε ≤ a`:

* `edgeCut_mid`: `q_ε = 1` on `[2ε, a − 2ε]`;
* `edgeCut_sq_left`, `edgeCut_sq_right`: near each end only one factor is active;
* `end_integral`, `end_integral_right`: `∫₀^{2ε} sin(β(z/ε))² dz = ε/2` (substitution `z = ε t` and
  `∫₀² sin² β = 1/2`), and its reflection `z ↦ a − z`;
* `left_integral`, `mid_integral`, `right_integral`: the three pieces of `∫₀ᵃ q_ε²` equal
  `ε/2`, `a − 4ε`, `ε/2`; `edgeCut_continuous` for interval integrability.

Item K7b adds the pieces (`∫₀ᵃ q_ε² = a − 3ε`, total `6a − 18ε`, the H3 bound with `CL = 18`).

What this file does NOT prove: the sum of the pieces (K7b), the H3 field for the paper's adapted
radius `R_v` of (7.48), any statement about the Dirichlet-to-Neumann operator, H4–H6, or
Theorem 1.3 / 11.1. It is real analysis of explicit functions of one variable.
-/

namespace SteklovAudit.PartitionKeptLength

open Real SteklovAudit.PartitionProfile

/-- **K7a.** The edge cutoff `q_ε z = sin(β(z/ε)) sin(β((a − z)/ε))` along an edge of length `a`. -/
noncomputable def edgeCut (β : ℝ → ℝ) (ε a z : ℝ) : ℝ :=
  sin (β (z / ε)) * sin (β ((a - z) / ε))

/-- **K7a.** A profile has `sin β = 1` from `2` on. -/
theorem sin_profile_of_two_le (β : ℝ → ℝ) (h : IsProfile β) {t : ℝ} (ht : 2 ≤ t) :
    sin (β t) = 1 := by
  rw [h.2.1 t ht, sin_pi_div_two]

/-- **K7a.** `2ε ≤ u` gives `2 ≤ u / ε`. -/
theorem two_le_div {ε u : ℝ} (hε : 0 < ε) (hu : 2 * ε ≤ u) : 2 ≤ u / ε := by
  first
    | (rw [le_div_iff₀ hε]; linarith)
    | (rw [le_div_iff hε]; linarith)

/-- **K7a.** In the middle of the edge the cutoff is `1`. -/
theorem edgeCut_mid (β : ℝ → ℝ) (h : IsProfile β) {ε a z : ℝ} (hε : 0 < ε)
    (h1 : 2 * ε ≤ z) (h2 : z ≤ a - 2 * ε) : edgeCut β ε a z = 1 := by
  unfold edgeCut
  rw [sin_profile_of_two_le β h (two_le_div hε h1),
    sin_profile_of_two_le β h (two_le_div hε (by linarith)), mul_one]

/-- **K7a.** Near `z = 0` only the left factor is active. -/
theorem edgeCut_sq_left (β : ℝ → ℝ) (h : IsProfile β) {ε a z : ℝ} (hε : 0 < ε)
    (ha : 4 * ε ≤ a) (hz : z ≤ 2 * ε) : edgeCut β ε a z ^ 2 = sin (β (z / ε)) ^ 2 := by
  unfold edgeCut
  rw [sin_profile_of_two_le β h (two_le_div hε (by linarith)), mul_one]

/-- **K7a.** Near `z = a` only the right factor is active. -/
theorem edgeCut_sq_right (β : ℝ → ℝ) (h : IsProfile β) {ε a z : ℝ} (hε : 0 < ε)
    (ha : 4 * ε ≤ a) (hz : a - 2 * ε ≤ z) :
    edgeCut β ε a z ^ 2 = sin (β ((a - z) / ε)) ^ 2 := by
  unfold edgeCut
  rw [sin_profile_of_two_le β h (two_le_div hε (by linarith)), one_mul]

/-- **K7a.** The edge cutoff is continuous in `z` for a continuous profile. -/
theorem edgeCut_continuous (β : ℝ → ℝ) (hβ : Continuous β) (ε a : ℝ) :
    Continuous (fun z => edgeCut β ε a z ^ 2) := by
  show Continuous (fun z => (sin (β (z / ε)) * sin (β ((a - z) / ε))) ^ 2)
  first
    | fun_prop
    | exact ((continuous_sin.comp (hβ.comp (continuous_id.div_const ε))).mul
        (continuous_sin.comp (hβ.comp ((continuous_const.sub continuous_id).div_const ε)))).pow 2

/-- **K7a.** `∫₀^{2ε} sin(β(z/ε))² dz = ε/2`. -/
theorem end_integral (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {ε : ℝ} (hε : 0 < ε) :
    ∫ z in (0 : ℝ)..(2 * ε), sin (β (z / ε)) ^ 2 = ε / 2 := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hc : (∫ z in (0 : ℝ)..(2 * ε), sin (β (z / ε)) ^ 2) =
      ε • ∫ t in (0 : ℝ) / ε..(2 * ε) / ε, sin (β t) ^ 2 :=
    intervalIntegral.integral_comp_div (fun t => sin (β t) ^ 2) hε0
  have e2 : 2 * ε / ε = 2 := by rw [mul_div_assoc, div_self hε0, mul_one]
  rw [zero_div, e2, integral_sin_sq β hβ h, smul_eq_mul] at hc
  rw [hc]
  ring

/-- **K7a.** The reflected end: `∫_{a−2ε}^{a} sin(β((a − z)/ε))² dz = ε/2`. -/
theorem end_integral_right (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {ε a : ℝ}
    (hε : 0 < ε) : ∫ z in (a - 2 * ε)..a, sin (β ((a - z) / ε)) ^ 2 = ε / 2 := by
  have hc : (∫ z in (a - 2 * ε)..a, sin (β ((a - z) / ε)) ^ 2) =
      ∫ u in a - a..a - (a - 2 * ε), sin (β (u / ε)) ^ 2 :=
    intervalIntegral.integral_comp_sub_left (fun u => sin (β (u / ε)) ^ 2) a
  rw [hc, sub_self, sub_sub_cancel]
  exact end_integral β hβ h hε

/-- **K7a.** Left piece of `∫₀ᵃ q_ε²`. -/
theorem left_integral (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {ε a : ℝ}
    (hε : 0 < ε) (ha : 4 * ε ≤ a) : ∫ z in (0 : ℝ)..(2 * ε), edgeCut β ε a z ^ 2 = ε / 2 := by
  rw [← end_integral β hβ h hε]
  apply intervalIntegral.integral_congr
  intro z hz
  rw [Set.uIcc_of_le (by linarith)] at hz
  exact edgeCut_sq_left β h hε ha hz.2

/-- **K7a.** Middle piece of `∫₀ᵃ q_ε²`. -/
theorem mid_integral (β : ℝ → ℝ) (h : IsProfile β) {ε a : ℝ} (hε : 0 < ε) (ha : 4 * ε ≤ a) :
    ∫ z in (2 * ε)..(a - 2 * ε), edgeCut β ε a z ^ 2 = a - 4 * ε := by
  have e : ∫ z in (2 * ε)..(a - 2 * ε), edgeCut β ε a z ^ 2 =
      ∫ z in (2 * ε)..(a - 2 * ε), (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by linarith)] at hz
    show edgeCut β ε a z ^ 2 = 1
    rw [edgeCut_mid β h hε hz.1 hz.2, one_pow]
  rw [e]
  first
    | (rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring)
    | (simp; ring)

/-- **K7a.** Right piece of `∫₀ᵃ q_ε²`. -/
theorem right_integral (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {ε a : ℝ}
    (hε : 0 < ε) (ha : 4 * ε ≤ a) : ∫ z in (a - 2 * ε)..a, edgeCut β ε a z ^ 2 = ε / 2 := by
  rw [← end_integral_right β hβ h (a := a) hε]
  apply intervalIntegral.integral_congr
  intro z hz
  rw [Set.uIcc_of_le (by linarith)] at hz
  exact edgeCut_sq_right β h hε ha hz.1

end SteklovAudit.PartitionKeptLength
