-- From hourly continuation 27 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
/-!
# Section 9: near-resonant defect obstruction and exact finite matrix decomposition

For diagonal self-adjoint A,B, the defect K = BJ-JA has entries
Kᵢⱼ=(bᵢ-aⱼ)Jᵢⱼ. Spectrally separated entries admit a gap estimate,
while resonant entries cannot be controlled by K alone. These scalar
results do not establish tetrahedral microlocal propagation.
-/
namespace SteklovAudit

theorem resonant_defect_identity (a b j : ℝ) :
    b * j - j * a = (b-a)*j := by ring

theorem exact_resonance_zero_defect (a j : ℝ) :
    a * j - j * a = 0 := by ring

theorem small_gap_unit_identification (ε : ℝ) :
    ε * (1:ℝ) - (1:ℝ) * 0 = ε := by ring

theorem resonant_entry_decomposition (a b j : ℝ) :
    (b * j - j * a)^2 = (b-a)^2*j^2 := by ring

-- Scalar budget for a near-resonant block; note the direction: a small
-- gap only bounds the defect ABOVE, not the identification BELOW.
theorem near_resonance_upper_defect (a b j η : ℝ)
    (hη : 0 ≤ η) (hgap : |b-a| ≤ η) :
    (b*j-j*a)^2 ≤ η^2*j^2 := by
  rw [resonant_entry_decomposition]
  have hsq : (b-a)^2 ≤ η^2 := by
    nlinarith [abs_nonneg (b-a), sq_abs (b-a)]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg j)

end SteklovAudit
