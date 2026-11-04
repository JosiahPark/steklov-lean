-- From hourly continuation 25 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
/-!
# Spectral gap leakage: elementary algebraic prerequisites

For diagonal self-adjoint A and B, K = BJ-JA has entries
Kᵢⱼ = (bᵢ-aⱼ) Jᵢⱼ. If a source window and target window
are separated by δ>0, the squared Hilbert--Schmidt mass
of the cross-window block J is at most δ⁻² times the squared
HS mass of the corresponding K block.

These scalar declarations do not certify the operator statement.
-/
namespace SteklovAudit

theorem spectral_gap_entry_identity (a b j : ℝ) :
    (b * j - j * a)^2 = (b - a)^2 * j^2 := by ring

theorem spectral_gap_entry_budget (a b j δ : ℝ)
    (hδ : 0 < δ) (hgap : δ ≤ |b - a|) :
    δ^2 * j^2 ≤ (b * j - j * a)^2 := by
  have hsq : δ^2 ≤ (b - a)^2 := by
    nlinarith [sq_nonneg (b - a), abs_nonneg (b - a), sq_abs (b - a)]
  rw [spectral_gap_entry_identity]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg j)

theorem spectral_gap_finite_budget (n : ℕ) (a b j : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hgap : ∀ i, δ ≤ |b i - a i|) :
    δ^2 * (∑ i, (j i)^2) ≤ ∑ i, (b i * j i - j i * a i)^2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => spectral_gap_entry_budget (a i) (b i) (j i) δ hδ (hgap i))

end SteklovAudit
