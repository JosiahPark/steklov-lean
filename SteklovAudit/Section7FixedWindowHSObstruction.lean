import Mathlib
/-!
A fixed-width *two-sided* spectral sandwich does not imply a uniform
Hilbert--Schmidt bound in dimension two. For the elliptic first-order
operator A = |D_x| + |D_y| on the flat 2-torus, the Fourier shift
J = exp(ix) and the projection onto eigenvalues L and L+1,
there are L orthogonal input modes (k,L-k), 1 <= k <= L,
whose outputs (k+1,L-k) remain in the projection and on which
[A,J] acts with coefficient 1.
These are arithmetic sublemmas only: the operator theorem is proved
separately in the accompanying audit and is NOT Lean-certified.
-/
namespace SteklovAudit

/-- L explicitly enumerated lattice modes on the positive diagonal. -/
theorem fixed_window_diagonal_count (L : ℕ) :
    (Finset.Icc 1 L).card = L := by
  simp

/-- Each positive-diagonal mode has input energy L and output energy L+1. -/
theorem fixed_window_shift_energies (L k : ℕ) (hk : k ≤ L) :
    k + (L - k) = L ∧ (k + 1) + (L - k) = L + 1 := by
  omega

/-- The exact squared defect on these L mutually orthogonal modes. -/
theorem fixed_window_hs_lower_budget (L : ℕ) :
    (∑ _k ∈ Finset.Icc 1 L, (1 : ℕ)) = L := by
  simp

/-- Consequently no energy-independent squared HS budget exists. -/
theorem fixed_window_no_uniform_hs_budget (C : ℕ) :
    ∃ L : ℕ, C < (∑ _k ∈ Finset.Icc 1 L, (1 : ℕ)) := by
  refine ⟨C + 1, ?_⟩
  simp

end SteklovAudit
