-- From hourly continuation 43 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib

namespace SteklovAudit

-- Scalar lemmas only; the matrix spectral-transfer theorem is NOT formalized here.
theorem square_gap_nonneg (x y : ℝ) : 0 ≤ (x - y)^2 := sq_nonneg _

theorem positive_gap_square (x y d : ℝ) (h : d ≤ x - y) (hd : 0 ≤ d) :
    d^2 ≤ (x-y)^2 := by
  nlinarith [sq_nonneg ((x-y)-d)]

-- For arbitrary finite self-adjoint A,B and J, the unformalized matrix theorem is:
-- ‖f(B) J - J f(A)‖_HS ≤ Lip(f) * ‖B J - J A‖_HS.
-- Its proof uses independent spectral bases and scalar Lipschitz bounds.
end SteklovAudit
