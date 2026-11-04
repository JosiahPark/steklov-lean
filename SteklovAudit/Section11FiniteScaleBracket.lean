-- From hourly continuation 40 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
-- Continuation 40: scalar algebra only; not compiled at the time Lean 4 candidates.
-- Does not certify the spectral theorem or any tetrahedron-specific claim.
import Mathlib

namespace SteklovAudit

theorem quadratic_shift_plus (a b L h : ℝ) :
    (a * (L+h)^2 + b*(L+h)) - (a*L^2+b*L) =
      2*a*L*h + a*h^2 + b*h := by ring

theorem quadratic_shift_minus (a b L h : ℝ) :
    (a * (L-h)^2 + b*(L-h)) - (a*L^2+b*L) =
      -2*a*L*h + a*h^2 - b*h := by ring

theorem alternating_pair_identity (A c k s : ℝ) (hs : s*s=1) :
    ((A*k^2+c*k*s)+(A*(k+1)^2-c*(k+1)*s))/2 =
      A*(k+1/2)^2+A/4-c*s/2 := by
  ring

end SteklovAudit
