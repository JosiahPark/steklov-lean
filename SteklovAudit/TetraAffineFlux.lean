import Std

/-!
# Affine harmonic traces on the reference regular tetrahedron

The vertices are (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1). Each face is indexed
by the opposite vertex. Its scaled outward normal is minus that vertex. Products
of affine traces have degree at most two, so the three edge midpoints integrate
them exactly with equal weights on each face. The pairing below is twelve times
the normalized boundary integral. The accompanying note derives the quadrature
identity and the application to spectral projections of the actual DtN operator.

All identities are polynomial and use only the commutative-ring laws.

What this file does NOT prove: that the midpoint sums equal boundary integrals (exactness of the
midpoint rule for quadratics), the weak Green identity, the Dirichlet-to-Neumann operator or its
eigenbasis, Parseval for the four probes, the countable cutoff bound, or any of the open gaps
(7.2), (7.29), (7.38)/(7.45), (9.1) or Theorem 1.3 / 11.1. Those steps are paper arguments in
`docs/affine-dtn-cutoff.md`.
-/

namespace SteklovAudit.TetraAffineFlux

variable {R : Type} [Lean.Grind.CommRing R]

/-- Constant coefficient and the three coordinate coefficients of an affine trace. -/
structure Affine (R : Type) where
  c : R
  x : R
  y : R
  z : R

/-- Coefficient pairing for the linear parts. -/
def slopes (u v : Affine R) : R := u.x * v.x + u.y * v.y + u.z * v.z

/-- The midpoint rule on a triangle has the barycentric second-moment
coefficients (diagonal 2, off-diagonal 1) after clearing the denominator 12. -/
theorem face_midpoint_moments (a b c d e f : R) :
    (a+b)*(d+e) + (a+c)*(d+f) + (b+c)*(e+f) =
    (a+b+c)*(d+e+f) + (a*d+b*e+c*f) := by grind

/-- Pair on a face whose scaled outward normal has coordinates (a,b,c).
Its edge midpoints are (a,0,0), (0,b,0), (0,0,c). Each field receives the
normal and midpoint separately since the same edge lies on two faces. -/
def facePair (a b c : R) (f g : R → R → R → R → R → R → R) : R :=
  f a b c a 0 0 * g a b c a 0 0 +
  f a b c 0 b 0 * g a b c 0 b 0 +
  f a b c 0 0 c * g a b c 0 0 c

def boundaryPair (f g : R → R → R → R → R → R → R) : R :=
  facePair (-1) (-1) (-1) f g + facePair (-1) 1 1 f g +
  facePair 1 (-1) 1 f g + facePair 1 1 (-1) f g

def traceValue (u : Affine R) (_a _b _c x y z : R) : R :=
  u.c + u.x*x + u.y*y + u.z*z

/-- Square root of three times the outward normal derivative. -/
def scaledFlux (u : Affine R) (a b c _x _y _z : R) : R := u.x*a + u.y*b + u.z*c

/-- Affine compression of the scaled flux annihilates constants. -/
def compressed (u : Affine R) : Affine R := ⟨0, u.x, u.y, u.z⟩

def fluxResidual (u : Affine R) (a b c x y z : R) : R :=
  scaledFlux u a b c x y z - traceValue (compressed u) a b c x y z

theorem boundary_mass (u v : Affine R) :
    boundaryPair (traceValue u) (traceValue v) = 12 * u.c*v.c + 4 * slopes u v := by
  simp only [boundaryPair, facePair, traceValue, slopes]
  grind

theorem green_pair (u v : Affine R) :
    boundaryPair (scaledFlux u) (traceValue v) = 4 * slopes u v := by
  simp only [boundaryPair, facePair, scaledFlux, traceValue, slopes]
  grind

theorem residual_orthogonal (u v : Affine R) :
    boundaryPair (fluxResidual u) (traceValue v) = 0 := by
  simp only [boundaryPair, facePair, fluxResidual, scaledFlux, compressed, traceValue]
  grind

theorem residual_energy (u v : Affine R) :
    boundaryPair (fluxResidual u) (fluxResidual v) = 8 * slopes u v := by
  simp only [boundaryPair, facePair, fluxResidual, scaledFlux, compressed, traceValue, slopes]
  grind

open Std Lean.Grind

/-- Spectral tail estimate before passing to the infinite sum. Each pair is the
spectral gap and the squared overlap with one normalized affine probe. -/
theorem cutoff_tail_moment [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]
    (gap : R) (hg : 0 ≤ gap) (terms : List (R × R))
    (h : ∀ z ∈ terms, gap ≤ z.1 ∧ 0 ≤ z.2) :
    gap * (terms.map (fun z => z.1 * z.2)).sum ≤
      (terms.map (fun z => z.1 * z.1 * z.2)).sum := by
  induction terms with
  | nil => simp [Semiring.mul_zero]
  | cons z tail ih =>
    have hz := h z (by simp)
    have ht := ih (fun w hw => h w (by simp [hw]))
    have hzw : 0 ≤ z.1 * z.2 := OrderedRing.mul_nonneg (by grind) hz.2
    have hi := OrderedRing.mul_le_mul_of_nonneg_right hz.1 hzw
    simp only [List.map_cons, List.sum_cons]
    grind

end SteklovAudit.TetraAffineFlux
