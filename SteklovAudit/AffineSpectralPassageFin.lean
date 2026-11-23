import Mathlib
import SteklovAudit.AffineParsevalDischarge

/-!
# G143: the finite-dimensional spectral-theorem passage for `AffineOperatorPre`

`AffineParsevalDischarge.AffineOperatorPre` asks for a symmetric operator `A` on a domain `D`, a
Hilbert basis `b` of eigenvectors of `A` lying in `D`, eigenvalues `lam`, and four probes in `D`.
Here, for a FINITE-DIMENSIONAL real inner-product space `E` and a symmetric linear map
`T : E →ₗ[ℝ] E`, all of these fields are built from Mathlib's spectral theorem
(`LinearMap.IsSymmetric.eigenvectorBasis`, `LinearMap.IsSymmetric.eigenvalues`), with `D = ⊤`.
So in finite dimension the only remaining named hypothesis behind the G126 full-trace bound
`8 B / a²` is `BoundaryIdentification` (`full_trace_fin`, `full_trace_fin_sum`).

What this file does NOT prove: the tetrahedron's Dirichlet-to-Neumann operator is
infinite-dimensional, so nothing here discharges the Hilbert-basis hypothesis for it (that needs a
compact-resolvent spectral theorem for an unbounded self-adjoint operator, not formalized here);
it does not prove `BoundaryIdentification` for any operator (G144 only checks that it is
satisfiable); and it proves none of H1–H6, (7.2), (7.29), (7.38)/(7.45), (9.1) or
Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.AffineSpectralPassageFin

open SteklovAudit.TetraAffineFlux SteklovAudit.ResidualLink SteklovAudit.AffineCutoffTail
  SteklovAudit.AffineWitnessFromOperator SteklovAudit.AffineFullTrace
  SteklovAudit.AffineParsevalDischarge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {T : E →ₗ[ℝ] E}

/-- The `AffineOperatorPre` built from a symmetric operator on a finite-dimensional space:
domain `⊤`, the orthonormal eigenbasis of the spectral theorem as Hilbert basis. -/
noncomputable def preOfSymmetric (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (u : Fin 4 → E) : AffineOperatorPre E (Fin n) where
  D := ⊤
  A := T ∘ₗ (⊤ : Submodule ℝ E).subtype
  symm := by
    intro x y
    show inner ℝ (T (x : E)) (y : E) = inner ℝ (x : E) (T (y : E))
    exact hT _ _
  b := (hT.eigenvectorBasis hn).toHilbertBasis
  mem := fun _ => Submodule.mem_top
  lam := hT.eigenvalues hn
  eig := by
    intro i
    show T ((hT.eigenvectorBasis hn).toHilbertBasis i) =
      hT.eigenvalues hn i • (hT.eigenvectorBasis hn).toHilbertBasis i
    rw [OrthonormalBasis.coe_toHilbertBasis]
    first
      | exact hT.apply_eigenvectorBasis hn i
      | simpa using hT.apply_eigenvectorBasis hn i
  u := fun j => ⟨u j, Submodule.mem_top⟩

variable (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) (u : Fin 4 → E)

theorem preOfSymmetric_lam : (preOfSymmetric hT hn u).lam = hT.eigenvalues hn := rfl

theorem preOfSymmetric_A_apply (x : E) (hx : x ∈ (preOfSymmetric hT hn u).D) :
    (preOfSymmetric hT hn u).A ⟨x, hx⟩ = T x := rfl

theorem preOfSymmetric_u (j : Fin 4) : ((preOfSymmetric hT hn u).u j : E) = u j := rfl

theorem preOfSymmetric_b : ⇑(preOfSymmetric hT hn u).b = ⇑(hT.eigenvectorBasis hn) := by
  show ⇑(hT.eigenvectorBasis hn).toHilbertBasis = ⇑(hT.eigenvectorBasis hn)
  first
    | exact OrthonormalBasis.coe_toHilbertBasis _
    | simp

variable {a : ℝ}

/-- G126's full centered trace bound `8B/a²` in finite dimension: the only named hypothesis left
is `BoundaryIdentification`. -/
theorem full_trace_fin (ha : 0 < a) (I : BoundaryIdentification (preOfSymmetric hT hn u) a)
    (F F' : ℝ → ℝ) (B : ℝ) (hd : ∀ x, HasDerivAt F (F' x) x)
    (hL : ∀ x y, |F' x - F' y| ≤ B * |x - y|) :
    |∑' p : Fin n × Fin 4, (F (hT.eigenvalues hn p.1) - F (muVec a p.2)) *
        ovl (toData ha (preOfSymmetric hT hn u) I) p.1 p.2 ^ 2| ≤ 8 * B / a ^ 2 :=
  full_trace_discharged ha I F F' B hd hL

/-- The same bound with the (finite) sum written as a `Finset` sum. -/
theorem full_trace_fin_sum (ha : 0 < a) (I : BoundaryIdentification (preOfSymmetric hT hn u) a)
    (F F' : ℝ → ℝ) (B : ℝ) (hd : ∀ x, HasDerivAt F (F' x) x)
    (hL : ∀ x y, |F' x - F' y| ≤ B * |x - y|) :
    |∑ p : Fin n × Fin 4, (F (hT.eigenvalues hn p.1) - F (muVec a p.2)) *
        ovl (toData ha (preOfSymmetric hT hn u) I) p.1 p.2 ^ 2| ≤ 8 * B / a ^ 2 := by
  have h := full_trace_fin hT hn u ha I F F' B hd hL
  first
    | (rw [← tsum_fintype]; exact h)
    | simpa only [tsum_fintype] using h
    | simpa using h

end SteklovAudit.AffineSpectralPassageFin
