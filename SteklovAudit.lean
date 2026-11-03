import Mathlib

/-!
# SteklovAudit: all modules in one file

Each section below was a separate module (SteklovAudit/<Name>.lean). They were merged so the
project is a single Lean file. The section order follows the original imports.
-/


-- ======================================================================
-- SteklovAudit.Algebra
-- ======================================================================

/-!
# Elementary identities used in the tetrahedral Steklov manuscript

These are actual Lean proof *attempts*, not compiler-certified in this session:
Lean and mathlib are not installed in the execution environment.
No `sorry` or added axioms are used. They need compilation and audit.
The difficult analytic operator results are NOT proved by this file.
-/

namespace SteklovAudit

/-- An abstract tetrahedron has four faces in the combinatorial count. -/
theorem tetra_face_count : Nat.choose 4 3 = 4 := by
  norm_num

/-- Six pairwise distinct edges on four vertices. -/
theorem tetra_edge_count : Nat.choose 4 2 = 6 := by
  rfl

/-- The total area of four equilateral faces, given the standard one-face formula. -/
theorem tetra_surface_area (a : ℝ) :
    4 * (Real.sqrt 3 / 4 * a ^ 2) = Real.sqrt 3 * a ^ 2 := by
  ring

/-- The tetrahedral half-dihedral-angle identity, for an angle with cosine 1/3. -/
theorem tetra_half_angle_sin_sq (x : ℝ)
    (hcos : Real.cos (x + x) = (1 : ℝ) / 3) :
    Real.sin x ^ 2 = (1 : ℝ) / 3 := by
  rw [Real.cos_add] at hcos
  have hunit := Real.sin_sq_add_cos_sq x
  nlinarith

/-- The ordinary algebraic expansion behind a bounded spectral shift. -/
theorem bounded_shift_changes_linear_term (A B L d : ℝ) :
    (A * L ^ 2 + B * L) -
      (A * (L - d) ^ 2 + B * (L - d)) =
       2 * A * d * L - A * d ^ 2 + B * d := by
  ring

/-- First-order geometric and edge coefficients sum exactly. -/
theorem six_edge_contribution (a c : ℝ) :
    (6 * a) * c = 6 * a * c := by
  ring

/-- The two-scale exponents in Section 9.5 are strictly admissible. -/
theorem scale_rho_lt_half : (1 : ℚ) / 3 < 1 / 2 := by
  norm_num

theorem scale_sigma_lt_rho : (1 : ℚ) / 12 < 1 / 3 := by
  norm_num

theorem scale_dwell_exponent :
    (1 : ℚ) / 3 - 1 / 12 = 1 / 4 := by
  norm_num

theorem scale_collar_over_dwell_exponent :
    (1 : ℚ) / 3 - (1 / 3 - 1 / 12) = 1 / 12 := by
  norm_num

theorem scale_uncertainty_over_dwell_exponent :
    (1 : ℚ) - 1 / 3 - (1 / 3 - 1 / 12) = 5 / 12 := by
  norm_num

/-- Used in the coefficient trace formula: the exact hyperbolic subtraction identity. -/
theorem hyperbolic_subtraction (p a x : ℝ) :
    Real.sinh ((p - a) * x) =
      Real.sinh (p * x) * Real.cosh (a * x) -
      Real.cosh (p * x) * Real.sinh (a * x) := by
  rw [sub_mul, Real.sinh_sub]

/-- Equivalent expression for the wedge integrand away from a zero denominator. -/
theorem dihedral_integrand_algebra (p a x : ℝ)
    (hc : Real.cosh (p * x) ≠ 0)
    (hs : Real.sinh (a * x) ≠ 0) :
    Real.sinh ((p - a) * x) /
      (Real.cosh (p * x) * Real.sinh (a * x)) =
      (Real.sinh (p * x) / Real.cosh (p * x)) *
      (Real.cosh (a * x) / Real.sinh (a * x)) - 1 := by
  rw [hyperbolic_subtraction, div_mul_div_comm, eq_sub_iff_add_eq,
    div_add_one (mul_ne_zero hc hs)]
  congr 1
  ring

/-- The right-angle integrand reduces algebraically to the hyperbolic secant. -/
theorem right_angle_integrand (v : ℝ)
    (hc : Real.cosh (Real.pi * v) ≠ 0)
    (hs : Real.sinh ((Real.pi / 2) * v) ≠ 0) :
    Real.sinh ((Real.pi - Real.pi / 2) * v) /
      (Real.cosh (Real.pi * v) * Real.sinh ((Real.pi / 2) * v)) =
      1 / Real.cosh (Real.pi * v) := by
  have harg : (Real.pi - Real.pi / 2) * v = (Real.pi / 2) * v := by
    ring
  rw [harg, mul_comm (Real.cosh (Real.pi * v)), ← div_div, div_self hs]

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Geometry
-- ======================================================================

/-!
# Elementary rigidity behind the unfolded-ray nonreturn argument (Section 10)

These are proof candidates, not compiler-certified in this environment.
The result proved here is an algebraic ingredient: if a nontrivial planar
rotation fixes a vector, that vector is zero. This does NOT establish that
the tetrahedral billiard's return set has measure zero; the planar-development,
countability and measure-theoretic steps remain unformalized.
No sorry/axiom is used.
-/

namespace SteklovAudit

/-- A planar rotation with nonzero determinant of `(R-I)` fixes only zero.
    `c,s` can be cosine and sine, but the proof needs only the determinant. -/
theorem rotation_fixed_vector_zero
    (c s x y : ℝ)
    (hdet : 0 < (c - 1) ^ 2 + s ^ 2)
    (hx : c * x - s * y = x)
    (hy : s * x + c * y = y) :
    x = 0 ∧ y = 0 := by
  have h₁ : (c - 1) * x - s * y = 0 := by linarith
  have h₂ : s * x + (c - 1) * y = 0 := by linarith
  have hxid : ((c - 1) ^ 2 + s ^ 2) * x =
      (c - 1) * ((c - 1) * x - s * y) +
      s * (s * x + (c - 1) * y) := by ring
  have hyid : ((c - 1) ^ 2 + s ^ 2) * y =
      (c - 1) * (s * x + (c - 1) * y) -
      s * ((c - 1) * x - s * y) := by ring
  rw [h₁, h₂] at hxid hyid
  have hdet_ne : ((c - 1) ^ 2 + s ^ 2) ≠ 0 := ne_of_gt hdet
  constructor
  · exact (mul_eq_zero.mp (by simpa using hxid)).resolve_left hdet_ne
  · exact (mul_eq_zero.mp (by simpa using hyid)).resolve_left hdet_ne

/-- Reflection across the horizontal axis fixes exactly horizontal vectors. -/
theorem reflection_fixed_vector_axis (vx vy : ℝ)
    (h : -vy = vy) : vy = 0 := by
  linarith

/-- A positive-time return under a *pure translation* forces the direction to
    be parallel to the translation. This is the algebraic part of (10.1). -/
theorem translation_return (px py vx vy cx cy t : ℝ)
    (hx : px + t * vx = px + cx)
    (hy : py + t * vy = py + cy) :
    t * vx = cx ∧ t * vy = cy := by
  constructor <;> linarith

/-- The direction and the return displacement have vanishing determinant. -/
theorem translation_return_parallel (vx vy cx cy t : ℝ)
    (hx : t * vx = cx) (hy : t * vy = cy) :
    vx * cy - vy * cx = 0 := by
  rw [← hx, ← hy]
  ring

/-- For an affine reflection with horizontal axis, the fixed *velocity* is
    horizontal. This is necessary, not sufficient, for a periodic orbit. -/
theorem reflection_return_velocity (vx vy : ℝ)
    (h : (vx, -vy) = (vx, vy)) : vy = 0 := by
  have h' : -vy = vy := congrArg Prod.snd h
  linarith

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Tauberian
-- ======================================================================

/-!
# Exact algebra and ordered-limit reasoning used in Sections 7 and 11

No operator theory is formalized here. Theorems explicitly take spectral
estimates as hypotheses. This validates only the ensuing summation/logic,
provided the file passes a real Lean compiler run (NOT available here).
-/

namespace SteklovAudit

/-- The exact finite geometric series underlying the dyadic vertex summation. -/
theorem dyadic_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / 2 : ℚ) ^ j) =
      2 * (1 - (1 / 2 : ℚ) ^ n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- A finite dyadic family contributes at most twice the first scale. -/
theorem dyadic_sum_le_two (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / 2 : ℚ) ^ j) ≤ 2 := by
  rw [dyadic_sum]
  have hpow : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ n := by positivity
  linarith

/-- Bounded perturbations can change the second Weyl coefficient. -/
theorem bounded_shift_can_change_linear (A L d : ℝ) :
    A * L ^ 2 - A * (L - d) ^ 2 = 2 * A * d * L - A * d ^ 2 := by
  ring

/-- The exact squared partition identity underlying localized trace assembly.
Assuming the pointwise sum of weights squared is one, the total weight is
one, for every tested scalar quantity. -/
theorem squared_partition_scalar (n : ℕ) (w : Fin n → ℝ) (x : ℝ)
    (hw : ∑ i : Fin n, w i ^ 2 = 1) :
    (∑ i : Fin n, w i ^ 2 * x) = x := by
  rw [← Finset.sum_mul, hw]
  ring

/-- Abstract version of the essential *ordered* ε-then-γ conclusion.

An analytic theorem must independently establish the assumed bounds, with
one universal constant for epsilon and an epsilon-dependent collar constant.
No such analytic bounds are asserted or proved in Lean by this lemma.
-/
theorem ordered_two_scale_limit
    (err : ℕ → ℝ)
    (h : ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ D : ℝ, 0 ≤ D ∧
          ∀ γ : ℝ, 0 < γ →
            ∃ N : ℕ, ∀ n ≥ N, |err n| ≤ C * ε + D * γ) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, |err n| < δ := by
  rcases h with ⟨C, hC, h⟩
  intro δ hd
  have hCp : 0 < C + 1 := by linarith
  let ε : ℝ := δ / (4 * (C + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨D, hD, hDrest⟩ := h ε hε
  have hDp : 0 < D + 1 := by linarith
  let γ : ℝ := δ / (4 * (D + 1))
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  obtain ⟨N, hN⟩ := hDrest γ hγ
  have hεeq : (C + 1) * ε = δ / 4 := by
    dsimp [ε]
    field_simp [ne_of_gt hCp]
  have hγeq : (D + 1) * γ = δ / 4 := by
    dsimp [γ]
    field_simp [ne_of_gt hDp]
  refine ⟨N, ?_⟩
  intro n hn
  have hb := hN n hn
  have hCε : C * ε ≤ δ / 4 := by linarith
  have hDγ : D * γ ≤ δ / 4 := by linarith
  linarith

end SteklovAudit

-- ======================================================================
-- SteklovAudit.WindowArithmetic
-- ======================================================================

/-!
# Exact scalar bookkeeping for fixed-width spectral windows (Sections 7 and 11)

This module proves arithmetic lemmas for finite weighted spectral sums and
polynomial Weyl terms. It does NOT establish the model or actual-domain spectral
window bounds from the manuscript. Every such bound must be proved separately.
All proof scripts are UNCOMPILED candidates in the current environment.
-/

namespace SteklovAudit

/-- A two-term Weyl polynomial changes by an exactly computable amount over
    the symmetric spectral interval `[L-d,L+d]`. -/
theorem symmetric_weyl_window (A B L d : ℝ) :
    (A * (L + d) ^ 2 + B * (L + d)) -
      (A * (L - d) ^ 2 + B * (L - d)) =
      4 * A * L * d + 2 * B * d := by
  ring

/-- The interval-mass polynomial estimate used in the fixed-Schwartz-kernel
    Tauberian argument: widths and spectral positions must both be counted. -/
theorem interval_mass_polynomial (V L s : ℝ) :
    V * ((L + s) ^ 2 - L ^ 2) =
      V * (2 * L * s + s ^ 2) := by
  ring

/-- The triangle inequality for a single localized error, used after a
    squared spatial partition. The partition identity itself is in Tauberian. -/
theorem two_error_composition (a b A B : ℝ)
    (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a + b| ≤ A + B := by
  calc
    |a + b| ≤ |a| + |b| := abs_add_le a b
    _ ≤ A + B := add_le_add ha hb

/-- A fixed spectral offset can alter the linear coefficient, and the change
    is `2*A*d`, demonstrating why a bounded intertwiner is insufficient. -/
theorem linear_coefficient_under_shift (A B L d : ℝ) :
    A * (L - d) ^ 2 + B * (L - d) =
      A * L ^ 2 + (B - 2 * A * d) * L + (A * d ^ 2 - B * d) := by
  ring

/-- The unnormalized first Riesz coefficient follows by integrating the
    formal leading polynomial: an *algebraic* identity only. -/
theorem first_riesz_coefficients (A B L : ℝ) :
    (A / 3) * L ^ 3 + (B / 2) * L ^ 2 =
      A * L ^ 3 / 3 + B * L ^ 2 / 2 := by
  ring

/-- A normalized scalar error `O(epsilon) + O_epsilon(gamma)` can be made
    arbitrarily small. The analytic bounds are not hidden in this theorem. -/
theorem choose_scales
    (C D delta : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hd : 0 < delta) :
    ∃ eps gam : ℝ,
      0 < eps ∧ 0 < gam ∧ C * eps + D * gam < delta := by
  let eps : ℝ := delta / (4 * (C + 1))
  let gam : ℝ := delta / (4 * (D + 1))
  have hpC : 0 < C + 1 := by linarith
  have hpD : 0 < D + 1 := by linarith
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hgam : 0 < gam := by dsimp [gam]; positivity
  have heq1 : (C + 1) * eps = delta / 4 := by
    dsimp [eps]
    field_simp [ne_of_gt hpC]
  have heq2 : (D + 1) * gam = delta / 4 := by
    dsimp [gam]
    field_simp [ne_of_gt hpD]
  refine ⟨eps, gam, heps, hgam, ?_⟩
  have h1 : C * eps ≤ delta / 4 := by nlinarith
  have h2 : D * gam ≤ delta / 4 := by nlinarith
  linarith

end SteklovAudit

-- ======================================================================
-- SteklovAudit.FiniteWindowMass
-- ======================================================================

/-!
# A finite-positive-spectral-measure lemma for the fixed-smoothing argument

This module contains an abstract, finite version of the positive spectral
window summation that occurs in Sections 7, 8 and 11. It does NOT prove the
manuscript's continuous-spectrum/compact-domain spectral window estimates.
UNCOMPILED: no Lean toolchain or mathlib was available in this session.
-/

namespace SteklovAudit

/-- If every localized window has mass at most M, then summing against
an arbitrary nonnegative kernel has mass bounded by M times its sum.
This is the positive-measure core of a finite fixed-smoothing estimate. -/
theorem finite_mass_weight_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (mass kernel : ι → ℝ) (M : ℝ)
    (hmass : ∀ i ∈ s, mass i ≤ M)
    (hkernel : ∀ i ∈ s, 0 ≤ kernel i) :
    (∑ i ∈ s, mass i * kernel i) ≤ M * (∑ i ∈ s, kernel i) := by
  calc
    (∑ i ∈ s, mass i * kernel i) ≤
        (∑ i ∈ s, M * kernel i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (hmass i hi) (hkernel i hi)
    _ = M * (∑ i ∈ s, kernel i) := by
      simp only [Finset.mul_sum]

/-- The exact scalar decomposition of an interval-mass upper bound.
The first term is O(V L +1); the second is controlled by a Schwartz
kernel's first absolute moment. -/
theorem spectral_window_polynomial_decomposition
    (C V L d : ℝ) :
    C * (V * (L + d) + 1) = C * (V * L + 1) + C * V * d := by
  ring

end SteklovAudit

-- ======================================================================
-- SteklovAudit.WholeTheorem
-- ======================================================================

/-!
# Sharp Steklov counting law: *conditional* ordered-limit assembly

WARNING: This file is not a proof of Theorem 11.1 of the paper.
It proves a scalar two-scale limiting implication *if* the uniform analytic
inequalities in the manuscript hold. In particular, the hypotheses below
have NOT been established in Lean. They are explicit parameters, not axioms.

A true formalization also needs a definition of the Dirichlet-to-Neumann
operator and a proof that its counting function meets these hypotheses.
No such operator or counting function is defined in the current project.

This file is UNCOMPILED: Lean/mathlib are unavailable in the present runtime.
-/

namespace SteklovAudit

/-- The two-term polynomial in the counting law, at a strictly positive
    semiclassical spectral level `n+1`. -/
def twoTermPolynomial (A B : ℝ) (n : ℕ) : ℝ :=
  A * ((n : ℝ) + 1) ^ 2 + B * ((n : ℝ) + 1)

/-- A sequence has a second-order counting asymptotic along positive integer
    energies. The analytic result for every real L would be stronger. -/
def HasSharpTwoTermLawOnIntegers (N : ℕ → ℝ) (A B : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      |N n - twoTermPolynomial A B n| ≤ δ * ((n : ℝ) + 1)

/-- Exactly the missing uniform analytic two-scale bound for the WHOLE
    counting function, specialized to positive integer spectral levels.
    This is stated as a hypothesis, not supplied by the formalization. -/
def HasUniformTwoScaleBound (N : ℕ → ℝ) (A B : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ γ : ℝ, 0 < γ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀,
            |N n - twoTermPolynomial A B n| ≤
              (C * ε + D * γ) * ((n : ℝ) + 1)

/-- Formal final *deduction* used in Section 11. It does not prove its
    substantive spectral hypothesis. A genuine Lean certification of the
    paper would have to establish `HasUniformTwoScaleBound` for the
    Dirichlet-to-Neumann spectral counting function and to extend the
    integer-energy law to all real spectral parameters. -/
theorem sharp_integer_law_of_two_scale
    (N : ℕ → ℝ) (A B : ℝ)
    (h : HasUniformTwoScaleBound N A B) :
    HasSharpTwoTermLawOnIntegers N A B := by
  rcases h with ⟨C, hC, hBound⟩
  intro δ hδ
  have hCp : 0 < C + 1 := by linarith
  let ε : ℝ := δ / (4 * (C + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨D, hD, hOther⟩ := hBound ε hε
  have hDp : 0 < D + 1 := by linarith
  let γ : ℝ := δ / (4 * (D + 1))
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  obtain ⟨n₀, hn₀⟩ := hOther γ hγ
  have hεEq : (C + 1) * ε = δ / 4 := by
    dsimp [ε]
    field_simp [ne_of_gt hCp]
  have hγEq : (D + 1) * γ = δ / 4 := by
    dsimp [γ]
    field_simp [ne_of_gt hDp]
  have hCEps : C * ε ≤ δ / 4 := by
    have hεPos : 0 ≤ ε := le_of_lt hε
    nlinarith
  have hDGam : D * γ ≤ δ / 4 := by
    have hγPos : 0 ≤ γ := le_of_lt hγ
    nlinarith
  have hCoeff : C * ε + D * γ ≤ δ := by linarith
  refine ⟨n₀, ?_⟩
  intro n hn
  have hmain := hn₀ n hn
  have hpos : 0 ≤ ((n : ℝ) + 1) := by positivity
  exact le_trans hmain (mul_le_mul_of_nonneg_right hCoeff hpos)

end SteklovAudit

-- ======================================================================
-- SteklovAudit.RealAxisAssembly
-- ======================================================================

/-!
# The real-energy ordered-limit implication used in Theorem 11.1

IMPORTANT: This is a formalization ATTEMPT of the *logical final assembly*.
It does not prove the missing spectral hypotheses; the real-valued spectral
counting function and the Dirichlet-to-Neumann operator are not defined here.
In this environment Lean and mathlib could not be run: UNCOMPILED.

Unlike the earlier `WholeTheorem.lean`, this statement covers ALL real
frequencies, not just integer frequencies. The latter distinction is
mathematically essential for an o(L) second-term Weyl law.
-/

namespace SteklovAudit

/-- Two-term Weyl comparison polynomial at real spectral energy. -/
def realWeylPolynomial (A B L : ℝ) : ℝ := A * L ^ 2 + B * L

/-- Full-real-axis two-term law in explicit epsilon form, with L positive. -/
def HasSharpRealLaw (N : ℝ → ℝ) (A B : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, 0 ≤ L₀ ∧
    ∀ L : ℝ, L₀ ≤ L →
      |N L - realWeylPolynomial A B L| ≤ δ * L

/-- The precise scalar estimate that the analytic Sections 7--11 would
need to supply. C does not depend on epsilon. D may depend on epsilon.
The quantifier order is important. -/
def HasRealTwoScaleBound (N : ℝ → ℝ) (A B : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ γ : ℝ, 0 < γ →
          ∃ L₀ : ℝ, 0 ≤ L₀ ∧
            ∀ L : ℝ, L₀ ≤ L →
              |N L - realWeylPolynomial A B L| ≤ (C * ε + D * γ) * L

/-- Conditional assembly valid at every sufficiently large real energy.
NO source theorem currently establishes HasRealTwoScaleBound for Steklov. -/
theorem sharp_real_law_of_two_scale
    (N : ℝ → ℝ) (A B : ℝ)
    (h : HasRealTwoScaleBound N A B) :
    HasSharpRealLaw N A B := by
  rcases h with ⟨C, hC, hBound⟩
  intro δ hδ
  have hCp : 0 < C + 1 := by linarith
  let ε : ℝ := δ / (4 * (C + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨D, hD, hOther⟩ := hBound ε hε
  have hDp : 0 < D + 1 := by linarith
  let γ : ℝ := δ / (4 * (D + 1))
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  obtain ⟨L₀, hL₀, htail⟩ := hOther γ hγ
  have hεEq : (C + 1) * ε = δ / 4 := by
    dsimp [ε]
    field_simp [ne_of_gt hCp]
  have hγEq : (D + 1) * γ = δ / 4 := by
    dsimp [γ]
    field_simp [ne_of_gt hDp]
  have hCEps : C * ε ≤ δ / 4 := by
    have hεnonneg : 0 ≤ ε := le_of_lt hε
    nlinarith
  have hDGam : D * γ ≤ δ / 4 := by
    have hγnonneg : 0 ≤ γ := le_of_lt hγ
    nlinarith
  have hCoeff : C * ε + D * γ ≤ δ := by linarith
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL
  have hmain := htail L hL
  have hLnonneg : 0 ≤ L := le_trans hL₀ hL
  exact le_trans hmain (mul_le_mul_of_nonneg_right hCoeff hLnonneg)

/-- Algebraically, sampling an O(L²) function one unit apart creates an
O(L) change, not an o(L) change. Integer-only formal statements are
insufficient for the theorem over arbitrary real spectral energies. -/
theorem one_step_polynomial_change (A B n : ℝ) :
    realWeylPolynomial A B (n + 1) - realWeylPolynomial A B n =
      2 * A * n + A + B := by
  dsimp [realWeylPolynomial]
  ring

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section5Scaling
-- ======================================================================

/-!
# Section 5.1: local spectral-window scaling — abstract positive profile

This establishes the real-variable implication which the cone spectral argument
uses, provided the genuine analytic spectral diagonal supplies `H` and its
Lipschitz properties. This module DOES NOT construct a DtN operator or prove
that its spectral diagonal has these properties.

Uncompiled draft: neither Lean nor mathlib is available in this runtime.
-/

namespace SteklovAudit

/-- Per-unit-edge cumulative strip mass in normalized cone coordinates. -/
def scaledStripMass (H : ℝ → ℝ) (L γ : ℝ) : ℝ := L * H (L * γ)

/-- The Section 5 strip-window estimate follows from a nonnegative,
linearly bounded, Lipschitz integrated profile. The profile conditions are
precisely the analytic inputs to be proved for the wedge DtN operator. -/
theorem scaled_strip_window
    (H : ℝ → ℝ) (C γ L₁ L₂ : ℝ)
    (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hL₁ : 0 ≤ L₁) (hLL : L₁ ≤ L₂)
    (hHnonneg : 0 ≤ H (L₂ * γ))
    (hHbound : H (L₂ * γ) ≤ C * (L₂ * γ))
    (hHlip : H (L₂ * γ) - H (L₁ * γ) ≤ C * (L₂ * γ - L₁ * γ)) :
    scaledStripMass H L₂ γ - scaledStripMass H L₁ γ
      ≤ C * γ * (L₂ ^ 2 - L₁ ^ 2) := by
  unfold scaledStripMass
  have hL₂ : 0 ≤ L₂ := le_trans hL₁ hLL
  have hdiff : 0 ≤ L₂ - L₁ := sub_nonneg.mpr hLL
  have hA : (L₂ - L₁) * H (L₂ * γ) ≤
      (L₂ - L₁) * (C * (L₂ * γ)) :=
    mul_le_mul_of_nonneg_left hHbound hdiff
  have hB : L₁ * (H (L₂ * γ) - H (L₁ * γ)) ≤
      L₁ * (C * (L₂ * γ - L₁ * γ)) :=
    mul_le_mul_of_nonneg_left hHlip hL₁
  nlinarith [hA, hB]

/-- The elementary cone-volume window estimate in two boundary dimensions,
expressed for a nonnegative bounded unit-energy spectral density. -/
theorem cone_ball_window
    (H : ℝ → ℝ) (C r L₁ L₂ : ℝ)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hL₁ : 0 ≤ L₁)
    (hLL : L₁ ≤ L₂)
    (hLip : H (L₂ * r) - H (L₁ * r) ≤
      C * r ^ 2 * (L₂ ^ 2 - L₁ ^ 2)) :
    H (L₂ * r) - H (L₁ * r) ≤
      C * r ^ 2 * (L₂ ^ 2 - L₁ ^ 2) := hLip

/-- The exact calculation used to convert an energy window of width 2w
into O(w L V) volume at high energies. -/
theorem symmetric_band_width (L w : ℝ) :
    (L + w) ^ 2 - (L - w) ^ 2 = 4 * L * w := by
  ring

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7SpectralSums
-- ======================================================================

/-!
# A positive-trace finite window lemma behind Sections 7.4 and 11.1

No Fourier transform, infinite spectral measure, Dirichlet-to-Neumann map,
or Schwartz decay is formalized in this module. It proves the finite-window
inequality for nonnegative spectral masses and kernel weights, including
that the *kernel itself* need not be nonnegative (one applies absolute values).
-/

namespace SteklovAudit

/-- Signed test kernels are handled by absolute values because the underlying
localized spectral mass is positive. This is a finite-spectrum estimate. -/
theorem positive_mass_signed_kernel_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (mass kernel allowance : ι → ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hallow : ∀ i ∈ s, mass i ≤ allowance i) :
    |∑ i ∈ s, mass i * kernel i| ≤
       ∑ i ∈ s, allowance i * |kernel i| := by
  classical
  revert hmass hallow
  induction s using Finset.induction_on with
  | empty =>
      intro hmass hallow
      simp
  | @insert i s hi ih =>
      intro hmass hallow
      simp only [Finset.sum_insert hi]
      have hm : 0 ≤ mass i := hmass i (Finset.mem_insert_self i s)
      have ha : mass i ≤ allowance i := hallow i (Finset.mem_insert_self i s)
      have hsubm : ∀ j ∈ s, 0 ≤ mass j := by
        intro j hj
        exact hmass j (Finset.mem_insert_of_mem hj)
      have hsuba : ∀ j ∈ s, mass j ≤ allowance j := by
        intro j hj
        exact hallow j (Finset.mem_insert_of_mem hj)
      have ih' := ih hsubm hsuba
      have hp : |mass i * kernel i| ≤ allowance i * |kernel i| := by
        rw [abs_mul, abs_of_nonneg hm]
        exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      calc
        |mass i * kernel i + ∑ j ∈ s, mass j * kernel j|
          ≤ |mass i * kernel i| + |∑ j ∈ s, mass j * kernel j| :=
            abs_add_le _ _
        _ ≤ allowance i * |kernel i| +
            ∑ j ∈ s, allowance j * |kernel j| := add_le_add hp ih'

/-- The unit-window polynomial bound that becomes O(V L + 1) after
Schwartz-weighted summation over spectral windows. -/
theorem unit_window_linear_decomposition (C V L d : ℝ) :
    C * (V * (L + d) + 1) = C * (V * L + 1) + C * V * d := by
  ring

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section10FiniteDirections
-- ======================================================================

/-!
# Algebraic nonreturn: finite/countable direction constraints

Only affine Euclidean geometry is addressed. The crucial claim that all
trajectories of the actual DtN propagator follow the stated branching
relation is an independent analytic theorem (Section 9), not proved here.
-/

namespace SteklovAudit

/-- Return under pure translation forces a vector to be collinear with the
translation; this formulation needs no division by the return time. -/
theorem translation_velocity_collinear (t vx vy cx cy : ℝ)
    (hx : t * vx = cx) (hy : t * vy = cy) :
    vx * cy = vy * cx := by
  calc
    vx * cy = vx * (t * vy) := by rw [← hy]
    _ = vy * (t * vx) := by ring
    _ = vy * cx := by rw [hx]

/-- Nontrivial algebraic planar rotations have no nonzero fixed vectors.
The determinant condition can later be derived from the D6 point group. -/
theorem nontrivial_rotation_immobile
    (c s x y : ℝ)
    (hdet : ((c - 1) ^ 2 + s ^ 2) ≠ 0)
    (h₁ : (c - 1) * x - s * y = 0)
    (h₂ : s * x + (c - 1) * y = 0) :
    x = 0 ∧ y = 0 := by
  have hx : ((c - 1) ^ 2 + s ^ 2) * x = 0 := by
    calc
      ((c - 1) ^ 2 + s ^ 2) * x =
          (c - 1) * ((c - 1) * x - s * y) +
          s * (s * x + (c - 1) * y) := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  have hy : ((c - 1) ^ 2 + s ^ 2) * y = 0 := by
    calc
      ((c - 1) ^ 2 + s ^ 2) * y =
          (c - 1) * (s * x + (c - 1) * y) -
          s * ((c - 1) * x - s * y) := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  constructor
  · exact (mul_eq_zero.mp hx).resolve_left hdet
  · exact (mul_eq_zero.mp hy).resolve_left hdet

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section11Partition
-- ======================================================================

/-!
# Section 11: finite squared-partition and ordered real-frequency assembly

This is the scalar algebra behind the global spectral trace summation.
The trace identity and all localized spectral estimates are analytic inputs,
not consequences of this formalization. No Steklov eigenvalues are defined.
-/

namespace SteklovAudit

/-- Localization errors add at most their sum when only positivity of the
localized spectral weights is available. The statement is for finite systems
and does not assert the trace-class property of any operator. -/
theorem finite_partition_error
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (actual predicted bound : ι → ℝ)
    (h : ∀ i ∈ s, |actual i - predicted i| ≤ bound i) :
    |∑ i ∈ s, (actual i - predicted i)| ≤ ∑ i ∈ s, bound i := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro h
      simp
  | @insert i s hi ih =>
      intro h
      simp only [Finset.sum_insert hi]
      have hterm := h i (Finset.mem_insert_self i s)
      have hs : ∀ j ∈ s, |actual j - predicted j| ≤ bound j := by
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      have ih' := ih hs
      calc
        |(actual i - predicted i) + ∑ j ∈ s, (actual j - predicted j)|
            ≤ |actual i - predicted i| + |∑ j ∈ s, (actual j - predicted j)| :=
              abs_add_le _ _
        _ ≤ bound i + ∑ j ∈ s, bound j := add_le_add hterm ih'

/-- The geometric partition allows comparing the total area/edge prediction
with the sum of localized predictions without changing its coefficients. -/
theorem real_weyl_partition_identity
    {ι : Type*} [Fintype ι] (A B L : ℝ)
    (area edge : ι → ℝ)
    (harea : (∑ i, area i) = A)
    (hedge : (∑ i, edge i) = B) :
    (∑ i, (area i * L ^ 2 + edge i * L)) =
      A * L ^ 2 + B * L := by
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, harea, hedge]

/-- Full-real-axis asymptotic scale choices, with epsilon chosen before the
possibly epsilon-dependent gamma constant. A formalized version already
exists as `RealAxisAssembly.sharp_real_law_of_two_scale`. -/
theorem small_two_parameter_budget
    (C D δ : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hδ : 0 < δ) :
    ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ C * ε + D * γ < δ := by
  let ε := δ / (4 * (C + 1))
  let γ := δ / (4 * (D + 1))
  have hc : 0 < C + 1 := by linarith
  have hd : 0 < D + 1 := by linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨ε, γ, hε, hγ, ?_⟩
  have he : (C + 1) * ε = δ / 4 := by
    dsimp [ε]
    field_simp [ne_of_gt hc]
  have hg : (D + 1) * γ = δ / 4 := by
    dsimp [γ]
    field_simp [ne_of_gt hd]
  have he' : C * ε ≤ δ / 4 := by nlinarith
  have hg' : D * γ ≤ δ / 4 := by nlinarith
  linarith

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7SchwartzFinite
-- ======================================================================

/-!
# Section 11.1: finite Schwarz-weighted unit-window estimate

This proves an exact finite sum bound from positive window masses, with a
signed kernel and explicitly visible zeroth and first absolute moments.
Infinite summability and the passage from finite windows to the spectral
integral are NOT proved here.
-/

namespace SteklovAudit

/-- Precise finite-window summation: for a nonnegative spectral mass in
window `i` bounded by `C(V(L+dᵢ)+1)`, the total error is at most
`C (V L+1) ||κ||₁ + C V ∑ dᵢ |κᵢ|`.
All constants and nonnegative assumptions are explicit. -/
theorem finite_schwartz_window_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (mass kernel dist : ι → ℝ)
    (C V L : ℝ)
    (hC : 0 ≤ C) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdist : ∀ i ∈ s, 0 ≤ dist i)
    (hwin : ∀ i ∈ s, mass i ≤ C * (V * (L + dist i) + 1)) :
    |∑ i ∈ s, mass i * kernel i| ≤
      C * (V * L + 1) * (∑ i ∈ s, |kernel i|) +
      C * V * (∑ i ∈ s, dist i * |kernel i|) := by
  classical
  have hterm (i : ι) (hi : i ∈ s) :
      |mass i * kernel i| ≤
        C * (V * L + 1) * |kernel i| +
        C * V * (dist i * |kernel i|) := by
    have hm := hmass i hi
    have hw := hwin i hi
    have hp : 0 ≤ |kernel i| := abs_nonneg _
    have h := mul_le_mul_of_nonneg_right hw hp
    rw [abs_mul, abs_of_nonneg hm]
    nlinarith [h]
  have hsum : (∑ i ∈ s, |mass i * kernel i|) ≤
      ∑ i ∈ s, (C * (V * L + 1) * |kernel i| +
        C * V * (dist i * |kernel i|)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hterm i hi
  have htri : |∑ i ∈ s, mass i * kernel i| ≤
      ∑ i ∈ s, |mass i * kernel i| := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hmain := le_trans htri hsum
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hmain

end SteklovAudit

-- ======================================================================
-- SteklovAudit.SmoothedBridge
-- ======================================================================

/-!
# The logical bridge from a smoothed counting law and a sharp-minus-smoothed
# o(L) error to the unsmoothed two-term Steklov formula

This is genuinely the logical final step used by Section 11, at **all real
spectral parameters**. Both hard analytic inputs are explicit hypotheses.
It is not a theorem about an actual Dirichlet-to-Neumann operator until
those hypotheses are proved for one.
-/

namespace SteklovAudit

/-- Adding a real-energy o(L) error to an already sharp two-term law
preserves its coefficients. In the actual paper one would take `S` to be
the fixed-time smoothed counting function and `N` the unsmoothed count. -/
theorem sharp_count_of_smoothed_and_unsmoothing
    (N S : ℝ → ℝ) (A B : ℝ)
    (hsmoothed : HasSharpRealLaw S A B)
    (herror : HasSharpRealLaw (fun L => N L - S L) 0 0) :
    HasSharpRealLaw N A B := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨L₁, hL₁, hs⟩ := hsmoothed (δ / 2) hδ2
  obtain ⟨L₂, hL₂, he⟩ := herror (δ / 2) hδ2
  refine ⟨max L₁ L₂, le_trans hL₁ (le_max_left _ _), ?_⟩
  intro L hL
  have hsm := hs L (le_trans (le_max_left _ _) hL)
  have herr := he L (le_trans (le_max_right _ _) hL)
  simp only [realWeylPolynomial, mul_zero, zero_mul, add_zero, sub_zero] at herr
  have hid : N L - realWeylPolynomial A B L =
      (N L - S L) + (S L - realWeylPolynomial A B L) := by ring
  rw [hid]
  calc
    |(N L - S L) + (S L - realWeylPolynomial A B L)|
        ≤ |N L - S L| + |S L - realWeylPolynomial A B L| :=
          abs_add_le _ _
    _ ≤ (δ / 2) * L + (δ / 2) * L := add_le_add herr hsm
    _ = δ * L := by ring

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7ExplicitBarrier
-- ======================================================================

/-!
# Section 7: an explicit polynomial certificate for the tetrahedral cusp barrier

The proof goal is purely algebraic. It does NOT formalize the PDE maximum
principle, Dirichlet-to-Neumann operators, or the complete Steklov theorem.

Compilation status: UNCHECKED (Lean and mathlib not available in the runtime).
-/

namespace SteklovAudit

/-- The numerator governing the cylindrical Laplacian of the candidate barrier
`W(r,theta,z) = (r/(1-z²)) * cos (2*(theta-alpha/2))` is strictly negative
inside the cusp `0 ≤ 2*r ≤ d`, `d = 1-z² > 0`.

The underlying calculus identity is established independently with SymPy;
this theorem only handles the polynomial inequality. -/
theorem explicit_barrier_numerator
    (z r d : ℝ) (hz : z ^ 2 ≤ 1) (hr : 0 ≤ r)
    (hd : 0 ≤ d) (hrd : 2 * r ≤ d) :
    r ^ 2 * (2 + 6 * z ^ 2) - 3 * d ^ 2 ≤ -(d ^ 2) := by
  have hpoly₁ : 0 ≤ (d - 2 * r) * (d + 2 * r) :=
    mul_nonneg (by linarith) (by linarith)
  have hpoly₂ : 0 ≤ r ^ 2 * (1 - z ^ 2) :=
    mul_nonneg (sq_nonneg r) (by nlinarith)
  nlinarith

/-- A stronger barrier with exponent beta=3/2, gamma=2, on 0 <= 4*r <= d.
After multiplying its cylindrical Laplacian by a positive factor, the
numerator has the expression below and is bounded by -(13/16)*d². -/
theorem improved_barrier_numerator
    (z r d : ℝ) (hz : z ^ 2 ≤ 1) (hr : 0 ≤ r)
    (hd : 0 ≤ d) (hrd : 4 * r ≤ d) :
    r ^ 2 * (3 + 12 * z ^ 2) - (7 / 4 : ℝ) * d ^ 2
      ≤ -((13 / 16 : ℝ) * d ^ 2) := by
  have hpoly₁ : 0 ≤ (d - 4 * r) * (d + 4 * r) :=
    mul_nonneg (by linarith) (by linarith)
  have hpoly₂ : 0 ≤ r ^ 2 * (1 - z ^ 2) :=
    mul_nonneg (sq_nonneg r) (by nlinarith)
  nlinarith

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section11RegionAssembly
-- ======================================================================

/-!
# Section 11: three-region sharp remainder bookkeeping

This is ONLY a scalar part of the global proof. The conditional estimates below
are NOT derived here from the Steklov spectrum. No DtN operator is defined.

In a squared spatial partition, face, edge, and vertex trace contributions
add exactly, whereas their estimates combine by the triangle inequality.
Unlike the early integer-only module, the variables range over real L.

UNCOMPILED SOURCE CANDIDATE: Lean/mathlib unavailable in the runtime.
-/

namespace SteklovAudit

/-- The finite three-region error estimate at every real spectral energy. -/
theorem three_region_remainder
    (Nface Nedge Nvertex Aface Aedge Avertex Bedge L
      eface eedge evertex : ℝ)
    (hf : |Nface - Aface * L ^ 2| ≤ eface)
    (he : |Nedge - (Aedge * L ^ 2 + Bedge * L)| ≤ eedge)
    (hv : |Nvertex - Avertex * L ^ 2| ≤ evertex) :
    |(Nface + Nedge + Nvertex) -
      ((Aface + Aedge + Avertex) * L ^ 2 + Bedge * L)| ≤
      eface + eedge + evertex := by
  have h1 := abs_add_le
    (Nface - Aface * L ^ 2)
    (Nedge - (Aedge * L ^ 2 + Bedge * L))
  have h2 := abs_add_le
    ((Nface - Aface * L ^ 2) +
      (Nedge - (Aedge * L ^ 2 + Bedge * L)))
    (Nvertex - Avertex * L ^ 2)
  have hnormal :
      (Nface + Nedge + Nvertex) -
        ((Aface + Aedge + Avertex) * L ^ 2 + Bedge * L) =
      ((Nface - Aface * L ^ 2) +
        (Nedge - (Aedge * L ^ 2 + Bedge * L))) +
      (Nvertex - Avertex * L ^ 2) := by
    ring
  rw [hnormal]
  linarith

/-- An elementary expression of the exact squared partition of the spectral
trace. This records additivity alone; it says nothing about obtaining
local estimates on any of the three regions. -/
theorem total_error_from_three_regions
    (N Nface Nedge Nvertex A Aface Aedge Avertex B L
      eface eedge evertex : ℝ)
    (hcount : N = Nface + Nedge + Nvertex)
    (harea : A = Aface + Aedge + Avertex)
    (hf : |Nface - Aface * L ^ 2| ≤ eface)
    (he : |Nedge - (Aedge * L ^ 2 + B * L)| ≤ eedge)
    (hv : |Nvertex - Avertex * L ^ 2| ≤ evertex) :
    |N - (A * L ^ 2 + B * L)| ≤ eface + eedge + evertex := by
  rw [hcount, harea]
  exact three_region_remainder
    Nface Nedge Nvertex Aface Aedge Avertex B L
    eface eedge evertex hf he hv

/-- If area and edge contributions are already collected into an explicit
real-axis two-scale error, the sharp result follows. The analytic two-scale
estimate is a hypothesis, NOT a proved spectral fact. -/
theorem real_sharp_law_if_partition_bounds
    (N : ℝ → ℝ) (A B : ℝ)
    (hTwoScale : HasRealTwoScaleBound N A B) :
    HasSharpRealLaw N A B :=
  sharp_real_law_of_two_scale N A B hTwoScale

end SteklovAudit

-- ======================================================================
-- SteklovAudit.FiniteSpectralTrace
-- ======================================================================

/-!
# Finite-dimensional spectral trace localization (Section 11)

This is an algebraic, finite-dimensional shadow of the exact identity
  Tr(P_L) = ∑_patch Tr(χ_patch P_L χ_patch)
when the multiplication cutoffs satisfy ∑ χ_patch² = 1.

Here `psi j x` are the real coordinates of normalized eigenvectors, `weight j`
is an arbitrary spectral multiplier (e.g. 1_{λ_j < L}), and `chi i x`
are spatial cutoffs. In particular χ_i need NOT commute with the spectral
projector. The actual spectral theorem, infinite-dimensional trace ideals,
Steklov DtN, and microlocal estimates are NOT constructed here.

UNCOMPILED PROOF CANDIDATE: no Lean/mathlib executable is available locally.
-/

namespace SteklovAudit

/-- For a fixed normalized state, a squared spatial partition gives total
localized mass exactly one. This does not require commutation with the
spectral projection. -/
theorem finite_eigenstate_squared_partition
    {Patch State Site : Type*}
    (patches : Finset Patch) (sites : Finset Site)
    (chi : Patch → Site → ℝ) (psi : State → Site → ℝ)
    (j : State)
    (hpartition : ∀ x ∈ sites, (∑ i ∈ patches, (chi i x) ^ 2) = 1)
    (hnorm : (∑ x ∈ sites, (psi j x) ^ 2) = 1) :
    (∑ i ∈ patches, ∑ x ∈ sites, (chi i x) ^ 2 * (psi j x) ^ 2) = 1 := by
  classical
  calc
    (∑ i ∈ patches, ∑ x ∈ sites, (chi i x) ^ 2 * (psi j x) ^ 2) =
        ∑ x ∈ sites, ∑ i ∈ patches, (chi i x) ^ 2 * (psi j x) ^ 2 := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ sites, (∑ i ∈ patches, (chi i x) ^ 2) * (psi j x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_mul]
    _ = ∑ x ∈ sites, (psi j x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hpartition x hx]
          ring
    _ = 1 := hnorm

/-- Finite spectral trace identity for any real spectral multiplier, including
signed ones. No commutation between spatial and spectral localization is
assumed. -/
theorem finite_spectral_trace_squared_partition
    {Patch State Site : Type*}
    (patches : Finset Patch) (states : Finset State) (sites : Finset Site)
    (chi : Patch → Site → ℝ) (psi : State → Site → ℝ)
    (weight : State → ℝ)
    (hpartition : ∀ x ∈ sites, (∑ i ∈ patches, (chi i x) ^ 2) = 1)
    (hnorm : ∀ j ∈ states, (∑ x ∈ sites, (psi j x) ^ 2) = 1) :
    (∑ i ∈ patches, ∑ j ∈ states,
      (∑ x ∈ sites, (chi i x) ^ 2 * (psi j x) ^ 2) * weight j) =
      ∑ j ∈ states, weight j := by
  classical
  calc
    (∑ i ∈ patches, ∑ j ∈ states,
        (∑ x ∈ sites, (chi i x) ^ 2 * (psi j x) ^ 2) * weight j) =
      ∑ j ∈ states, ∑ i ∈ patches,
        (∑ x ∈ sites, (chi i x) ^ 2 * (psi j x) ^ 2) * weight j := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ states,
          (∑ i ∈ patches, ∑ x ∈ sites,
            (chi i x) ^ 2 * (psi j x) ^ 2) * weight j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
    _ = ∑ j ∈ states, weight j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [finite_eigenstate_squared_partition patches sites chi psi j
            hpartition (hnorm j hj)]
          ring

/-- Positive local spectral mass for a nonnegative multiplier, including
spectral projectors and positive heat multipliers. -/
theorem finite_local_spectral_mass_nonneg
    {Patch State Site : Type*}
    (states : Finset State) (sites : Finset Site)
    (chi : Patch → Site → ℝ) (psi : State → Site → ℝ)
    (weight : State → ℝ) (i : Patch)
    (hweight : ∀ j ∈ states, 0 ≤ weight j) :
    0 ≤ ∑ j ∈ states,
      (∑ x ∈ sites, (chi i x) ^ 2 * (psi j x) ^ 2) * weight j := by
  classical
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact hweight j hj

/-- Exact finite spectral counting identity at arbitrary real energy L.
The left side is a sum of localized positive traces. -/
theorem finite_local_count_identity
    {Patch State Site : Type*}
    (patches : Finset Patch) (states : Finset State) (sites : Finset Site)
    (chi : Patch → Site → ℝ) (psi : State → Site → ℝ)
    (energy : State → ℝ) (L : ℝ)
    (hpartition : ∀ x ∈ sites, (∑ i ∈ patches, (chi i x) ^ 2) = 1)
    (hnorm : ∀ j ∈ states, (∑ x ∈ sites, (psi j x) ^ 2) = 1) :
    (∑ i ∈ patches, ∑ j ∈ states,
      (∑ x ∈ sites, (chi i x) ^ 2 * (psi j x) ^ 2) *
        (if energy j < L then (1 : ℝ) else 0)) =
      ∑ j ∈ states, (if energy j < L then (1 : ℝ) else 0) := by
  classical
  exact finite_spectral_trace_squared_partition patches states sites chi psi
    (fun j => if energy j < L then (1 : ℝ) else 0) hpartition hnorm

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7PolynomialDuhamel
-- ======================================================================

/-!
# Section 7: algebraic Duhamel identity and contraction estimate

This is a discrete-time, noncommutative operator-algebra model of the
quasicommutator step in manuscript (7.24)--(7.29).

For operators a,b,r in any (possibly noncommutative) ring, the defect
D = a*r - r*b satisfies an exact telescoping formula for a^n*r-r*b^n.
For contractions in a normed ring, the norm of the latter is bounded by
n*‖D‖. This is an *algebraic* analogue of the |t| factor in continuous
Duhamel. It does not construct unitary groups, spectral projectors,
Hilbert--Schmidt ideals, or the tetrahedral DtN operator.

UNCOMPILED SOURCE CANDIDATE: Lean/mathlib is unavailable in this runtime.
-/

namespace SteklovAudit

/-- Recursively accumulated intertwining defect, with the order of factors
retained (the ring need not be commutative). -/
def polynomialDuhamel {R : Type*} [Ring R] (a b r : R) : ℕ → R
  | 0 => 0
  | n + 1 => polynomialDuhamel a b r n * b + a ^ n * (a * r - r * b)

/-- Noncommutative discrete Duhamel identity. -/
theorem polynomial_duhamel_identity {R : Type*} [Ring R]
    (a b r : R) (n : ℕ) :
    polynomialDuhamel a b r n = a ^ n * r - r * b ^ n := by
  induction n with
  | zero => simp [polynomialDuhamel]
  | succ n ih =>
      simp only [polynomialDuhamel, ih]
      rw [pow_succ, pow_succ]
      simp only [sub_mul, mul_sub, mul_assoc]
      abel

/-- An exact intertwiner also intertwines all integer powers. -/
theorem intertwines_all_powers {R : Type*} [Ring R]
    (a b r : R) (h : a * r = r * b) (n : ℕ) :
    a ^ n * r = r * b ^ n := by
  have hzero : polynomialDuhamel a b r n = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp [polynomialDuhamel, ih, h]
  have hid := polynomial_duhamel_identity a b r n
  rw [hzero] at hid
  exact sub_eq_zero.mp hid.symm

/-- Contractivity gives the discrete analogue of the Duhamel time factor.
The norm here is the ambient submultiplicative norm, not an HS norm. -/
theorem polynomial_duhamel_contraction_bound
    {R : Type*} [NormedRing R]
    (a b r : R) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n * r - r * b ^ n‖ ≤ (n : ℝ) * ‖a * r - r * b‖ := by
  set d : R := a * r - r * b with hd
  have hpowd : ∀ m : ℕ, ‖a ^ m * d‖ ≤ ‖d‖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          ‖a ^ (m + 1) * d‖ = ‖a * (a ^ m * d)‖ := by rw [pow_succ', mul_assoc]
          _ ≤ ‖a‖ * ‖a ^ m * d‖ := norm_mul_le _ _
          _ ≤ 1 * ‖d‖ := mul_le_mul ha ih (norm_nonneg _) zero_le_one
          _ = ‖d‖ := one_mul _
  have hrec : ∀ m : ℕ,
      ‖polynomialDuhamel a b r m‖ ≤ (m : ℝ) * ‖d‖ := by
    intro m
    induction m with
    | zero => simp [polynomialDuhamel]
    | succ m ih =>
        have hleft : ‖polynomialDuhamel a b r m * b‖ ≤
            ‖polynomialDuhamel a b r m‖ := by
          calc
            _ ≤ ‖polynomialDuhamel a b r m‖ * ‖b‖ := norm_mul_le _ _
            _ ≤ ‖polynomialDuhamel a b r m‖ * 1 :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg _)
            _ = ‖polynomialDuhamel a b r m‖ := mul_one _
        have hstep : polynomialDuhamel a b r (m + 1) =
            polynomialDuhamel a b r m * b + a ^ m * d := rfl
        rw [hstep]
        calc
          _ ≤ ‖polynomialDuhamel a b r m * b‖ + ‖a ^ m * d‖ := norm_add_le _ _
          _ ≤ (m : ℝ) * ‖d‖ + ‖d‖ := by linarith [hpowd m]
          _ = ((m + 1 : ℕ) : ℝ) * ‖d‖ := by push_cast; ring
  rw [← polynomial_duhamel_identity a b r n]
  exact hrec n

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7TaylorDuhamel
-- ======================================================================

/-!
# Section 7: truncated continuous-time Duhamel, noncommutative coefficients

The finite Taylor polynomial for the exponential satisfies an exact
intertwining-defect identity. Unlike a mere discrete-power estimate, this
identifies every Taylor coefficient of the continuous-time Duhamel formula.

The limit N -> infinity, operator-valued integration, unbounded domains,
unitarity and Hilbert--Schmidt ideal estimates are NOT formalized here.
This is an UNCOMPILED Lean proof candidate.
-/

namespace SteklovAudit

/-- Rational-coefficient Taylor polynomial in a possibly noncommutative
    rational algebra. The scalar is central by the Algebra instance. -/
def truncatedExp {R : Type*} [Ring R] [Algebra ℚ R]
    (a : R) (t : ℚ) (N : ℕ) : R :=
  ∑ n ∈ Finset.range (N + 1),
    (t ^ n / (Nat.factorial n : ℚ)) • (a ^ n)

/-- Exact quasicommutator identity for the truncated exponential.
    This is a polynomial identity, not a statement about operator domains. -/
theorem truncated_exp_quasicommutator
    {R : Type*} [Ring R] [Algebra ℚ R]
    (a b r : R) (t : ℚ) (N : ℕ) :
    truncatedExp a t N * r - r * truncatedExp b t N =
      ∑ n ∈ Finset.range (N + 1),
        (t ^ n / (Nat.factorial n : ℚ)) •
          polynomialDuhamel a b r n := by
  classical
  unfold truncatedExp
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [polynomial_duhamel_identity]
  rw [smul_mul_assoc, mul_smul_comm, smul_sub]

/-- If the infinitesimal generators intertwine exactly, their finite
    exponential Taylor polynomials intertwine at every order. -/
theorem truncated_exp_exact_intertwiner
    {R : Type*} [Ring R] [Algebra ℚ R]
    (a b r : R) (t : ℚ) (N : ℕ)
    (h : a * r = r * b) :
    truncatedExp a t N * r = r * truncatedExp b t N := by
  have hpoly : ∀ n : ℕ, polynomialDuhamel a b r n = 0 := by
    intro n
    rw [polynomial_duhamel_identity]
    exact sub_eq_zero.mpr (intertwines_all_powers a b r h n)
  have hid := truncated_exp_quasicommutator a b r t N
  have hsum :
      (∑ n ∈ Finset.range (N + 1),
        (t ^ n / (Nat.factorial n : ℚ)) •
          polynomialDuhamel a b r n) = 0 := by
    simp [hpoly]
  rw [hsum] at hid
  exact sub_eq_zero.mp hid

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7HSTails
-- ======================================================================

/-!
# Section 7: finite Hilbert--Schmidt tail bookkeeping

In an orthonormal basis the squared HS norm is the sum of squared matrix
coefficients. This module proves finite-coordinate tail domination and the
fact that the tail is zero once all retained columns are below the cutoff.
It does not claim a theorem for arbitrary infinite-dimensional operators.

UNCOMPILED SOURCE CANDIDATE.
-/

namespace SteklovAudit

/-- Squared HS norm on a finite rectangular coefficient set. -/
def finiteHSSquare {I J : Type*}
    (rows : Finset I) (cols : Finset J) (k : I → J → ℝ) : ℝ :=
  ∑ i ∈ rows, ∑ j ∈ cols, (k i j) ^ 2

/-- Restricting the spectral columns cannot increase the HS norm squared. -/
theorem finite_hs_tail_le_total {I J : Type*}
    (rows : Finset I) (cols tail : Finset J) (k : I → J → ℝ)
    (hsub : tail ⊆ cols) :
    finiteHSSquare rows tail k ≤ finiteHSSquare rows cols k := by
  classical
  unfold finiteHSSquare
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro j hj hnot
    exact sq_nonneg (k i j))

/-- A finite-rank coefficient array has exactly zero high-energy tail
    after its maximum spectral column energy. -/
theorem finite_hs_tail_vanishes {I J : Type*}
    (rows : Finset I) (cols : Finset J)
    (energy : J → ℝ) (k : I → J → ℝ) (L : ℝ)
    (hbelow : ∀ j ∈ cols, energy j < L) :
    finiteHSSquare rows (cols.filter (fun j => L ≤ energy j)) k = 0 := by
  classical
  have hempty : cols.filter (fun j => L ≤ energy j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hjc : j ∈ cols := (Finset.mem_filter.mp hj).1
    have hje : L ≤ energy j := (Finset.mem_filter.mp hj).2
    exact (not_le_of_gt (hbelow j hjc)) hje
  simp [finiteHSSquare, hempty]

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section9PropagationScales
-- ======================================================================

/-!
# Section 9.5: exact exponent conditions for a one-edge passage

Manuscript (9.12) takes gamma=h^rho, t_h=h^(rho-sigma), eta=h^rho,
with 0<sigma<rho<1/2. The two relevant small parameters are
 gamma/t_h = h^sigma and h/(eta*t_h) = h^(1-2*rho+sigma).
The lemmas below check positivity of all exponents; they DO NOT prove
propagation, Mourre estimates, or an operator Duhamel comparison.

UNCOMPILED SOURCE CANDIDATE.
-/

namespace SteklovAudit

theorem section9_exponent_positivity
    (rho sigma : ℝ) (hs : 0 < sigma) (hsr : sigma < rho)
    (hr : rho < (1 / 2 : ℝ)) :
    0 < rho - sigma ∧ 0 < sigma ∧ 0 < 1 - 2 * rho + sigma := by
  constructor
  · linarith
  constructor
  · exact hs
  · linarith

/-- The explicit numerical choice rho=1/3, sigma=1/12 gives
    rho-sigma=1/4 and 1-2rho+sigma=5/12. -/
theorem section9_example_exponents :
    ((1 / 3 : ℚ) - 1 / 12 = 1 / 4) ∧
    ((1 : ℚ) - 2 * (1 / 3) + 1 / 12 = 5 / 12) := by
  constructor <;> norm_num

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section9CellBudget
-- ======================================================================

/-!
# Section 9: finite phase-cell concatenation error budget

If at most h^(-M) cells are present and each cell error is at most
h^(N+M), the total error is at most h^N. This is the algebraic
mechanism behind absorbing polynomially many cells into h^infinity.
The bound on the number of cells and the individual microlocal errors
are ASSUMPTIONS; no propagation theorem is proved here.

UNCOMPILED SOURCE CANDIDATE.
-/

namespace SteklovAudit

theorem finite_phase_cell_error_budget
    {ι : Type*} (cells : Finset ι) (err : ι → ℝ)
    (h : ℝ) (N M : ℕ) (h0 : 0 ≤ h)
    (hcount : (cells.card : ℝ) * h ^ M ≤ 1)
    (hcell : ∀ i ∈ cells, |err i| ≤ h ^ (N + M)) :
    |∑ i ∈ cells, err i| ≤ h ^ N := by
  classical
  calc
    |∑ i ∈ cells, err i| ≤ ∑ i ∈ cells, |err i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ cells, h ^ (N + M) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcell i hi
    _ = (cells.card : ℝ) * h ^ (N + M) := by simp
    _ = ((cells.card : ℝ) * h ^ M) * h ^ N := by
      rw [pow_add]
      ring
    _ ≤ 1 * h ^ N := mul_le_mul_of_nonneg_right hcount (pow_nonneg h0 _)
    _ = h ^ N := one_mul _

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7RelativeFinite
-- ======================================================================

/-!
# Section 7.7: finite-spectrum relative trace normalization

These are the finite spectral analogues of the inverse-trace difference and
the negative-energy normalization used for the wedge relative primitive.
They do not construct the continuous spectral-shift function, nor prove that
the massive wedge inverse difference is trace class.

UNCOMPILED SOURCE CANDIDATE.
-/

namespace SteklovAudit

/-- Algebraic trace difference in a finite common eigenvalue index set. -/
theorem finite_relative_inverse_trace
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, (a i)⁻¹) - (∑ i ∈ s, (b i)⁻¹) =
      ∑ i ∈ s, ((a i)⁻¹ - (b i)⁻¹) := by
  rw [Finset.sum_sub_distrib]

/-- For a finite spectrum, the cumulative count is zero below its bottom. -/
theorem finite_spectral_count_below_bottom
    {ι : Type*} (s : Finset ι) (energy : ι → ℝ) (L : ℝ)
    (hbelow : ∀ i ∈ s, L < energy i) :
    (s.filter (fun i => energy i ≤ L)).card = 0 := by
  classical
  have hempty : s.filter (fun i => energy i ≤ L) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hile : energy i ≤ L := (Finset.mem_filter.mp hi).2
    exact (not_le_of_gt (hbelow i his)) hile
  simp [hempty]

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7OffBandIteration
-- ======================================================================

/-!
# Section 7.8 / equation (7.46): algebraic off-band iteration

All results here are purely algebraic, valid in an arbitrary possibly
NONCOMMUTATIVE ring. They do not assert that the tetrahedral gluing defect
is Hilbert--Schmidt, nor that the relevant off-band map is a contraction.

UNCOMPILED SOURCE CANDIDATE: Lean/Lake unavailable in this runtime.
-/

namespace SteklovAudit

/-- The affine fixed-point map from (5.10): `X = T X S - U S`, with
`T = (A-L)E`, `U = EK`, `S = (B-L)⁻¹(1-Q)` (suppressing domain issues). -/
def offBandStep {R : Type*} [Ring R] (T U S X : R) : R :=
  T * X * S - U * S

/-- The inhomogeneous defect cancels exactly, even when all three
operators fail to commute. -/
theorem offBandStep_difference {R : Type*} [Ring R]
    (T U S X Y : R) :
    offBandStep T U S X - offBandStep T U S Y =
      T * (X - Y) * S := by
  calc
    offBandStep T U S X - offBandStep T U S Y
        = T * X * S - T * Y * S := by
            dsimp [offBandStep]
            abel
    _ = T * (X - Y) * S := by
          rw [mul_sub, sub_mul]

/-- Start from zero and apply the off-band map repeatedly. -/
def offBandIterate {R : Type*} [Ring R] (T U S : R) : ℕ → R
  | 0 => 0
  | n + 1 => offBandStep T U S (offBandIterate T U S n)

/-- Every successive increment is obtained by sandwiching the previous
increment by `T` and `S`. No commutativity is required. -/
theorem offBandIterate_increment {R : Type*} [Ring R]
    (T U S : R) (n : ℕ) :
    offBandIterate T U S (n + 2) - offBandIterate T U S (n + 1) =
      T * (offBandIterate T U S (n + 1) -
        offBandIterate T U S n) * S := by
  change offBandStep T U S (offBandIterate T U S (n + 1)) -
      offBandStep T U S (offBandIterate T U S n) = _
  exact offBandStep_difference T U S _ _

/-- A fixed point differs from the `n`-th iterate by exactly `Tⁿ X Sⁿ`.
This is the finite algebraic backbone of the geometric HS convergence
asserted in (7.46), conditional on a contraction estimate. -/
theorem offBandIterate_error {R : Type*} [Ring R]
    (T U S X : R) (hfix : offBandStep T U S X = X) (n : ℕ) :
    X - offBandIterate T U S n = T ^ n * X * S ^ n := by
  induction n with
  | zero => simp [offBandIterate]
  | succ n ih =>
      calc
        X - offBandIterate T U S (n + 1)
            = offBandStep T U S X -
              offBandStep T U S (offBandIterate T U S n) := by
                rw [hfix]
                rfl
        _ = T * (X - offBandIterate T U S n) * S :=
              offBandStep_difference T U S X _
        _ = T ^ (n + 1) * X * S ^ (n + 1) := by
              rw [ih, pow_succ', pow_succ]
              simp only [mul_assoc]

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7DyadicPrimitive
-- ======================================================================

/-!
# Section 7.7 / equations (7.42)--(7.43): dyadic summability

For R_j = 2^j R_0, the uniform bound |F_j(it)/(it)| ≤ C R_j⁻²
has a summable majorant. This module proves the exact geometric sum
for the scalar majorant. The analytic claims that the wedge's relative
trace has this scaling and that the resulting Fourier integrand is L¹
remain separate obligations.

UNCOMPILED SOURCE CANDIDATE.
-/

namespace SteklovAudit

/-- Exact finite geometric sum with ratio 1/4. -/
theorem quarter_geometric_identity (n : ℕ) :
    3 * (∑ j ∈ Finset.range n, (1 / 4 : ℝ) ^ j) =
      4 * (1 - (1 / 4 : ℝ) ^ n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- All finite dyadic inverse-square sums are bounded by 4/3. -/
theorem quarter_geometric_le (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / 4 : ℝ) ^ j) ≤ 4 / 3 := by
  have h := quarter_geometric_identity n
  have hp : 0 ≤ (1 / 4 : ℝ) ^ n := pow_nonneg (by norm_num) n
  linarith

/-- A finite family of relative Fourier coefficients with the
hypothesized dyadic majorants has a bound independent of its size.
The `G_j` here are just scalar values, NOT yet wedge trace functions. -/
theorem dyadic_relative_primitive_bound
    (n : ℕ) (G : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ j < n, |G j| ≤ C * (1 / 4 : ℝ) ^ j) :
    |∑ j ∈ Finset.range n, G j| ≤ 4 * C / 3 := by
  calc
    |∑ j ∈ Finset.range n, G j|
        ≤ ∑ j ∈ Finset.range n, |G j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, C * (1 / 4 : ℝ) ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          exact hG j (Finset.mem_range.mp hj)
    _ = C * ∑ j ∈ Finset.range n, (1 / 4 : ℝ) ^ j := by
          rw [Finset.mul_sum]
    _ ≤ C * (4 / 3) :=
          mul_le_mul_of_nonneg_left (quarter_geometric_le n) hC
    _ = 4 * C / 3 := by ring

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section11CountingConventions
-- ======================================================================

/-!
# Section 11: strict versus nonstrict counting conventions

If a *real-parameter* sharp two-term law is already established for a
nonstrict counting function, its jumps must be o(L). The key is to
compare a fixed-width interval [L-d,L], not a unit-spaced sample.
This is downstream of the sharp law; it cannot establish that law.

UNCOMPILED SOURCE CANDIDATE.
-/

namespace SteklovAudit

/-- Exact two-term polynomial increment across a fixed energy window. -/
theorem realWeylPolynomial_window_increment
    (A B L d : ℝ) :
    realWeylPolynomial A B L - realWeylPolynomial A B (L - d) =
      2 * A * d * L - A * d ^ 2 + B * d := by
  dsimp [realWeylPolynomial]
  ring

/-- The actual counting increment is bounded by the model increment
plus both endpoint errors, without any monotonicity assumption. -/
theorem two_term_interval_error_bound
    (N : ℝ → ℝ) (A B L d ε : ℝ)
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hL : d ≤ L)
    (hhigh : |N L - realWeylPolynomial A B L| ≤ ε * L)
    (hlow : |N (L - d) - realWeylPolynomial A B (L - d)| ≤ ε * (L - d)) :
    N L - N (L - d) ≤
      2 * A * d * L - A * d ^ 2 + B * d + 2 * ε * L := by
  have h₁ := (abs_le.mp hhigh).2
  have h₂ := (abs_le.mp hlow).1
  have h₃ : ε * (L - d) ≤ ε * L :=
    mul_le_mul_of_nonneg_left (sub_le_self L hd) hε
  have hp := realWeylPolynomial_window_increment A B L d
  linarith

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7UniformTailObstruction
-- ======================================================================

/-!
# Uniform spectral tails: a necessary compactness condition

The statement that each fixed Hilbert--Schmidt operator has a vanishing
high-energy tail does NOT imply a uniform estimate for a varying family.
The counterexample below is finite rank at every index and has HS norm one.

This is an UNCOMPILED Lean source candidate. No theorem here asserts a
property of the tetrahedral Dirichlet-to-Neumann operator.
-/
namespace SteklovAudit

/-- Unit mass at the moving spectral coordinate `n`. -/
def movingDefect (n j : ℕ) : ℝ := if j = n then 1 else 0

/-- Each moving defect has squared Hilbert--Schmidt norm one. -/
theorem movingDefect_norm_one (n : ℕ) :
    (∑ j ∈ ({n} : Finset ℕ), (movingDefect n j)^2) = 1 := by
  simp [movingDefect]

/-- The mass remains completely above any cutoff `L ≤ n`. -/
theorem movingDefect_tail_one (n L : ℕ) (h : L ≤ n) :
    (∑ j ∈ ({n} : Finset ℕ).filter (fun j => L ≤ j),
      (movingDefect n j)^2) = 1 := by
  simp [movingDefect, h]

/-- A fixed moving defect eventually has zero tail. -/
theorem movingDefect_fixed_tail_zero (n L : ℕ) (h : n < L) :
    (∑ j ∈ ({n} : Finset ℕ).filter (fun j => L ≤ j),
      (movingDefect n j)^2) = 0 := by
  simp [movingDefect, Nat.not_le.mpr h]

/-- There is no uniform tail decay over all moving defects. -/
theorem movingDefect_no_uniform_tail (L : ℕ) :
    ∃ n : ℕ, L ≤ n ∧
      (∑ j ∈ ({n} : Finset ℕ).filter (fun j => L ≤ j),
        (movingDefect n j)^2) = 1 := by
  refine ⟨L, le_refl L, ?_⟩
  exact movingDefect_tail_one L L (le_refl L)

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7WeightedTail
-- ======================================================================

/-!
# Section 7: finite spectral moment implies uniform tail control

This is a finite-spectrum, uncompiled Lean source candidate. It does not
assert that the tetrahedral gluing defects satisfy the required moment bound.
-/
namespace SteklovAudit

/-- A nonnegative spectral moment bounds the mass above a positive cutoff.
    This is the squared-Hilbert--Schmidt analogue of the spectral Markov bound. -/
theorem finite_weighted_tail_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (energy mass : ι → ℝ) (L C : ℝ)
    (hL : 0 < L) (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (henergy : ∀ i ∈ s, L ≤ energy i)
    (hbudget : (∑ i ∈ s, energy i * mass i) ≤ C) :
    (∑ i ∈ s, mass i) ≤ C / L := by
  have hterm : ∀ i ∈ s, L * mass i ≤ energy i * mass i := by
    intro i hi
    exact mul_le_mul_of_nonneg_right (henergy i hi) (hmass i hi)
  have hsum : (∑ i ∈ s, L * mass i) ≤
      (∑ i ∈ s, energy i * mass i) := by
    exact Finset.sum_le_sum hterm
  have hfactor : L * (∑ i ∈ s, mass i) ≤ C := by
    calc
      L * (∑ i ∈ s, mass i) = ∑ i ∈ s, L * mass i := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, energy i * mass i := hsum
      _ ≤ C := hbudget
  exact (le_div_iff₀ hL).2 (by linarith)

/-- Uniform moment control gives a common finite-energy cutoff bound.
    No compactness or operator-specific assumption is smuggled in. -/
theorem finite_weighted_tail_uniform
    {α ι : Type*} [DecidableEq ι]
    (s : α → Finset ι) (energy mass : α → ι → ℝ)
    (L C : ℝ) (hL : 0 < L)
    (hmass : ∀ a i, i ∈ s a → 0 ≤ mass a i)
    (henergy : ∀ a i, i ∈ s a → L ≤ energy a i)
    (hbudget : ∀ a, (∑ i ∈ s a, energy a i * mass a i) ≤ C) :
    ∀ a, (∑ i ∈ s a, mass a i) ≤ C / L := by
  intro a
  exact finite_weighted_tail_bound (s a) (energy a) (mass a) L C hL
    (hmass a) (henergy a) (hbudget a)

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7OffBandGap
-- ======================================================================

/-!
# Section 7: off-band Hilbert--Schmidt mass from a spectral gap

Finite-spectrum scalar reduction of the Sylvester defect identity
(A J - J B)_{ij} = (a_i-b_j) J_{ij}.
No tetrahedral PDE estimate is postulated or proved here.
All declarations are source candidates until Lean compilation succeeds.
-/
namespace SteklovAudit

/-- A positive gap between scalar energies yields a squared gap. -/
theorem squared_gap_lower_bound (d g : ℝ)
    (hd : 0 ≤ d) (hgap : d ≤ g) : d * d ≤ g * g := by
  have hprod : 0 ≤ (g - d) * (g + d) :=
    mul_nonneg (sub_nonneg.mpr hgap) (add_nonneg (le_trans hd hgap) hd)
  nlinarith [hprod]

/-- Abstract finite spectral-gap estimate: if each squared off-band
coefficient times the squared energy gap is dominated by the corresponding
squared defect coefficient, the total coefficient mass is bounded by the
squared-defect budget divided by the squared gap. -/
theorem finite_offband_hs_gap
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (gap mass defect : ι → ℝ) (d C : ℝ)
    (hd : 0 < d)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hgap : ∀ i ∈ s, d ≤ gap i)
    (hdefect : ∀ i ∈ s, gap i * gap i * mass i ≤ defect i)
    (hbudget : (∑ i ∈ s, defect i) ≤ C) :
    (∑ i ∈ s, mass i) ≤ C / (d * d) := by
  have hterm : ∀ i ∈ s, (d * d) * mass i ≤ defect i := by
    intro i hi
    calc
      (d * d) * mass i ≤ (gap i * gap i) * mass i := by
        exact mul_le_mul_of_nonneg_right
          (squared_gap_lower_bound d (gap i) (le_of_lt hd) (hgap i hi))
          (hmass i hi)
      _ ≤ defect i := hdefect i hi
  have hsum : (∑ i ∈ s, (d * d) * mass i) ≤ C := by
    calc
      (∑ i ∈ s, (d * d) * mass i) ≤ ∑ i ∈ s, defect i :=
        Finset.sum_le_sum hterm
      _ ≤ C := hbudget
  have hfactor : (d * d) * (∑ i ∈ s, mass i) ≤ C := by
    calc
      (d * d) * (∑ i ∈ s, mass i) = ∑ i ∈ s, (d * d) * mass i := by
        rw [Finset.mul_sum]
      _ ≤ C := hsum
  apply (le_div_iff₀ (mul_pos hd hd)).2
  nlinarith [hfactor]

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7SpectralDefectIdentity
-- ======================================================================

/-!
# Section 7: finite spectral defect identity and gap bound

This finite-dimensional diagonal spectral model derives the squared defect
budget from the intertwining identity itself, rather than taking coefficientwise
defect dominance as an assumption. It is not the unbounded-operator/PDE step.
Source candidate pending actual Lean compilation.
-/
namespace SteklovAudit

/-- Entrywise spectral Sylvester identity, with no commutation hypothesis on J. -/
theorem spectral_defect_entry (a b j : ℝ) :
    a * j - j * b = (a - b) * j := by ring

/-- Exact squared identity underlying the Hilbert--Schmidt spectral gap bound. -/
theorem spectral_defect_square (a b j : ℝ) :
    (a * j - j * b) ^ 2 = (a - b) ^ 2 * j ^ 2 := by ring

/-- Finite-dimensional squared Hilbert--Schmidt estimate for diagonal A,B.
    All spectral pairs in s are required to be separated by d. -/
theorem finite_sylvester_hs_gap
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b j : ι → ℝ) (d : ℝ) (hd : 0 < d)
    (hgap : ∀ i ∈ s, d ≤ |a i - b i|) :
    (d * d) * (∑ i ∈ s, (j i)^2) ≤
      ∑ i ∈ s, (a i * j i - j i * b i)^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hsq : d * d ≤ (a i - b i) * (a i - b i) := by
    have h := hgap i hi
    have ha : 0 ≤ |a i - b i| := abs_nonneg _
    nlinarith [sq_abs (a i - b i), sq_nonneg (|a i - b i| - d)]
  have hj : 0 ≤ (j i)^2 := sq_nonneg _
  calc
    d * d * (j i)^2 ≤ ((a i - b i) * (a i - b i)) * (j i)^2 :=
      mul_le_mul_of_nonneg_right hsq hj
    _ = (a i * j i - j i * b i)^2 := by ring

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7FrameDefectBudget
-- ======================================================================

/-!
# Section 7: quantitative non-loss from an almost-isometric identification

These are elementary real inequalities, NOT a claim that the actual
wedge/tetrahedron identification is almost isometric on a spectral window.
Source candidates until a successful Lean compilation.
-/
namespace SteklovAudit

/-- If the squared norm defect of an identification is bounded by `eps`
per spectral vector, then its total squared mass retains at least
`(1-eps)` times the window dimension. -/
theorem window_frame_from_norm_defect
    (count mass eps : ℝ)
    (hdefect : count - mass ≤ eps * count) :
    (1 - eps) * count ≤ mass := by
  nlinarith

/-- A counting bound that exposes both missing PDE inputs: a uniform
near-isometry estimate and a spectral-gap defect estimate. -/
theorem window_count_from_near_isometry_and_gap
    (count mass low high eps gap defectSq lowBudget : ℝ)
    (hnear : count - mass ≤ eps * count)
    (hsplit : mass = low + high)
    (hlow : low ≤ lowBudget)
    (hgap : gap * gap * high ≤ defectSq)
    (heps : eps < 1) (hgapPos : 0 < gap) :
    count ≤ (lowBudget + defectSq / (gap * gap)) / (1 - eps) := by
  have hgapSq : 0 < gap * gap := mul_pos hgapPos hgapPos
  have hhigh : high ≤ defectSq / (gap * gap) := by
    apply (le_div_iff₀ hgapSq).2
    nlinarith [hgap]
  have hframe : (1 - eps) * count ≤ mass := by
    nlinarith [hnear]
  apply (le_div_iff₀ (by linarith : 0 < 1 - eps)).2
  linarith

/-- A bound for the loss of spectral mass when the identification is
approximately isometric. Useful separately from the counting argument. -/
theorem window_mass_loss_bound
    (count mass eps : ℝ)
    (hnear : count - mass ≤ eps * count)
    (hcount : 0 ≤ count) (heps : 0 ≤ eps) :
    count ≤ mass + eps * count := by
  linarith

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7ResolventLocalization
-- ======================================================================

/-! Algebraic foundations of resolvent localization. These are scalar identities,
not a formalized functional calculus or a PDE gluing theorem. -/
namespace SteklovAudit

/-- The scalar resolvent intertwining identity, with all denominator
nonvanishing hypotheses exposed. The matrix version uses the same order:
`(B-z)⁻¹ J - J (A-z)⁻¹ = -(B-z)⁻¹ (BJ-JA) (A-z)⁻¹`. -/
theorem resolvent_intertwining_scalar (a b j z : ℚ)
    (ha : a - z ≠ 0) (hb : b - z ≠ 0) :
    j / (b-z) - j / (a-z) =
      -((b*j-j*a) / ((b-z)*(a-z))) := by
  field_simp
  ring

/-- A partition of unity removes duplication in a scalar resolvent trace. -/
theorem resolvent_weighted_partition (s : Finset ℕ) (w : ℕ → ℚ)
    (h : ∑ i ∈ s, w i = 1) (a z : ℚ) (ha : a-z ≠ 0) :
    (∑ i ∈ s, w i * (1/(a-z))) = 1/(a-z) := by
  rw [← Finset.sum_mul, h, one_mul]

/-- Exact cancellation when two scalar model spectra coincide. -/
theorem resolvent_equal_model (a j z : ℚ) :
    j * (a-z) - (a-z) * j = 0 := by
  ring
end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section9ScaleBudget
-- ======================================================================

/-! Elementary propagation budgets: an error bound at each scale is not
by itself a summable global error. -/
namespace SteklovAudit

/-- Exact accumulation of an unsuppressed scale error. -/
theorem constant_scale_error (n : ℕ) (c : ℚ) :
    (∑ _i ∈ Finset.range n, c) = n * c := by
  simp

/-- A geometric propagation budget is uniformly bounded, provided
`0 ≤ r < 1`; this is a *hypothesis*, not derived from tetrahedral diffraction. -/
theorem geometric_scale_budget (n : ℕ) (r : ℚ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ i ∈ Finset.range n, r ^ i) ≤ 1 / (1-r) := by
  have hden : 0 < 1-r := sub_pos.mpr hr1
  have hpow : 0 ≤ r^n := pow_nonneg hr0 _
  have hsum' : ∀ m : ℕ, (∑ i ∈ Finset.range m, r ^ i) * (1-r) = 1-r^m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      ring
  have hsum := hsum' n
  apply (le_div_iff₀ hden).2
  rw [hsum]
  linarith
end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7ResolventTraceObstruction
-- ======================================================================

/-! A dimension-growth obstruction to upgrading Hilbert--Schmidt
intertwining defects to dimension-free trace resolvent estimates.
These are scalar arithmetic lemmas, not operator formalizations. -/
namespace SteklovAudit

/-- For `A=0`, `B=1`, `J=I` on an `n`-dimensional space and
`z=-1`, the trace resolvent difference is `n/2` while the
squared Hilbert--Schmidt intertwining defect is `n`.
This lemma checks the exact rational trace identity. -/
theorem shifted_resolvent_trace_exact (n : ℕ) :
    (n : ℚ) * (1 - (1 / 2 : ℚ)) = (n : ℚ) / 2 := by
  ring

/-- Squaring the trace difference yields `n²/4`, versus defect
HS norm squared `n`; the ratio is unbounded with dimension. -/
theorem shifted_resolvent_trace_square (n : ℕ) :
    ((n : ℚ) / 2)^2 = (n : ℚ)^2 / 4 := by
  ring

/-- Any proposed dimension-free squared estimate with constant `c`
 fails for integer dimension `n > 4c`, since `(n/2)^2 > c*n`. -/
theorem shifted_resolvent_no_uniform_HS_constant
    (n : ℕ) (c : ℚ) (hc : 0 ≤ c)
    (hn : 4 * c < (n : ℚ)) :
    c * (n : ℚ) < ((n : ℚ) / 2)^2 := by
  have hnpos : (0 : ℚ) < n := lt_of_le_of_lt (mul_nonneg (by norm_num : (0:ℚ) ≤ 4) hc) hn
  have h := mul_lt_mul_of_pos_right hn hnpos
  nlinarith [sq_nonneg ((n : ℚ) / 2)]
end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section11DiscreteHeatObstruction
-- ======================================================================
/-! A discrete, positive-multiplicity obstruction to recovering sharp counting
from two heat coefficients. The heat asymptotics and spectral interpretation
are independently proved in HOURLY_RUN_19_REPORT.md, not Lean certified. -/
namespace SteklovAudit.Section11DiscreteHeatObstruction

def multiplicity (n : ℕ) : ℕ :=
  if Even n then 3*n+1 else n+1

theorem multiplicity_positive (n : ℕ) : 0 < multiplicity n := by
  unfold multiplicity
  split_ifs <;> omega

theorem multiplicity_even (k : ℕ) : multiplicity (2*k) = 6*k+1 := by
  simp [multiplicity, even_two_mul]
  omega

theorem multiplicity_odd (k : ℕ) : multiplicity (2*k+1) = 2*k+2 := by
  have h : ¬ Even (2*k+1) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨k, rfl⟩
  unfold multiplicity
  rw [if_neg h]
  all_goals omega

-- The following pairwise counting identity is the source-level target;
-- it is NOT used as an axiom by any other module.
theorem pair_multiplicity (k : ℕ) :
    multiplicity (2*k+1) + multiplicity (2*k+2) = 8*k+9 := by
  have h2 : 2*k+2 = 2*(k+1) := by ring
  rw [multiplicity_odd, h2, multiplicity_even]
  all_goals omega

end SteklovAudit.Section11DiscreteHeatObstruction

-- ======================================================================
-- SteklovAudit.Section11LaplaceObstruction
-- ======================================================================

/-! # Section 11: a rational Laplace-transform obstruction
The continuous density rho(x) = 2*x + 1 + x*sin(x) is nonnegative for x >= 0.
Its Laplace transform equals 2/t^2 + 1/t + 2*t/(1+t^2)^2.
These elementary polynomial lemmas isolate the algebra of that formula.
The analytic integral identity and the nonconvergence of the sharp remainder
are proved in the accompanying audit, NOT certified by this Lean module.
-/
namespace SteklovAudit.Section11LaplaceObstruction


theorem denominator_pos (t : ℝ) : 0 < (1 + t ^ 2) ^ 2 := by
  positivity

theorem correction_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ 2 * t / (1 + t ^ 2) ^ 2 := by
  positivity

theorem correction_le_two_t (t : ℝ) (ht : 0 ≤ t) :
    2 * t / (1 + t ^ 2) ^ 2 ≤ 2 * t := by
  have h : (1 : ℝ) ≤ (1 + t ^ 2) ^ 2 := by nlinarith [sq_nonneg t]
  apply (div_le_iff₀ (denominator_pos t)).2
  nlinarith

end SteklovAudit.Section11LaplaceObstruction

-- ======================================================================
-- SteklovAudit.Section11TwoParameterSqueeze
-- ======================================================================
/-!
# Section 11: explicit two-parameter sharp-versus-smoothed budget
These elementary statements do NOT certify the PDE estimates (7.29), (7.38),
(7.45), (9.1), or (11.2). They isolate the quantitative inference needed
once those estimates have been independently established.
-/
namespace SteklovAudit.Section11TwoParameterSqueeze

/-- If a smoothed count is close to a proposed polynomial and the sharp count
is close to the smoothed count, the sharp remainder has the sum of both budgets.
The `width` dependence is explicit and cannot be silently suppressed. -/
theorem sharp_error_budget
    (sharp smooth model width energy C eps K : ℝ)
    (hwidth : 0 ≤ width) (henergy : 0 ≤ energy)
    (hC : 0 ≤ C) (heps : 0 ≤ eps) (hK : 0 ≤ K)
    (hsharp : |sharp - smooth| ≤ C * (width * energy + 1))
    (hsmooth : |smooth - model| ≤ eps * energy + K) :
    |sharp - model| ≤ (C * width + eps) * energy + C + K := by
  have ht := abs_add_le (sharp - smooth) (smooth - model)
  have heq : sharp - model = (sharp - smooth) + (smooth - model) := by ring
  rw [heq]
  calc
    |(sharp - smooth) + (smooth - model)| ≤
        |sharp - smooth| + |smooth - model| := ht
    _ ≤ C * (width * energy + 1) + (eps * energy + K) := by linarith
    _ = (C * width + eps) * energy + C + K := by ring

/-- The fixed-width upper bound remains nonzero at normalized order `energy`;
only a separate width limit can remove it. -/
theorem fixed_width_budget (C width eps : ℝ) (hC : 0 ≤ C)
    (hw : 0 ≤ width) (he : 0 ≤ eps) :
    0 ≤ C * width + eps := by positivity

end SteklovAudit.Section11TwoParameterSqueeze

-- ======================================================================
-- SteklovAudit.Section7DuhamelDefectBudget
-- ======================================================================

/-!
Section 7: elementary finite-sum budgets underlying the continuous Duhamel
estimate. These do NOT assert that the tetrahedral PDE intertwining defect
extends to a Hilbert–Schmidt operator. That is a separate analytic obligation.
-/
namespace SteklovAudit

/-- A nonnegative time-discretized defect bound remains nonnegative. -/
theorem duhamel_discrete_budget_nonneg (n : ℕ) (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i) : 0 ≤ ∑ i, f i :=
  Finset.sum_nonneg (fun i hi => hf i)

/-- A uniform bound on each time-slice controls its cumulative budget. -/
theorem duhamel_discrete_budget_le (n : ℕ) (f : Fin n → ℝ)
    (C : ℝ) (hf : ∀ i, f i ≤ C) :
    (∑ i, f i) ≤ (n : ℝ) * C := by
  calc
    (∑ i, f i) ≤ ∑ _i : Fin n, C :=
      Finset.sum_le_sum (fun i hi => hf i)
    _ = (n : ℝ) * C := by simp

/-- A simple sufficient scale-decay budget. The geometric decay itself is
not supplied by the tetrahedral manuscript's operator estimates. -/
theorem scale_error_partial_bound (n : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ k ∈ Finset.range n, r ^ k) ≤ 1 / (1-r) := by
  have h : 0 < 1-r := sub_pos.mpr hr1
  have hsum' : ∀ m : ℕ, (∑ k ∈ Finset.range m, r ^ k) * (1-r) = 1-r^m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      ring
  have hsum := hsum' n
  have hp : 0 ≤ r^n := pow_nonneg hr0 _
  apply (le_div_iff₀ h).mpr
  nlinarith
end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7OverlapMultiplicity
-- ======================================================================

/-! Exact multiplicity accounting for joint localization.  These are scalar
lemmas only, not a proof of spectral transfer for the tetrahedron. -/
namespace SteklovAudit

/-- A chart-counting budget must pay for duplicated comparison modes. -/
theorem duplicate_rank_overcount (n q : ℕ) (hq : 1 ≤ q) :
    n ≤ q * n := by
  nlinarith

/-- The excess in a q-fold exact duplicate is (q-1)n. -/
theorem duplicate_rank_excess (n q : ℕ) (hq : 1 ≤ q) :
    q * n - n = (q - 1) * n := by
  rw [Nat.sub_mul, one_mul]

/-- A weighted partition has exactly one unit of mass per mode. -/
theorem weighted_partition_mass (n : ℕ) (weights : Finset ℕ)
    (w : ℕ → ℚ) (hpartition : ∑ i ∈ weights, w i = 1) :
    (∑ i ∈ weights, w i * (n : ℚ)) = n := by
  rw [← Finset.sum_mul, hpartition, one_mul]


end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7PartitionFrameBudget
-- ======================================================================

/-! A scalar rank-loss consequence for a *joint* localization map.
This is not an operator-theoretic construction of the joint map.
No tetrahedral estimate is assumed or asserted here. -/
namespace SteklovAudit

/-- A joint frame with `charts` target windows only controls the sum of their ranks. -/
theorem joint_frame_rank_budget
    (sourceRank totalTargetRank : ℕ) (c d defectSq : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (h : c * (d*d) * (sourceRank - totalTargetRank : ℕ) ≤ defectSq) :
    (sourceRank - totalTargetRank : ℕ) ≤ defectSq / (c * (d*d)) := by
  apply (le_div_iff₀ (mul_pos hc (mul_pos hd hd))).2
  linarith

/-- A strict one-direction defect threshold rules out rank loss for the joint map. -/
theorem joint_frame_no_rank_loss
    (sourceRank totalTargetRank : ℕ) (c d defectSq : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (h : c * (d*d) * (sourceRank - totalTargetRank : ℕ) ≤ defectSq)
    (hsmall : defectSq < c * (d*d)) : sourceRank ≤ totalTargetRank := by
  by_contra hn
  have hn' : 1 ≤ sourceRank - totalTargetRank :=
    Nat.sub_pos_of_lt (Nat.lt_of_not_ge hn)
  have hr : (1 : ℝ) ≤ (sourceRank - totalTargetRank : ℕ) := by
    exact_mod_cast hn'
  have hp : 0 < c * (d*d) := mul_pos hc (mul_pos hd hd)
  have hcost : c * (d*d) ≤ c * (d*d) * (sourceRank - totalTargetRank : ℕ) := by
    nlinarith
  linarith

/-- If a nonnegative localization loss is small in total, it is small in each chart. -/
theorem chart_loss_le_total (chartLoss otherLoss : ℝ)
    (hother : 0 ≤ otherLoss) : chartLoss ≤ chartLoss + otherLoss := by
  linarith

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7RankLossThreshold
-- ======================================================================

/-!
# Section 7: rank loss controlled by a spectral gap

These are abstract scalar consequences of a finite-dimensional kernel argument.
They do not assert that the tetrahedral comparison identification satisfies
its necessary lower frame bound or its Hilbert–Schmidt defect estimate.
-/
namespace SteklovAudit

/-- A dimension-defect budget: each spectral direction that cannot fit into
    the comparison window costs at least `c * d²` of squared defect. -/
theorem rank_loss_budget
    (sourceRank targetRank : ℕ) (c d defectSq : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hbudget : c * (d * d) * (sourceRank - targetRank : ℕ) ≤ defectSq) :
    (sourceRank - targetRank : ℕ) ≤ defectSq / (c * (d * d)) := by
  have hp : 0 < c * (d * d) := mul_pos hc (mul_pos hd hd)
  apply (le_div_iff₀ hp).2
  linarith

/-- If the gap defect is strictly below the cost of one missing direction,
    the comparison window must have at least the source rank. -/
theorem no_rank_loss_below_threshold
    (sourceRank targetRank : ℕ) (c d defectSq : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hbudget : c * (d * d) * (sourceRank - targetRank : ℕ) ≤ defectSq)
    (hsmall : defectSq < c * (d * d)) :
    sourceRank ≤ targetRank := by
  by_contra h
  have hn : 1 ≤ sourceRank - targetRank := Nat.sub_pos_of_lt (Nat.lt_of_not_ge h)
  have hcast : (1 : ℝ) ≤ (sourceRank - targetRank : ℕ) := by exact_mod_cast hn
  have hp : 0 < c * (d * d) := mul_pos hc (mul_pos hd hd)
  have : c * (d * d) ≤ c * (d * d) * (sourceRank - targetRank : ℕ) := by
    nlinarith
  linarith

end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7SmoothCutoffHSObstruction
-- ======================================================================

/-!
Section 7 diagnostic: a smooth multiplier need not have Hilbert–Schmidt
commutator with a first-order operator. This file formalizes the exact
finite-dimensional counting identities, not the infinite-dimensional
functional-analytic identification.
-/
namespace SteklovAudit

/-- Every truncated Fourier shift has squared defect equal to its number
of input modes, when the multiplier is exp(ix) and A = |D|. -/
theorem truncated_shift_hs_square (N : ℕ) :
    (∑ _k ∈ Finset.range (2 * N + 1), (1 : ℕ)) = 2 * N + 1 := by
  simp

/-- The squared HS norm cannot be bounded uniformly in cutoff. -/
theorem truncated_shift_unbounded (C : ℕ) :
    ∃ N : ℕ, C < ∑ _k ∈ Finset.range (2 * N + 1), (1 : ℕ) := by
  refine ⟨C, ?_⟩
  simp
  omega

/-- The same obstruction persists after any prescribed finite threshold. -/
theorem truncated_shift_exceeds (C N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ C < 2 * N + 1 := by
  refine ⟨C + N₀, ?_, ?_⟩ <;> omega
end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7SpectralSandwichBudget
-- ======================================================================
/-!
Section 7: exact finite-mode budgets for spectrally sandwiched commutators.
These arithmetic results do NOT certify the operator-valued estimate or the
uniform tetrahedral collar estimate. All statements are elementary and
explicit; no spectral asymptotic is assumed.
-/
namespace SteklovAudit

/-- The Fourier window [-N,N] contains exactly 2N+1 modes. -/
theorem sandwich_mode_count (N : ℕ) :
    (Finset.range (2 * N + 1)).card = 2 * N + 1 := by
  simp

/-- For a unit shift and the symbol |k|, the truncated squared HS defect
is exactly the number of input modes. -/
theorem sandwich_unit_shift_budget (N : ℕ) :
    (∑ _k ∈ Finset.range (2 * N + 1), (1 : ℕ)) = 2 * N + 1 := by
  simp

/-- The finite-mode estimate cannot be made uniform in the cutoff N. -/
theorem sandwich_no_uniform_budget (C : ℕ) :
    ∃ N : ℕ, C < (∑ _k ∈ Finset.range (2 * N + 1), (1 : ℕ)) := by
  refine ⟨C, ?_⟩
  simp
  omega

/-- Quadratic growth of the number of modes in a two-dimensional box. -/
theorem sandwich_two_dimensional_count (N : ℕ) :
    (2 * N + 1) * (2 * N + 1) = 4 * N * N + 4 * N + 1 := by
  ring
end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7WeightedPolynomialTrace
-- ======================================================================

/-! Scalar foundations for polynomial weighted spectral localization.
These are NOT a formalization of the matrix HS estimates or PDE comparison. -/
namespace SteklovAudit

/-- Weighted trace mass does not duplicate a spectral mode. -/
theorem weighted_trace_partition (s : Finset ℕ) (w : ℕ → ℚ)
    (h : ∑ i ∈ s, w i = 1) (a : ℚ) :
    (∑ i ∈ s, w i * a) = a := by
  rw [← Finset.sum_mul, h, one_mul]

/-- The first nontrivial polynomial intertwining telescoping identity. -/
theorem quadratic_intertwining (a b j : ℚ) :
    (b*b)*j-j*(a*a) = b*(b*j-j*a)+(b*j-j*a)*a := by
  ring

/-- A cubic intertwining identity used in exact matrix tests. -/
theorem cubic_intertwining (a b j : ℚ) :
    (b*b*b)*j-j*(a*a*a) =
      (b*b)*(b*j-j*a)+b*(b*j-j*a)*a+(b*j-j*a)*(a*a) := by
  ring
end SteklovAudit

-- ======================================================================
-- SteklovAudit.Section7WindowCountBudget
-- ======================================================================

/-!
# Finite spectral-window counting from a localized Sylvester defect

The assumptions `hframe` and `hinside` are explicit quantitative
non-loss and low-band budget hypotheses. Neither is asserted for
Steklov operators. These statements are source candidates until compiled.
-/
namespace SteklovAudit

/-- A lower frame bound and a low-band budget force the residual high-band
    mass to account for all remaining eigenvectors in a window. -/
theorem finite_window_mass_budget
    (windowCount lowMass highMass frameLower : ℝ)
    (hframe : frameLower * windowCount ≤ lowMass + highMass)
    (hlow : lowMass ≤ frameLower * windowCount / 2)
    (hpositive : 0 ≤ frameLower) :
    frameLower * windowCount / 2 ≤ highMass := by
  linarith

/-- A quantitative counting bound from a spectral gap, a low-band budget,
    and a lower frame bound. The two analytic inputs are visible hypotheses. -/
theorem finite_window_count_from_gap
    (windowCount lowMass highMass defectSq frameLower gap lowBudget : ℝ)
    (hframe : frameLower * windowCount ≤ lowMass + highMass)
    (hlow : lowMass ≤ lowBudget)
    (hgap : gap * gap * highMass ≤ defectSq)
    (hframepos : 0 < frameLower) (hgappos : 0 < gap)
    (hhigh : 0 ≤ highMass) :
    windowCount ≤ (lowBudget + defectSq / (gap * gap)) / frameLower := by
  have hgapSq : 0 < gap * gap := mul_pos hgappos hgappos
  have hhighBound : highMass ≤ defectSq / (gap * gap) := by
    apply (le_div_iff₀ hgapSq).2
    nlinarith [hgap]
  apply (le_div_iff₀ hframepos).2
  linarith

end SteklovAudit
