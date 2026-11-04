import Mathlib
import SteklovAudit

/-!
# Theorem 11.1 from a ledger of named hypotheses (statement-first audit)

This file states the paper's main theorem (Theorem 1.3 / 11.1, formula (11.4)) with the paper's
constants, and proves it from an explicit ledger of named hypotheses `Thm111Inputs`. The ledger
mirrors the global assembly of Section 11.2: a squared spatial partition splits the counting
function into vertex, edge and face parts, and each part carries the estimate the paper cites for it.

Ledger (each `[H#]` field below is one hypothesis; the audit script counts them):
* `[H1 splitting]`  trace linearity of the squared partition, `N = V + E + F`;
* `[H2 area]`   the three area coefficients add to `|∂T_a| / (4π) = √3 a² / (4π)`;
* `[H3 length]` the edge length kept by the vertex cutoffs is `6a + O(ε)`;
* `[H4 vertex]` (7.49): vertex part, error `O(εL) + o(L)` (the `o(L)` absorbs `O(log L) + O(1)`);
* `[H5 edge]`   (11.3): edge part, error `C_ε γ L + o(L)`. This is where (7.29), (7.38)/(7.45)
  and (9.1) enter; it is the hypothesis the abstract layer (`AbstractTransfer*.lean`) works to shrink;
* `[H6 face]`   Lemma 7.4 / Section 10.2: face part, zero linear coefficient, error `o(L)`.

Also proved here:
* `nonvacuous`: the ledger is satisfiable (an exact two-term count meets every hypothesis), so the
  main theorem is not vacuously true;
* `conclusion_nontrivial`: the conclusion is a real restriction (`L²` does not satisfy the law with
  coefficients `0, 0`).

What this file does NOT prove, and what it does not constrain. The ledger is satisfiable whenever
the conclusion already holds (take the edge and face parts to be their model terms and put the rest of
`N` in the vertex part), because nothing ties the localized counts to cutoffs, traces or the Steklov
operator. So `theorem_11_1_of_inputs` certifies the Section 11.2 arithmetic and order of limits, and
fixes the exact shape of the six inputs; the content of each input lies in the PDE. The ledger does
encode that the vertex part, its area coefficient and the kept edge length are fixed by `ε` before
`γ` is chosen. What this file does NOT prove: any of `[H1]`–`[H6]` for the actual Steklov operator. No
Dirichlet-to-Neumann operator, Sobolev trace or partition of unity on the tetrahedron is defined.
Statement-level caveat: `dihedralCoeff` is a Bochner integral, which Mathlib sets to `0` when the
integrand is not integrable; integrability on `(0, ∞)` is NOT yet proved here (roadmap item C2).
-/

namespace SteklovAudit.MainConditional

open SteklovAudit MeasureTheory

/-- Weyl area coefficient of the regular tetrahedron of side `a`: `|∂T_a| / (4π) = √3 a² / (4π)`. -/
noncomputable def areaCoeff (a : ℝ) : ℝ := Real.sqrt 3 * a ^ 2 / (4 * Real.pi)

/-- The dihedral invariant (1.4): `c_α = (1/π) ∫₀^∞ sinh((π−α)v) / (cosh(πv) sinh(αv)) dv`.
See the module docstring for the integrability caveat. At `α = π/2` the integrand is `1/cosh(πv)`
(`SteklovAudit.right_angle_integrand`). -/
noncomputable def dihedralCoeff (α : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ v in Set.Ioi (0 : ℝ),
    Real.sinh ((Real.pi - α) * v) / (Real.cosh (Real.pi * v) * Real.sinh (α * v))

/-- The tetrahedral dihedral angle `α₀ = arccos(1/3)`. -/
noncomputable def tetraAngle : ℝ := Real.arccos (1 / 3)

/-- The vertex part of the partition; it depends on `ε` only (vertex radii are fixed first). -/
structure VertexPart where
  /-- vertex-localized count -/
  V : ℝ → ℝ
  /-- its area coefficient -/
  AV : ℝ
  /-- total edge length kept by the vertex cutoffs, `Σ_e ∫ q_e²` -/
  len : ℝ

/-- The edge and face parts at scales `(ε, γ)`. -/
structure EdgeFacePart where
  /-- edge-localized count -/
  E : ℝ → ℝ
  /-- face-localized count -/
  F : ℝ → ℝ
  /-- area coefficient of the edge collars -/
  AE : ℝ
  /-- area coefficient of the face interiors -/
  AF : ℝ

/-- The ledger of named hypotheses behind Theorem 11.1 (Section 11.2). -/
structure Thm111Inputs (N : ℝ → ℝ) (a c : ℝ) where
  vert : ℝ → VertexPart
  part : ℝ → ℝ → EdgeFacePart
  CL : ℝ
  CV : ℝ
  DE : ℝ → ℝ
  hCL : 0 ≤ CL
  hCV : 0 ≤ CV
  hDE : ∀ ε, 0 ≤ DE ε
  /-- [H1 splitting] trace linearity of the squared partition. -/
  splitting : ∀ ε γ L, N L = (vert ε).V L + (part ε γ).E L + (part ε γ).F L
  /-- [H2 area] the area terms add to `|∂T_a| / (4π)`. -/
  area : ∀ ε γ, (vert ε).AV + (part ε γ).AE + (part ε γ).AF = areaCoeff a
  /-- [H3 length] the edge length omitted by the vertex cutoffs is `O(ε)`. -/
  length : ∀ ε, 0 < ε → |(vert ε).len - 6 * a| ≤ CL * ε
  /-- [H4 vertex] (7.49). -/
  vertex : ∀ ε, 0 < ε → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |(vert ε).V L - (vert ε).AV * L ^ 2| ≤ (CV * ε + η) * L
  /-- [H5 edge] (11.3), fed by (7.29), (7.38)/(7.45), (9.1). -/
  edge : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |(part ε γ).E L - (part ε γ).AE * L ^ 2 - c * (vert ε).len * L| ≤ (DE ε * γ + η) * L
  /-- [H6 face] Lemma 7.4 with Section 10.2. -/
  face : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |(part ε γ).F L - (part ε γ).AF * L ^ 2| ≤ η * L

/-- The tetrahedral angle lies in `(0, π)`, so (1.4) is evaluated inside its range. -/
theorem tetraAngle_mem : 0 < tetraAngle ∧ tetraAngle < Real.pi := by
  unfold tetraAngle
  exact ⟨Real.arccos_pos.mpr (by norm_num), Real.arccos_lt_pi.mpr (by norm_num)⟩

/-- Four-term triangle inequality. -/
theorem abs_add_four_le (x y z w : ℝ) : |x + y + z + w| ≤ |x| + |y| + |z| + |w| := by
  have h1 := abs_add_le (x + y + z) w
  have h2 := abs_add_le (x + y) z
  have h3 := abs_add_le x y
  linarith

/-- Section 11.2 assembly: the ledger gives the uniform two-scale bound (11.5). -/
theorem two_scale_of_inputs (N : ℝ → ℝ) (a c : ℝ) (H : Thm111Inputs N a c) :
    HasRealTwoScaleBound N (areaCoeff a) (6 * a * c) := by
  refine ⟨H.CV + |c| * H.CL, add_nonneg H.hCV (mul_nonneg (abs_nonneg c) H.hCL), ?_⟩
  intro ε hε
  refine ⟨H.DE ε + 3, by linarith [H.hDE ε], ?_⟩
  intro γ hγ
  obtain ⟨L1, h1⟩ := H.vertex ε hε γ hγ
  obtain ⟨L2, h2⟩ := H.edge ε γ hε hγ γ hγ
  obtain ⟨L3, h3⟩ := H.face ε γ hε hγ γ hγ
  have hlen := H.length ε hε
  refine ⟨max (max L1 L2) (max L3 0), le_trans (le_max_right L3 0) (le_max_right _ _), ?_⟩
  intro L hL
  have hL1 : L1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : L2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL3 : L3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL0 : 0 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have e1 := h1 L hL1
  have e2 := h2 L hL2
  have e3 := h3 L hL3
  have hsplit := H.splitting ε γ L
  have harea := H.area ε γ
  have hid : N L - realWeylPolynomial (areaCoeff a) (6 * a * c) L =
      ((H.vert ε).V L - (H.vert ε).AV * L ^ 2)
        + ((H.part ε γ).E L - (H.part ε γ).AE * L ^ 2 - c * (H.vert ε).len * L)
        + ((H.part ε γ).F L - (H.part ε γ).AF * L ^ 2)
        + c * ((H.vert ε).len - 6 * a) * L := by
    rw [hsplit, ← harea]
    unfold realWeylPolynomial
    ring
  have e4 : |c * ((H.vert ε).len - 6 * a) * L| ≤ |c| * H.CL * ε * L := by
    rw [abs_mul, abs_mul, abs_of_nonneg hL0]
    have hm : |c| * |(H.vert ε).len - 6 * a| ≤ |c| * (H.CL * ε) :=
      mul_le_mul_of_nonneg_left hlen (abs_nonneg c)
    calc |c| * |(H.vert ε).len - 6 * a| * L ≤ |c| * (H.CL * ε) * L :=
          mul_le_mul_of_nonneg_right hm hL0
      _ = |c| * H.CL * ε * L := by ring
  have r1 : (H.CV * ε + γ) * L = H.CV * ε * L + γ * L := by ring
  have r2 : (H.DE ε * γ + γ) * L = H.DE ε * γ * L + γ * L := by ring
  have r3 : ((H.CV + |c| * H.CL) * ε + (H.DE ε + 3) * γ) * L =
      H.CV * ε * L + |c| * H.CL * ε * L + H.DE ε * γ * L + 3 * (γ * L) := by ring
  rw [hid, r3]
  refine le_trans (abs_add_four_le _ _ _ _) ?_
  linarith

/-- **Theorem 11.1 (conditional).** Under the ledger `Thm111Inputs`, the count satisfies
`N(L) = (√3 a² / 4π) L² + 6 a c L + o(L)`. -/
theorem theorem_11_1_of_inputs (N : ℝ → ℝ) (a c : ℝ) (H : Thm111Inputs N a c) :
    HasSharpRealLaw N (areaCoeff a) (6 * a * c) :=
  sharp_real_law_of_two_scale N (areaCoeff a) (6 * a * c) (two_scale_of_inputs N a c H)

/-- Formula (11.4) with the paper's constants, from the ledger. -/
theorem formula_11_4_of_inputs (N : ℝ → ℝ) (a : ℝ)
    (H : Thm111Inputs N a (dihedralCoeff tetraAngle)) :
    HasSharpRealLaw N (areaCoeff a) (6 * a * dihedralCoeff tetraAngle) :=
  theorem_11_1_of_inputs N a _ H

/-- Non-vacuity witness: the exact two-term count meets every hypothesis of the ledger. (This only
shows the ledger is consistent; see the module docstring for what it does not constrain.) -/
noncomputable def exactInputs (a c : ℝ) :
    Thm111Inputs (fun L => realWeylPolynomial (areaCoeff a) (6 * a * c) L) a c where
  vert := fun _ =>
    { V := fun L => areaCoeff a * L ^ 2
      AV := areaCoeff a
      len := 6 * a }
  part := fun _ _ =>
    { E := fun L => c * (6 * a) * L
      F := fun _ => 0
      AE := 0
      AF := 0 }
  CL := 0
  CV := 0
  DE := fun _ => 0
  hCL := le_refl 0
  hCV := le_refl 0
  hDE := fun _ => le_refl 0
  splitting := by
    intro ε γ L
    show realWeylPolynomial (areaCoeff a) (6 * a * c) L =
      areaCoeff a * L ^ 2 + c * (6 * a) * L + 0
    unfold realWeylPolynomial
    ring
  area := by
    intro ε γ
    show areaCoeff a + 0 + 0 = areaCoeff a
    ring
  length := by
    intro ε _
    show |6 * a - 6 * a| ≤ 0 * ε
    simp
  vertex := by
    intro ε _ η hη
    refine ⟨0, fun L hL => ?_⟩
    show |areaCoeff a * L ^ 2 - areaCoeff a * L ^ 2| ≤ (0 * ε + η) * L
    rw [sub_self, abs_zero]
    exact mul_nonneg (by linarith) hL
  edge := by
    intro ε γ _ _ η hη
    refine ⟨0, fun L hL => ?_⟩
    show |c * (6 * a) * L - 0 * L ^ 2 - c * (6 * a) * L| ≤ (0 * γ + η) * L
    rw [show c * (6 * a) * L - 0 * L ^ 2 - c * (6 * a) * L = 0 by ring, abs_zero]
    exact mul_nonneg (by linarith) hL
  face := by
    intro ε γ _ _ η hη
    refine ⟨0, fun L hL => ?_⟩
    show |(0 : ℝ) - 0 * L ^ 2| ≤ η * L
    rw [show (0 : ℝ) - 0 * L ^ 2 = 0 by ring, abs_zero]
    exact mul_nonneg hη.le hL

/-- Non-vacuity: the ledger can be satisfied, so `theorem_11_1_of_inputs` is not vacuous. -/
theorem nonvacuous (a c : ℝ) :
    HasSharpRealLaw (fun L => realWeylPolynomial (areaCoeff a) (6 * a * c) L)
      (areaCoeff a) (6 * a * c) :=
  theorem_11_1_of_inputs _ a c (exactInputs a c)

/-- The conclusion is a genuine restriction: `L²` does not obey the law with coefficients `0, 0`. -/
theorem conclusion_nontrivial : ¬ HasSharpRealLaw (fun L => L ^ 2) 0 0 := by
  intro h
  obtain ⟨L₀, hL₀, hL⟩ := h 1 one_pos
  have h2 : |(L₀ + 2) ^ 2 - realWeylPolynomial 0 0 (L₀ + 2)| ≤ 1 * (L₀ + 2) :=
    hL (L₀ + 2) (by linarith)
  have hp : realWeylPolynomial 0 0 (L₀ + 2) = 0 := by
    unfold realWeylPolynomial
    ring
  have h3 := le_abs_self ((L₀ + 2) ^ 2 - realWeylPolynomial 0 0 (L₀ + 2))
  nlinarith

end SteklovAudit.MainConditional
