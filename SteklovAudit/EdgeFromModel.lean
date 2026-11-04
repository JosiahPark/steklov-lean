import Mathlib
import SteklovAudit.MainConditional

/-!
# C4: `[H5 edge]` from a model edge law and a cumulative comparison

Roadmap item C4. The ledger hypothesis `[H5 edge]` of `MainConditional.lean` (the edge part obeys
(11.3)) is split into two strictly narrower named inputs, as in Section 7 of the paper:

* `model`   (7.38)/(7.45): a model edge count `Emod ε γ` (the wedge model) satisfies the edge law
  with error `(DE ε · γ + η) L` for `L` large;
* `compare` (7.29), the output of the abstract layer B4/B5: the true edge-localized count differs
  from the model count by `o(L)`.

Proved here: `edge_of_model_compare` (the two inputs imply `[H5 edge]`), the ledger
`Thm111InputsC4` (H1–H4, H6 unchanged, H5 replaced by `model` + `compare`), its conversion to
`Thm111Inputs`, the converse `ofLedger` (so the split loses nothing), Theorem 11.1 / (11.4) from
the new ledger, and its non-vacuity.

What this file does NOT prove: the model edge law (7.38)/(7.45) for the wedge Steklov problem, the
comparison (7.29) for the actual Steklov operator (B4/B5 prove it only from the named inputs
`PDEInputs` and a tail hypothesis), or any other ledger entry. It does not prove the main theorem.
The hypothesis count printed in STATUS.md (taken from `MainConditional.lean`) is not changed.
-/

namespace SteklovAudit.EdgeFromModel

open SteklovAudit SteklovAudit.MainConditional

/-- Model law plus `o(L)` comparison implies the edge law (11.3). -/
theorem edge_of_model_compare (E Emod : ℝ → ℝ → ℝ → ℝ) (AE : ℝ → ℝ → ℝ) (len DE : ℝ → ℝ)
    (c : ℝ)
    (model : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      |Emod ε γ L - AE ε γ * L ^ 2 - c * len ε * L| ≤ (DE ε * γ + η) * L)
    (compare : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      |E ε γ L - Emod ε γ L| ≤ η * L) :
    ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      |E ε γ L - AE ε γ * L ^ 2 - c * len ε * L| ≤ (DE ε * γ + η) * L := by
  intro ε γ hε hγ η hη
  obtain ⟨L1, h1⟩ := model ε γ hε hγ (η / 2) (half_pos hη)
  obtain ⟨L2, h2⟩ := compare ε γ hε hγ (η / 2) (half_pos hη)
  refine ⟨max L1 L2, fun L hL => ?_⟩
  have e1 := h1 L (le_trans (le_max_left _ _) hL)
  have e2 := h2 L (le_trans (le_max_right _ _) hL)
  have hid : E ε γ L - AE ε γ * L ^ 2 - c * len ε * L =
      (E ε γ L - Emod ε γ L) + (Emod ε γ L - AE ε γ * L ^ 2 - c * len ε * L) := by ring
  have hsplit : (DE ε * γ + η) * L = η / 2 * L + (DE ε * γ + η / 2) * L := by ring
  rw [hid, hsplit]
  exact le_trans (abs_add_le _ _) (add_le_add e2 e1)

/-- The ledger of `MainConditional.lean` with `[H5 edge]` replaced by `model` and `compare`. -/
structure Thm111InputsC4 (N : ℝ → ℝ) (a c : ℝ) where
  vert : ℝ → VertexPart
  part : ℝ → ℝ → EdgeFacePart
  CL : ℝ
  CV : ℝ
  DE : ℝ → ℝ
  hCL : 0 ≤ CL
  hCV : 0 ≤ CV
  hDE : ∀ ε, 0 ≤ DE ε
  /-- H1 splitting (unchanged). -/
  splitting : ∀ ε γ L, N L = (vert ε).V L + (part ε γ).E L + (part ε γ).F L
  /-- H2 area (unchanged). -/
  area : ∀ ε γ, (vert ε).AV + (part ε γ).AE + (part ε γ).AF = areaCoeff a
  /-- H3 length (unchanged). -/
  length : ∀ ε, 0 < ε → |(vert ε).len - 6 * a| ≤ CL * ε
  /-- H4 vertex (unchanged). -/
  vertex : ∀ ε, 0 < ε → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |(vert ε).V L - (vert ε).AV * L ^ 2| ≤ (CV * ε + η) * L
  /-- H6 face (unchanged). -/
  face : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |(part ε γ).F L - (part ε γ).AF * L ^ 2| ≤ η * L
  /-- The model (wedge) edge count at scales `(ε, γ)`. -/
  Emod : ℝ → ℝ → ℝ → ℝ
  /-- H5a model edge law (7.38)/(7.45). -/
  model : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |Emod ε γ L - (part ε γ).AE * L ^ 2 - c * (vert ε).len * L| ≤ (DE ε * γ + η) * L
  /-- H5b cumulative comparison (7.29), `o(L)`; the target of the B4/B5 layer. -/
  compare : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |(part ε γ).E L - Emod ε γ L| ≤ η * L

/-- The new ledger yields the old one: `[H5 edge]` is now a theorem. -/
noncomputable def toLedger {N : ℝ → ℝ} {a c : ℝ} (H : Thm111InputsC4 N a c) :
    Thm111Inputs N a c where
  vert := H.vert
  part := H.part
  CL := H.CL
  CV := H.CV
  DE := H.DE
  hCL := H.hCL
  hCV := H.hCV
  hDE := H.hDE
  splitting := H.splitting
  area := H.area
  length := H.length
  vertex := H.vertex
  edge := edge_of_model_compare (fun ε γ L => (H.part ε γ).E L) H.Emod
    (fun ε γ => (H.part ε γ).AE) (fun ε => (H.vert ε).len) H.DE c H.model H.compare
  face := H.face

/-- Converse: any old ledger gives a new one (take `Emod = E`), so the split loses nothing. -/
noncomputable def ofLedger {N : ℝ → ℝ} {a c : ℝ} (H : Thm111Inputs N a c) :
    Thm111InputsC4 N a c where
  vert := H.vert
  part := H.part
  CL := H.CL
  CV := H.CV
  DE := H.DE
  hCL := H.hCL
  hCV := H.hCV
  hDE := H.hDE
  splitting := H.splitting
  area := H.area
  length := H.length
  vertex := H.vertex
  face := H.face
  Emod := fun ε γ L => (H.part ε γ).E L
  model := H.edge
  compare := by
    intro ε γ _ _ η hη
    refine ⟨0, fun L hL => ?_⟩
    show |(H.part ε γ).E L - (H.part ε γ).E L| ≤ η * L
    rw [sub_self, abs_zero]
    exact mul_nonneg hη.le hL

/-- **Theorem 11.1 (conditional), C4 ledger.** -/
theorem theorem_11_1_of_C4 (N : ℝ → ℝ) (a c : ℝ) (H : Thm111InputsC4 N a c) :
    HasSharpRealLaw N (areaCoeff a) (6 * a * c) :=
  theorem_11_1_of_inputs N a c (toLedger H)

/-- Formula (11.4) with the paper's constants, from the C4 ledger. -/
theorem formula_11_4_of_C4 (N : ℝ → ℝ) (a : ℝ)
    (H : Thm111InputsC4 N a (dihedralCoeff tetraAngle)) :
    HasSharpRealLaw N (areaCoeff a) (6 * a * dihedralCoeff tetraAngle) :=
  theorem_11_1_of_C4 N a _ H

/-- Non-vacuity of the C4 ledger. -/
theorem nonvacuous_C4 (a c : ℝ) :
    HasSharpRealLaw (fun L => realWeylPolynomial (areaCoeff a) (6 * a * c) L)
      (areaCoeff a) (6 * a * c) :=
  theorem_11_1_of_C4 _ a c (ofLedger (exactInputs a c))

end SteklovAudit.EdgeFromModel
