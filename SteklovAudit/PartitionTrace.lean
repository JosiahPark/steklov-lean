import Mathlib
import SteklovAudit.MainConditional

/-!
# C5: `[H1 splitting]` and `[H2 area]` from a finite squared partition

Roadmap item C5. In spectral coordinates at a finite cutoff (index type `n`), let `P L` be any
square matrix (the spectral projection `1_[0,L]` in the intended use) and let `q₁, …` be diagonal
cutoffs with `Σ_k q_k(i)² = 1`. Proved here:

* `diag_conj_entry`: `(D_q P D_q)_{ii} = q_i² P_{ii}`;
* `trace_squared_partition`: `Tr P = Σ_k Tr(D_{χ_k} P D_{χ_k})` when `Σ_k χ_k² = 1`;
* `trace_split3`: the three-piece (vertex / edge / face) version;
* `area_additive`: with boundary weights `w` summing to `|∂T_a| = √3 a²`, the area coefficients
  `A(q) = (Σ_i w_i q_i²) / (4π)` of the three pieces add to `areaCoeff a`;
* the ledger `Thm111InputsC5`, in which `[H1]` and `[H2]` are no longer hypotheses but follow
  from a `count` identity `N L = Tr (P L)`, the squared-partition identity and the weight sum;
  `toLedger` and `theorem_11_1_of_C5`.

What this file does NOT prove: that `P L` is a spectral projection of the Dirichlet-to-Neumann
operator, that the finite cutoff approximates the true count, that the discrete area weights
approximate surface measure, or any of `[H3]`–`[H6]` (restated unchanged, in terms of the
localized traces). It does not prove the main theorem. The hypothesis count in STATUS.md (taken
from `MainConditional.lean`) is not changed.
-/

namespace SteklovAudit.PartitionTrace

open SteklovAudit SteklovAudit.MainConditional

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Diagonal entries of a diagonal conjugation. -/
theorem diag_conj_entry (d : n → ℝ) (P : Matrix n n ℝ) (i : n) :
    (Matrix.diagonal d * P * Matrix.diagonal d) i i = d i ^ 2 * P i i := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- Trace linearity of a squared partition: `Tr P = Σ_k Tr(χ_k P χ_k)` when `Σ_k χ_k² = 1`. -/
theorem trace_squared_partition {κ : Type*} [Fintype κ] (P : Matrix n n ℝ) (χ : κ → n → ℝ)
    (h : ∀ i, ∑ k, χ k i ^ 2 = 1) :
    Matrix.trace P =
      ∑ k, Matrix.trace (Matrix.diagonal (χ k) * P * Matrix.diagonal (χ k)) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, diag_conj_entry]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_mul, h i, one_mul]

/-- Three-piece (vertex / edge / face) trace splitting. -/
theorem trace_split3 (M : Matrix n n ℝ) (q1 q2 q3 : n → ℝ)
    (h : ∀ i, q1 i ^ 2 + q2 i ^ 2 + q3 i ^ 2 = 1) :
    Matrix.trace M =
      Matrix.trace (Matrix.diagonal q1 * M * Matrix.diagonal q1)
        + Matrix.trace (Matrix.diagonal q2 * M * Matrix.diagonal q2)
        + Matrix.trace (Matrix.diagonal q3 * M * Matrix.diagonal q3) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, diag_conj_entry]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  linear_combination (-(M i i)) * h i

/-- Localized count `Tr(D_q P(L) D_q)`. -/
noncomputable def loc (P : ℝ → Matrix n n ℝ) (q : n → ℝ) (L : ℝ) : ℝ :=
  Matrix.trace (Matrix.diagonal q * P L * Matrix.diagonal q)

/-- Discrete area coefficient `(Σ_i w_i q_i²) / (4π)` of a cutoff `q`. -/
noncomputable def areaOf (w q : n → ℝ) : ℝ := (∑ i, w i * q i ^ 2) / (4 * Real.pi)

/-- Additivity of the area coefficients over a squared partition. -/
theorem area_additive (a : ℝ) (w q1 q2 q3 : n → ℝ)
    (h : ∀ i, q1 i ^ 2 + q2 i ^ 2 + q3 i ^ 2 = 1) (hw : ∑ i, w i = Real.sqrt 3 * a ^ 2) :
    areaOf w q1 + areaOf w q2 + areaOf w q3 = areaCoeff a := by
  have hs : ∑ i, w i * q1 i ^ 2 + ∑ i, w i * q2 i ^ 2 + ∑ i, w i * q3 i ^ 2 = ∑ i, w i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by linear_combination (w i) * h i)
  unfold areaOf areaCoeff
  rw [← hw, ← hs]
  ring

/-- Ledger with `[H1]`, `[H2]` derived from a finite squared partition; H3–H6 unchanged. -/
structure Thm111InputsC5 (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℝ → ℝ) (a c : ℝ) where
  P : ℝ → Matrix ι ι ℝ
  w : ι → ℝ
  qV : ℝ → ι → ℝ
  qE : ℝ → ℝ → ι → ℝ
  qF : ℝ → ℝ → ι → ℝ
  len : ℝ → ℝ
  CL : ℝ
  CV : ℝ
  DE : ℝ → ℝ
  hCL : 0 ≤ CL
  hCV : 0 ≤ CV
  hDE : ∀ ε, 0 ≤ DE ε
  /-- the count is the trace of `P L` -/
  count : ∀ L, N L = Matrix.trace (P L)
  /-- squared partition of unity -/
  sq_sum : ∀ ε γ i, qV ε i ^ 2 + qE ε γ i ^ 2 + qF ε γ i ^ 2 = 1
  /-- boundary weights sum to `|∂T_a|` -/
  wsum : ∑ i, w i = Real.sqrt 3 * a ^ 2
  /-- H3 length (unchanged). -/
  length : ∀ ε, 0 < ε → |len ε - 6 * a| ≤ CL * ε
  /-- H4 vertex (unchanged). -/
  vertex : ∀ ε, 0 < ε → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |loc P (qV ε) L - areaOf w (qV ε) * L ^ 2| ≤ (CV * ε + η) * L
  /-- H5 edge (unchanged). -/
  edge : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |loc P (qE ε γ) L - areaOf w (qE ε γ) * L ^ 2 - c * len ε * L| ≤ (DE ε * γ + η) * L
  /-- H6 face (unchanged). -/
  face : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |loc P (qF ε γ) L - areaOf w (qF ε γ) * L ^ 2| ≤ η * L

/-- The C5 ledger yields the original ledger: `[H1]` and `[H2]` are now theorems. -/
noncomputable def toLedger {N : ℝ → ℝ} {a c : ℝ} (H : Thm111InputsC5 n N a c) :
    Thm111Inputs N a c where
  vert := fun ε => { V := loc H.P (H.qV ε), AV := areaOf H.w (H.qV ε), len := H.len ε }
  part := fun ε γ =>
    { E := loc H.P (H.qE ε γ), F := loc H.P (H.qF ε γ)
      AE := areaOf H.w (H.qE ε γ), AF := areaOf H.w (H.qF ε γ) }
  CL := H.CL
  CV := H.CV
  DE := H.DE
  hCL := H.hCL
  hCV := H.hCV
  hDE := H.hDE
  splitting := by
    intro ε γ L
    rw [H.count L]
    exact trace_split3 (H.P L) (H.qV ε) (H.qE ε γ) (H.qF ε γ) (H.sq_sum ε γ)
  area := by
    intro ε γ
    exact area_additive a H.w (H.qV ε) (H.qE ε γ) (H.qF ε γ) (H.sq_sum ε γ) H.wsum
  length := H.length
  vertex := H.vertex
  edge := H.edge
  face := H.face

/-- **Theorem 11.1 (conditional), C5 ledger.** -/
theorem theorem_11_1_of_C5 (N : ℝ → ℝ) (a c : ℝ) (H : Thm111InputsC5 n N a c) :
    HasSharpRealLaw N (areaCoeff a) (6 * a * c) :=
  theorem_11_1_of_inputs N a c (toLedger H)

end SteklovAudit.PartitionTrace
