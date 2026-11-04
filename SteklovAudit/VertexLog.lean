import Mathlib
import SteklovAudit.EdgeLength

/-!
# D5: `[H4 vertex]` from the explicit form of (7.49)

Roadmap item D5. `MainConditional` states `[H4 vertex]` with an `o(L)` remainder, and its docstring
says that `o(L)` absorbs the `O(log L) + O(1)` terms of (7.49). This file proves that absorption:

* `log_le_two_sqrt`: `log L ≤ 2√L` for `L > 0`;
* `vertex_of_log`: a vertex bound of the form (7.49),
  `|V(L) − A_V L²| ≤ C_V ε L + K (log L + 1)` for `L ≥ 1`, implies the `[H4]` form
  `∀ η > 0, ∃ L₀, ∀ L ≥ L₀, |V(L) − A_V L²| ≤ (C_V ε + η) L`;
* the ledger `Thm111InputsD5`: the C6 ledger with `[H4]` replaced by the (7.49) form with an
  `ε`-dependent constant `K(ε)`; `toC6` and `theorem_11_1_of_D5`.

This is a restatement in the paper's form, not a weakening: the (7.49) form implies the `[H4]` form,
so the new input is at least as strong. Its value is that the ledger now asks for exactly what
(7.49) states. What this file does NOT prove: (7.49) itself, or any of `[H5]`, `[H6]`; it does not
prove the main theorem (Theorem 1.3 / 11.1). The hypothesis count in STATUS.md is not changed.
-/

namespace SteklovAudit.VertexLog

open SteklovAudit SteklovAudit.MainConditional SteklovAudit.PartitionTrace SteklovAudit.EdgeLength

/-- `log L ≤ 2√L` for `L > 0`. -/
theorem log_le_two_sqrt (L : ℝ) (hL : 0 < L) : Real.log L ≤ 2 * Real.sqrt L := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have h1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log L = Real.log (Real.sqrt L) + Real.log (Real.sqrt L) := by
    rw [← Real.log_mul hs.ne' hs.ne', Real.mul_self_sqrt hL.le]
  linarith

/-- D5. The (7.49) form of the vertex bound implies the `[H4 vertex]` form. -/
theorem vertex_of_log (V : ℝ → ℝ) (AV CV K ε : ℝ) (hK : 0 ≤ K)
    (h : ∀ L, 1 ≤ L → |V L - AV * L ^ 2| ≤ CV * ε * L + K * (Real.log L + 1)) :
    ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |V L - AV * L ^ 2| ≤ (CV * ε + η) * L := by
  intro η hη
  have hη0 : η ≠ 0 := hη.ne'
  have hM0 : 0 ≤ 3 * K / η := div_nonneg (by linarith) hη.le
  refine ⟨max 1 ((3 * K / η) ^ 2), fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLM : (3 * K / η) ^ 2 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := by linarith
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hs1 : 1 ≤ Real.sqrt L := by
    have h1 := Real.sqrt_le_sqrt hL1
    rwa [Real.sqrt_one] at h1
  have hsM : 3 * K / η ≤ Real.sqrt L := by
    have h1 := Real.sqrt_le_sqrt hLM
    rwa [Real.sqrt_sq hM0] at h1
  have hlog := log_le_two_sqrt L hLpos
  have hηM : η * (3 * K / η) = 3 * K := by
    first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [mul_div_assoc', mul_div_cancel_left₀ (3 * K) hη0])
  have h3K : 3 * K ≤ η * Real.sqrt L := by
    have h1 := mul_le_mul_of_nonneg_left hsM hη.le
    linarith
  have hKlog : K * (Real.log L + 1) ≤ 3 * K * Real.sqrt L := by
    have h1 : Real.log L + 1 ≤ 3 * Real.sqrt L := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hK
    linarith
  have hfin : 3 * K * Real.sqrt L ≤ η * L := by
    have h1 := mul_le_mul_of_nonneg_right h3K hs
    calc 3 * K * Real.sqrt L ≤ η * Real.sqrt L * Real.sqrt L := h1
      _ = η * L := by rw [mul_assoc, hss]
  have e := h L hL1
  calc |V L - AV * L ^ 2| ≤ CV * ε * L + K * (Real.log L + 1) := e
    _ ≤ CV * ε * L + η * L := by linarith
    _ = (CV * ε + η) * L := by ring

/-- Ledger with `[H1]`–`[H3]` derived (C5, C6) and `[H4]` in the (7.49) form; H5, H6 unchanged. -/
structure Thm111InputsD5 (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℝ → ℝ) (a c : ℝ) where
  P : ℝ → Matrix ι ι ℝ
  w : ι → ℝ
  qV : ℝ → ι → ℝ
  qE : ℝ → ℝ → ι → ℝ
  qF : ℝ → ℝ → ι → ℝ
  cut : EdgeCutoffs a
  ha : 0 ≤ a
  CV : ℝ
  KV : ℝ → ℝ
  DE : ℝ → ℝ
  hCV : 0 ≤ CV
  hKV : ∀ ε, 0 ≤ KV ε
  hDE : ∀ ε, 0 ≤ DE ε
  count : ∀ L, N L = Matrix.trace (P L)
  sq_sum : ∀ ε γ i, qV ε i ^ 2 + qE ε γ i ^ 2 + qF ε γ i ^ 2 = 1
  wsum : ∑ i, w i = Real.sqrt 3 * a ^ 2
  /-- H4 vertex in the form (7.49): `O(εL) + O_ε(log L) + O_ε(1)`. -/
  vertex : ∀ ε, 0 < ε → ∀ L, 1 ≤ L →
    |loc P (qV ε) L - areaOf w (qV ε) * L ^ 2| ≤ CV * ε * L + KV ε * (Real.log L + 1)
  /-- H5 edge (unchanged). -/
  edge : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |loc P (qE ε γ) L - areaOf w (qE ε γ) * L ^ 2 - c * cut.len ε * L| ≤ (DE ε * γ + η) * L
  /-- H6 face (unchanged). -/
  face : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |loc P (qF ε γ) L - areaOf w (qF ε γ) * L ^ 2| ≤ η * L

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The D5 ledger yields the C6 ledger. -/
noncomputable def toC6 {N : ℝ → ℝ} {a c : ℝ} (H : Thm111InputsD5 n N a c) :
    Thm111InputsC6 n N a c where
  P := H.P
  w := H.w
  qV := H.qV
  qE := H.qE
  qF := H.qF
  cut := H.cut
  ha := H.ha
  CV := H.CV
  DE := H.DE
  hCV := H.hCV
  hDE := H.hDE
  count := H.count
  sq_sum := H.sq_sum
  wsum := H.wsum
  vertex := fun ε hε =>
    vertex_of_log (loc H.P (H.qV ε)) (areaOf H.w (H.qV ε)) H.CV (H.KV ε) ε (H.hKV ε)
      (H.vertex ε hε)
  edge := H.edge
  face := H.face

/-- **Theorem 11.1 (conditional), D5 ledger.** -/
theorem theorem_11_1_of_D5 (N : ℝ → ℝ) (a c : ℝ) (H : Thm111InputsD5 n N a c) :
    HasSharpRealLaw N (areaCoeff a) (6 * a * c) :=
  theorem_11_1_of_C6 N a c (toC6 H)

end SteklovAudit.VertexLog
