import Mathlib
import SteklovAudit.PartitionTrace

/-!
# C6: `[H3 length]` from cutoff support lengths

Roadmap item C6. Each of the six edges of `T_a` is parametrized by `[0, a]`. For each `ε` and edge
`e`, `q2 ε e` is the squared vertex-kept edge profile `q_e²`: continuous, `0 ≤ q_e² ≤ 1` on
`[0, a]`, and `q_e² = 1` on `[Kε, a − Kε]` (the vertex cutoffs act only within distance `Kε` of
the endpoints). Proved here:

* `edge_integral_bounds`: `a − 2r ≤ ∫₀^a q² ≤ a` (for every `r ≥ 0`, also when `2r > a`);
* `six_edge_length`: six such edges give `|Σ_e ∫ q_e² − 6a| ≤ 12 r`;
* `length_bound`: `|len ε − 6a| ≤ 12 K ε`, i.e. `[H3 length]` with `CL = 12 K`;
* the ledger `Thm111InputsC6`, in which `[H1]`, `[H2]` (from C5) and `[H3]` are theorems;
  `toC5` and `theorem_11_1_of_C6`.

What this file does NOT prove: that the paper's vertex cutoffs have these support properties, or
that the edge profiles `q2` are the restrictions of the discrete cutoffs `qE` (this link is not
encoded, as in C5 nothing ties the cutoffs to the Steklov operator). `[H4]`–`[H6]` are restated
unchanged. It does not prove the main theorem. The hypothesis count in STATUS.md (taken from
`MainConditional.lean`) is not changed.
-/

namespace SteklovAudit.EdgeLength

open SteklovAudit SteklovAudit.MainConditional SteklovAudit.PartitionTrace

/-- One edge: `a − 2r ≤ ∫₀^a f ≤ a` when `0 ≤ f ≤ 1` on `[0, a]` and `f = 1` on `[r, a − r]`. -/
theorem edge_integral_bounds (f : ℝ → ℝ) (a r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hf : Continuous f) (h0 : ∀ x ∈ Set.Icc 0 a, 0 ≤ f x) (h1 : ∀ x ∈ Set.Icc 0 a, f x ≤ 1)
    (hone : ∀ x ∈ Set.Icc r (a - r), f x = 1) :
    a - 2 * r ≤ ∫ x in (0:ℝ)..a, f x ∧ ∫ x in (0:ℝ)..a, f x ≤ a := by
  have hT0 : 0 ≤ ∫ x in (0:ℝ)..a, f x := intervalIntegral.integral_nonneg ha h0
  have hT1 : ∫ x in (0:ℝ)..a, f x ≤ ∫ x in (0:ℝ)..a, (1:ℝ) :=
    intervalIntegral.integral_mono_on ha (hf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) h1
  have hc : ∫ x in (0:ℝ)..a, (1:ℝ) = a := by
    first | simp | norm_num [intervalIntegral.integral_const]
  refine ⟨?_, by linarith⟩
  by_cases hra : 2 * r ≤ a
  · have hrr : r ≤ a - r := by linarith
    have e1 : (∫ x in (0:ℝ)..r, f x) + (∫ x in r..(a - r), f x) = ∫ x in (0:ℝ)..(a - r), f x :=
      intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _)
    have e2 : (∫ x in (0:ℝ)..(a - r), f x) + (∫ x in (a - r)..a, f x) = ∫ x in (0:ℝ)..a, f x :=
      intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _)
    have hA : 0 ≤ ∫ x in (0:ℝ)..r, f x :=
      intervalIntegral.integral_nonneg hr (fun x hx => h0 x ⟨hx.1, by linarith [hx.2]⟩)
    have hC : 0 ≤ ∫ x in (a - r)..a, f x :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun x hx => h0 x ⟨by linarith [hx.1], hx.2⟩)
    have hEq : Set.EqOn f (fun _ => (1:ℝ)) (Set.uIcc r (a - r)) := by
      intro x hx
      rw [Set.uIcc_of_le hrr] at hx
      exact hone x hx
    have hB : ∫ x in r..(a - r), f x = a - 2 * r := by
      rw [intervalIntegral.integral_congr hEq]
      first
        | (simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring)
        | (simp; ring)
        | simp
        | norm_num
    linarith
  · linarith

/-- Six edges: `|Σ_e I_e − 6a| ≤ 12 r` when each `a − 2r ≤ I_e ≤ a`. -/
theorem six_edge_length (I : Fin 6 → ℝ) (a r : ℝ) (hb : ∀ e, a - 2 * r ≤ I e ∧ I e ≤ a) :
    |(∑ e, I e) - 6 * a| ≤ 12 * r := by
  have hlo : ∑ _e : Fin 6, (a - 2 * r) ≤ ∑ e, I e := Finset.sum_le_sum (fun e _ => (hb e).1)
  have hhi : ∑ e, I e ≤ ∑ _e : Fin 6, a := Finset.sum_le_sum (fun e _ => (hb e).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlo hhi
  try push_cast at hlo hhi
  rw [abs_le]
  constructor <;> linarith

/-- Squared vertex-kept edge profiles with support defect `Kε` at each endpoint. -/
structure EdgeCutoffs (a : ℝ) where
  K : ℝ
  hK : 0 ≤ K
  /-- `q2 ε e x = q_e(x)²` at scale `ε`, edge `e`, arclength `x ∈ [0, a]` -/
  q2 : ℝ → Fin 6 → ℝ → ℝ
  cont : ∀ ε e, Continuous (q2 ε e)
  nonneg : ∀ ε e, ∀ x ∈ Set.Icc 0 a, 0 ≤ q2 ε e x
  le_one : ∀ ε e, ∀ x ∈ Set.Icc 0 a, q2 ε e x ≤ 1
  one_mid : ∀ ε e, ∀ x ∈ Set.Icc (K * ε) (a - K * ε), q2 ε e x = 1

/-- Kept edge length `Σ_e ∫₀^a q_e²`. -/
noncomputable def EdgeCutoffs.len {a : ℝ} (C : EdgeCutoffs a) (ε : ℝ) : ℝ :=
  ∑ e : Fin 6, ∫ x in (0:ℝ)..a, C.q2 ε e x

/-- `[H3 length]` with `CL = 12 K`. -/
theorem length_bound {a : ℝ} (C : EdgeCutoffs a) (ha : 0 ≤ a) (ε : ℝ) (hε : 0 < ε) :
    |C.len ε - 6 * a| ≤ 12 * C.K * ε := by
  have hr : 0 ≤ C.K * ε := mul_nonneg C.hK hε.le
  have h := six_edge_length (fun e => ∫ x in (0:ℝ)..a, C.q2 ε e x) a (C.K * ε)
    (fun e => edge_integral_bounds (C.q2 ε e) a (C.K * ε) ha hr (C.cont ε e) (C.nonneg ε e)
      (C.le_one ε e) (C.one_mid ε e))
  have h2 : 12 * (C.K * ε) = 12 * C.K * ε := by ring
  rw [← h2]
  exact h

/-- Ledger with `[H1]`, `[H2]`, `[H3]` derived; H4–H6 unchanged. -/
structure Thm111InputsC6 (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℝ → ℝ) (a c : ℝ) where
  P : ℝ → Matrix ι ι ℝ
  w : ι → ℝ
  qV : ℝ → ι → ℝ
  qE : ℝ → ℝ → ι → ℝ
  qF : ℝ → ℝ → ι → ℝ
  cut : EdgeCutoffs a
  ha : 0 ≤ a
  CV : ℝ
  DE : ℝ → ℝ
  hCV : 0 ≤ CV
  hDE : ∀ ε, 0 ≤ DE ε
  count : ∀ L, N L = Matrix.trace (P L)
  sq_sum : ∀ ε γ i, qV ε i ^ 2 + qE ε γ i ^ 2 + qF ε γ i ^ 2 = 1
  wsum : ∑ i, w i = Real.sqrt 3 * a ^ 2
  /-- H4 vertex (unchanged). -/
  vertex : ∀ ε, 0 < ε → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |loc P (qV ε) L - areaOf w (qV ε) * L ^ 2| ≤ (CV * ε + η) * L
  /-- H5 edge (unchanged). -/
  edge : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |loc P (qE ε γ) L - areaOf w (qE ε γ) * L ^ 2 - c * cut.len ε * L| ≤ (DE ε * γ + η) * L
  /-- H6 face (unchanged). -/
  face : ∀ ε γ, 0 < ε → 0 < γ → ∀ η, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |loc P (qF ε γ) L - areaOf w (qF ε γ) * L ^ 2| ≤ η * L

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The C6 ledger yields the C5 ledger: `[H3]` is now a theorem. -/
noncomputable def toC5 {N : ℝ → ℝ} {a c : ℝ} (H : Thm111InputsC6 n N a c) :
    Thm111InputsC5 n N a c where
  P := H.P
  w := H.w
  qV := H.qV
  qE := H.qE
  qF := H.qF
  len := H.cut.len
  CL := 12 * H.cut.K
  CV := H.CV
  DE := H.DE
  hCL := by have := H.cut.hK; linarith
  hCV := H.hCV
  hDE := H.hDE
  count := H.count
  sq_sum := H.sq_sum
  wsum := H.wsum
  length := length_bound H.cut H.ha
  vertex := H.vertex
  edge := H.edge
  face := H.face

/-- **Theorem 11.1 (conditional), C6 ledger.** -/
theorem theorem_11_1_of_C6 (N : ℝ → ℝ) (a c : ℝ) (H : Thm111InputsC6 n N a c) :
    HasSharpRealLaw N (areaCoeff a) (6 * a * c) :=
  theorem_11_1_of_C5 N a c (toC5 H)

end SteklovAudit.EdgeLength
