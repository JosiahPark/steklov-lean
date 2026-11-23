import Mathlib
import SteklovAudit.TraceLocalMassGrowth

/-!
# G147: definition check for the growth inputs of G145

Roadmap item G147 (priority row 3, definition check). Finding: the hypotheses of
`TraceLocalMassGrowth.trace_littleO_of_growth` are degenerate. Its local-mass input
`hJ : ∀ L, hs2 (D L).J ≤ Mloc * L` is required for EVERY real `L`, including `L < 0`, which forces
`Mloc = 0` (`growth_hJ_forces_Mloc_zero`), then `J = 0` at every scale
(`growth_hJ_forces_J_zero`), so the trace comparison is identically `0`
(`growth_trace_zero`). The theorem is true but says nothing about nonzero data.

Repair (a new theorem, the old one is untouched): `trace_littleO_of_growth_pos` asks for the
defect and local-mass inputs only for `0 < L`. The witness `wD` on `Fin 1 × Fin 1`
(`a = 1/L`, `b = 0`, `J = √L`, `f = id`, `Lf = 1`, `ε = 1/√L`, `Mloc = 1`) meets all its
hypotheses with NONZERO defect `hs2 K = 1/L` and trace comparison `= 1`
(`growth_inputs_nonvacuous`, `witness_littleO`).

F table text: the growth inputs (stated for `L > 0`) are consistent with a nonzero defect.

What this file does NOT prove:
* No defect, local-mass or rate bound is proved for any operator; no Dirichlet-to-Neumann
  operator is constructed. The witness is a one-entry toy array.
* Nothing here proves Lemma 7.1′, τ(M), κ(M), Prop. 7.3, (7.29), any of H1–H6, or
  Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.GrowthInputsWitness

open SteklovAudit.AbstractTransfer SteklovAudit.TraceLocalMass SteklovAudit.TraceLocalMassGrowth

section Finding

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G147 finding.** The all-`L` local-mass input of `trace_littleO_of_growth` forces `Mloc = 0`. -/
theorem growth_hJ_forces_Mloc_zero (D : ℝ → Data ι κ) (Mloc : ℝ) (hM : 0 ≤ Mloc)
    (hJ : ∀ L, hs2 (D L).J ≤ Mloc * L) : Mloc = 0 := by
  have h := hJ (-1)
  have h0 := hs2_nonneg (D (-1)).J
  linarith

/-- **G147 finding.** Hence every coefficient `J i j` vanishes at every scale. -/
theorem growth_hJ_forces_J_zero (D : ℝ → Data ι κ) (Mloc : ℝ) (hM : 0 ≤ Mloc)
    (hJ : ∀ L, hs2 (D L).J ≤ Mloc * L) (L : ℝ) (i : ι) (j : κ) : (D L).J i j = 0 := by
  have hM0 := growth_hJ_forces_Mloc_zero D Mloc hM hJ
  have h := hJ L
  rw [hM0, zero_mul] at h
  have hle : (D L).J i j ^ 2 ≤ hs2 (D L).J := by
    unfold hs2
    calc (D L).J i j ^ 2 ≤ ∑ j', (D L).J i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => (D L).J i j' ^ 2)
            (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (D L).J i' j' ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', (D L).J i' j' ^ 2)
            (fun i' _ => Finset.sum_nonneg (fun j' _ => sq_nonneg _)) (Finset.mem_univ i)
  have h2 : (D L).J i j ^ 2 = 0 := le_antisymm (le_trans hle h) (sq_nonneg _)
  first
  | simpa using h2
  | exact (pow_eq_zero_iff two_ne_zero).mp h2
  | nlinarith [sq_nonneg ((D L).J i j)]

/-- **G147 finding.** So the trace comparison in `trace_littleO_of_growth` is identically `0`. -/
theorem growth_trace_zero (D : ℝ → Data ι κ) (f : ℝ → ℝ → ℝ) (Mloc : ℝ) (hM : 0 ≤ Mloc)
    (hJ : ∀ L, hs2 (D L).J ≤ Mloc * L) (L : ℝ) :
    ∑ i, ∑ j, (f L ((D L).a i) - f L ((D L).b j)) * (D L).J i j ^ 2 = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [growth_hJ_forces_J_zero D Mloc hM hJ L i j]
  ring

/-- **G147 repair.** `trace_littleO_of_growth` with the defect and local-mass inputs asked
only for `0 < L`. All inputs are named hypotheses. -/
theorem trace_littleO_of_growth_pos (D : ℝ → Data ι κ) (f : ℝ → ℝ → ℝ) (Lf ε : ℝ → ℝ)
    (Mloc : ℝ) (hLf : ∀ L, 0 ≤ Lf L) (hf : ∀ L x y, |f L x - f L y| ≤ Lf L * |x - y|)
    (hε : ∀ L, 0 ≤ ε L) (hM : 0 ≤ Mloc)
    (hK : ∀ L, 0 < L → hs2 (D L).K ≤ ε L ^ 2) (hJ : ∀ L, 0 < L → hs2 (D L).J ≤ Mloc * L)
    (hrate : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → Lf L * ε L ≤ η * Real.sqrt L) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      |∑ i, ∑ j, (f L ((D L).a i) - f L ((D L).b j)) * (D L).J i j ^ 2| ≤ η * L := by
  intro η hη
  obtain ⟨L₀, hL₀⟩ := littleO_of_growing_lipschitz Lf ε Mloc hLf hε hM hrate η hη
  refine ⟨max L₀ 1, fun L hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hL)
  have e : Mloc / (1 / L) = Mloc * L := by
    first
    | rw [one_div, div_inv_eq_mul]
    | simp [div_eq_mul_inv]
  have hJ' : hs2 (D L).J ≤ Mloc / (1 / L) := by
    rw [e]
    exact hJ L hLpos
  have h1 := trace_local_mass_le (D L) (f L) (Lf L) (ε L) Mloc (1 / L) (hLf L) (hf L)
    (hK L hLpos) hJ'
  rw [abs_of_nonneg (hε L), e] at h1
  exact le_trans h1 (hL₀ L (le_trans (le_max_left _ _) hL))

end Finding

/-- `hs2` of a `1 × 1` array is the square of its entry. -/
theorem hs2_fin1 (M : Fin 1 → Fin 1 → ℝ) : hs2 M = M 0 0 ^ 2 := by
  first
  | (unfold hs2; rw [Fin.sum_univ_one, Fin.sum_univ_one])
  | simp [hs2]

/-- The witness family: `a = 1/L`, `b = 0`, `J = √L` on `Fin 1 × Fin 1`. -/
noncomputable def wD (L : ℝ) : Data (Fin 1) (Fin 1) :=
  ⟨fun _ => 1 / L, fun _ => 0, fun _ _ => Real.sqrt L⟩

/-- The witness defect size `ε L = 1/√L`. -/
noncomputable def wε (L : ℝ) : ℝ := 1 / Real.sqrt L

theorem witness_K_hs2 (L : ℝ) (hL : 0 < L) : hs2 (wD L).K = 1 / L := by
  rw [hs2_fin1]
  show ((1 / L - 0) * Real.sqrt L) ^ 2 = 1 / L
  have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  have hne : L ≠ 0 := ne_of_gt hL
  calc ((1 / L - 0) * Real.sqrt L) ^ 2 = (1 / L) ^ 2 * Real.sqrt L ^ 2 := by ring
    _ = (1 / L) ^ 2 * L := by rw [hs]
    _ = 1 / L := by
        first
        | (field_simp; done)
        | (field_simp; ring)
        | (rw [div_pow, one_pow, sq]; field_simp)

theorem witness_J_hs2 (L : ℝ) (hL : 0 ≤ L) : hs2 (wD L).J = L := by
  rw [hs2_fin1]
  show Real.sqrt L ^ 2 = L
  exact Real.sq_sqrt hL

theorem witness_eps_sq (L : ℝ) (hL : 0 < L) : wε L ^ 2 = 1 / L := by
  show (1 / Real.sqrt L) ^ 2 = 1 / L
  rw [div_pow, one_pow, Real.sq_sqrt hL.le]

theorem witness_eps_nonneg (L : ℝ) : 0 ≤ wε L := by
  unfold wε
  positivity

theorem witness_rate :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → 1 * wε L ≤ η * Real.sqrt L := by
  intro η hη
  refine ⟨1 / η + 1, fun L hL => ?_⟩
  have hLη : 1 / η < L := by linarith
  have hLpos : 0 < L := lt_trans (div_pos one_pos hη) hLη
  have hη0 : η ≠ 0 := ne_of_gt hη
  have hsq : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have e : η * (1 / η) = 1 := by field_simp
  have h1 : 1 < η * L := by linarith [mul_lt_mul_of_pos_left hLη hη]
  have h2 : η * Real.sqrt L * Real.sqrt L = η * L := by rw [mul_assoc, hss]
  show 1 * (1 / Real.sqrt L) ≤ η * Real.sqrt L
  rw [one_mul]
  first
  | rw [div_le_iff₀ hsq]
  | rw [div_le_iff hsq]
  linarith

theorem witness_trace_eq_one (L : ℝ) (hL : 0 < L) :
    ∑ i, ∑ j, ((wD L).a i - (wD L).b j) * (wD L).J i j ^ 2 = 1 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  show (1 / L - 0) * Real.sqrt L ^ 2 = 1
  have hne : L ≠ 0 := ne_of_gt hL
  rw [Real.sq_sqrt hL.le, sub_zero]
  field_simp

/-- **G147.** The hypotheses of `trace_littleO_of_growth_pos` hold for the witness, whose
defect is nonzero and whose trace comparison equals `1` for every `L > 0`. -/
theorem growth_inputs_nonvacuous :
    (∀ L, 0 < L → hs2 (wD L).K ≤ wε L ^ 2) ∧ (∀ L, 0 < L → hs2 (wD L).J ≤ 1 * L) ∧
      (∀ L, 0 < L → hs2 (wD L).K ≠ 0) ∧
      (∀ L, 0 < L → ∑ i, ∑ j, ((wD L).a i - (wD L).b j) * (wD L).J i j ^ 2 = 1) := by
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, witness_trace_eq_one⟩
  · exact (witness_K_hs2 L hL).trans_le (witness_eps_sq L hL).symm.le
  · exact (witness_J_hs2 L hL.le).trans_le (one_mul L).symm.le
  · rw [witness_K_hs2 L hL]
    exact (div_pos one_pos hL).ne'

/-- **G147.** `trace_littleO_of_growth_pos` applies to the witness (the hypotheses typecheck
together). -/
theorem witness_littleO :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      |∑ i, ∑ j, ((fun (_ : ℝ) (x : ℝ) => x) L ((wD L).a i)
        - (fun (_ : ℝ) (x : ℝ) => x) L ((wD L).b j)) * (wD L).J i j ^ 2| ≤ η * L :=
  trace_littleO_of_growth_pos wD (fun _ x => x) (fun _ => 1) wε 1 (fun _ => zero_le_one)
    (fun L x y => by show |x - y| ≤ 1 * |x - y|; rw [one_mul]) witness_eps_nonneg zero_le_one
    (growth_inputs_nonvacuous.1) (growth_inputs_nonvacuous.2.1) witness_rate

end SteklovAudit.GrowthInputsWitness
