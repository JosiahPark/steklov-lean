import Mathlib
import SteklovAudit.TraceLocalMass

/-!
# G145: the trace comparison with growing Lipschitz constants

Roadmap item G145 (priority row 3, a one-run reduction toward row 5). G141
(`TraceLocalMass.littleO_of_bounded_defect`) treated a bounded Lipschitz constant. Here the
Lipschitz constant `Λ L` and the defect `ε L` may grow with `L`:

* `littleO_of_growing_lipschitz`: if `Λ L · ε L = o(√L)` then `Λ L · ε L · √(Mloc · L) = o(L)`.
* `growing_needs_rate`, `growing_needs_rate_not_littleO`: with `Λ L = √L`, `ε = 1`, `Mloc = 1`
  the bound equals `L`, so `Λ ε = O(√L)` alone does not give `o(L)`; the little-o rate is needed.
* `trace_littleO_of_growth`: for a family `D L` of spectral data with `Lf L`-Lipschitz
  multipliers `f L`, defect `hs2 (D L).K ≤ ε L ²` and local mass `hs2 (D L).J ≤ Mloc · L`
  (scale `h = 1/L`), the trace comparison is `o(L)` when `Lf L · ε L = o(√L)`.

F table text: the Lipschitz trace comparison is `o(L)` whenever `Lip · defect = o(√L)`; the
defect rate for the actual operator stays open.

What this file does NOT prove:
* The defect bound, the local mass bound and the rate `Lf L · ε L = o(√L)` are named
  hypotheses. They are not proved for the paper's cumulative multipliers or for any operator;
  no Dirichlet-to-Neumann operator is constructed and the data `D L` are arbitrary.
* Nothing here proves Lemma 7.1′, τ(M), κ(M), Prop. 7.3, (7.29), any of H1–H6, or
  Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.TraceLocalMassGrowth

open SteklovAudit.AbstractTransfer SteklovAudit.TraceLocalMass

/-- **G145.** Growing constants: if `Λ L · ε L = o(√L)` then `Λ L · ε L · √(Mloc · L) = o(L)`. -/
theorem littleO_of_growing_lipschitz (Λ ε : ℝ → ℝ) (Mloc : ℝ)
    (hΛ : ∀ L, 0 ≤ Λ L) (hε : ∀ L, 0 ≤ ε L) (hM : 0 ≤ Mloc)
    (hrate : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → Λ L * ε L ≤ η * Real.sqrt L) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      Λ L * ε L * Real.sqrt (Mloc * L) ≤ η * L := by
  intro η hη
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt Mloc := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs1 : 0 < s + 1 := by linarith
  have hne : s + 1 ≠ 0 := ne_of_gt hs1
  have hη' : 0 < η / (s + 1) := div_pos hη hs1
  obtain ⟨L₀, hL₀⟩ := hrate (η / (s + 1)) hη'
  refine ⟨max L₀ 0, fun L hL => ?_⟩
  have hLL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : 0 ≤ L := le_trans (le_max_right _ _) hL
  have hb := hL₀ L hLL₀
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hc : η / (s + 1) * (s + 1) = η := by
    first
    | exact div_mul_cancel₀ η hne
    | field_simp
  have hkey : η / (s + 1) * s ≤ η := by
    have h2 : η / (s + 1) * s = η - η / (s + 1) := by linear_combination hc
    rw [h2]
    linarith
  have _hΛ0 := hΛ L
  calc Λ L * ε L * Real.sqrt (Mloc * L) = (Λ L * ε L) * (s * Real.sqrt L) := by
        rw [Real.sqrt_mul hM, ← hs]
    _ ≤ (η / (s + 1) * Real.sqrt L) * (s * Real.sqrt L) :=
        mul_le_mul_of_nonneg_right hb (mul_nonneg hs0 hsL)
    _ = (η / (s + 1) * s) * (Real.sqrt L * Real.sqrt L) := by ring
    _ ≤ η * (Real.sqrt L * Real.sqrt L) :=
        mul_le_mul_of_nonneg_right hkey (mul_nonneg hsL hsL)
    _ = η * L := by rw [hsq]

/-- **G145.** With `Λ L = √L`, `ε = 1`, `Mloc = 1` the bound `Λ ε √(Mloc L)` equals `L`. -/
theorem growing_needs_rate (L : ℝ) (hL : 0 ≤ L) :
    Real.sqrt L * 1 * Real.sqrt (1 * L) = L := by
  rw [one_mul, mul_one]
  exact Real.mul_self_sqrt hL

/-- **G145.** So `Λ ε = O(√L)` alone does not give `o(L)`: the example above is not `o(L)`. -/
theorem growing_needs_rate_not_littleO :
    ¬ ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      Real.sqrt L * 1 * Real.sqrt (1 * L) ≤ η * L := by
  intro h
  obtain ⟨L₀, hL₀⟩ := h (1 / 2) (by norm_num)
  have h1 := hL₀ (max L₀ 1) (le_max_left _ _)
  have h2 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  rw [growing_needs_rate _ (by linarith)] at h1
  linarith

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G145.** Trace comparison for a family at scale `h = 1/L` with growing Lipschitz constants:
it is `o(L)` when `Lf L · ε L = o(√L)`. All inputs are named hypotheses. -/
theorem trace_littleO_of_growth (D : ℝ → Data ι κ) (f : ℝ → ℝ → ℝ) (Lf ε : ℝ → ℝ)
    (Mloc : ℝ) (hLf : ∀ L, 0 ≤ Lf L) (hf : ∀ L x y, |f L x - f L y| ≤ Lf L * |x - y|)
    (hε : ∀ L, 0 ≤ ε L) (hM : 0 ≤ Mloc)
    (hK : ∀ L, hs2 (D L).K ≤ ε L ^ 2) (hJ : ∀ L, hs2 (D L).J ≤ Mloc * L)
    (hrate : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → Lf L * ε L ≤ η * Real.sqrt L) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      |∑ i, ∑ j, (f L ((D L).a i) - f L ((D L).b j)) * (D L).J i j ^ 2| ≤ η * L := by
  intro η hη
  obtain ⟨L₀, hL₀⟩ := littleO_of_growing_lipschitz Lf ε Mloc hLf hε hM hrate η hη
  refine ⟨L₀, fun L hL => ?_⟩
  have e : Mloc / (1 / L) = Mloc * L := by
    first
    | rw [one_div, div_inv_eq_mul]
    | simp [div_eq_mul_inv]
  have hJ' : hs2 (D L).J ≤ Mloc / (1 / L) := by
    rw [e]
    exact hJ L
  have h1 := trace_local_mass_le (D L) (f L) (Lf L) (ε L) Mloc (1 / L) (hLf L) (hf L)
    (hK L) hJ'
  rw [abs_of_nonneg (hε L), e] at h1
  exact le_trans h1 (hL₀ L hL)

end SteklovAudit.TraceLocalMassGrowth
