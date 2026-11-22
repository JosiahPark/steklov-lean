import Mathlib
import SteklovAudit.H5PinnedRows

/-!
# G104: pinned rows are non-vacuous on nonempty data

Roadmap item G104. The pinned rows `H5bPinnedRows` (G101, `H5PinnedRows.lean`) have an
inhabitant for nonempty one-by-one cutoff data `decayD` (`a = 1 / L`, `b = 0`, `J = 1`) with
`F = id`, `E = 1 / L`, `Emod = 0`: `disc = 0`, `Λ = 1`, `m = 1`, `δ = 1 / L ^ 3`. The defect
`hs2 K = 1 / L ^ 2` is nonzero for `L > 0`, so the pinned form is satisfiable without the empty
choice of G102 and without a zero defect. Together with G103 (`H5PinnedNotTarget.lean`) this
shows the pinned rows are neither vacuous nor the target in disguise.

What this file does NOT prove: no row is proved for any operator; `decayD` is a toy family, not
the cutoff data of the Steklov operator of the tetrahedron, which is not defined in Lean. No DtN
operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional. This is an audit only.
-/

namespace SteklovAudit.H5PinnedNonvacuous

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5PinnedRows

/-- One-point index sizes. -/
abbrev oA : ℝ → ℝ → ℝ → ℕ := fun _ _ _ => 1

/-- Nonempty one-by-one cutoff data: `a = 1 / L`, `b = 0`, overlap `J = 1`. -/
noncomputable def decayD : ∀ ε γ L : ℝ, Data (Fin 1) (Fin 1) :=
  fun _ _ L => ⟨fun _ => 1 / L, fun _ => 0, fun _ _ => 1⟩

/-- The identity function at every `(ε, γ, L)`. -/
def idF : ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ x => x

/-- The energy `E = 1 / L`. -/
noncomputable def eD : ℝ → ℝ → ℝ → ℝ := fun _ _ L => 1 / L

/-- The cutoff sum of the decay data is `1 / L`. -/
theorem decay_sum (ε γ L : ℝ) :
    ∑ i : Fin 1, ∑ j : Fin 1, (idF ε γ L ((decayD ε γ L).a i) - idF ε γ L ((decayD ε γ L).b j)) *
      (decayD ε γ L).J i j ^ 2 = 1 / L := by
  first
    | (simp [decayD, idF]; done)
    | (simp [decayD, idF, Fin.sum_univ_one]; ring)
    | (rw [Fin.sum_univ_one, Fin.sum_univ_one]; simp only [decayD, idF]; ring)

/-- The overlap mass of the decay data is `1`. -/
theorem decayD_hs2J (ε γ L : ℝ) : hs2 (decayD ε γ L).J = 1 := by
  first
    | (simp [hs2, decayD]; done)
    | (simp [hs2, decayD, Fin.sum_univ_one]; done)
    | (rw [hs2, Fin.sum_univ_one, Fin.sum_univ_one]; simp only [decayD]; ring)

/-- The defect of the decay data: `hs2 K = 1 / L ^ 2`. -/
theorem decayD_hs2K (ε γ L : ℝ) : hs2 (decayD ε γ L).K = 1 / L ^ 2 := by
  first
    | (simp [hs2, Data.K, decayD]; done)
    | (simp [hs2, Data.K, decayD, Fin.sum_univ_one]; ring)
    | (rw [hs2, Fin.sum_univ_one, Fin.sum_univ_one]; simp only [Data.K, decayD]; ring)

/-- The defect is nonzero for `L > 0`. -/
theorem decay_defect_pos (ε γ L : ℝ) (hL : 0 < L) : 0 < hs2 (decayD ε γ L).K := by
  rw [decayD_hs2K]
  first
    | positivity
    | exact div_pos one_pos (pow_pos hL 2)

/-- **G104.** Pinned rows for the decay data. -/
noncomputable def decayRows : H5bPinnedRows eD (fun _ _ _ => 0) oA oA decayD idF where
  disc := fun _ _ _ => 0
  cutoff := by
    intro ε γ L
    first
      | (simp [eD, decayD, idF, oA]; done)
      | (rw [decay_sum]; simp [eD])
      | (simp only [eD]; rw [decay_sum]; simp)
  discVanish := by
    intro ε γ _ _ η hη
    refine ⟨1, fun L hL => ?_⟩
    show (0 : ℝ) ≤ η * L
    exact mul_nonneg hη.le (by linarith)
  Λ := fun _ _ => 1
  hΛ := fun _ _ => zero_le_one
  lip := by
    intro ε γ L x y
    show |x - y| ≤ 1 * |x - y|
    exact le_of_eq (one_mul _).symm
  m := fun _ _ => 1
  hm := fun _ _ => zero_le_one
  massLin := by
    intro ε γ L hL
    show hs2 (decayD ε γ L).J ≤ 1 * L
    rw [decayD_hs2J]
    linarith
  δ := fun _ _ L => 1 / L ^ 3
  defectLin := by
    intro ε γ L hL
    show hs2 (decayD ε γ L).K ≤ 1 / L ^ 3 * L
    rw [decayD_hs2K]
    have hL0 : L ≠ 0 := ne_of_gt (by linarith)
    apply le_of_eq
    first
      | (field_simp; ring)
      | field_simp
      | (rw [div_mul_eq_mul_div, one_mul, pow_succ, div_mul_cancel_right₀ hL0])
  δVanish := by
    intro ε γ _ _ η hη
    refine ⟨max 1 (1 / η), fun L hL => ?_⟩
    show 1 / L ^ 3 ≤ η
    have h1 : 1 ≤ L := le_trans (le_max_left _ _) hL
    have h2 : 1 / η ≤ L := le_trans (le_max_right _ _) hL
    have hLpos : 0 < L := by linarith
    have hsq : 1 ≤ L ^ 2 := by nlinarith
    have hcube : L ≤ L ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hsq hLpos.le]
    have h3 : 1 / L ^ 3 ≤ 1 / L := one_div_le_one_div_of_le hLpos hcube
    have h4 : 1 / L ≤ η := by
      have h5 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / η) h2
      rwa [one_div_one_div] at h5
    linarith

theorem decayRows_m : decayRows.m = fun _ _ => 1 := rfl

/-- **G104 (F table).** The pinned form is satisfiable on nonempty data with nonzero defect. -/
theorem pinned_nonempty_decay :
    Nonempty (H5bPinnedRows eD (fun _ _ _ => 0) oA oA decayD idF) :=
  ⟨decayRows⟩

end SteklovAudit.H5PinnedNonvacuous
