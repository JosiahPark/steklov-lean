import Mathlib
import SteklovAudit.H5PinnedRowsPow

/-!
# G106: the pinned trade-off rows are strictly weaker than the pinned linear rows

Roadmap item G106. On the same pinned one-by-one cutoff data `qD` (`a = 1 / L ^ 2`, `b = 0`,
`J = L`) with `F = id`, `E = 1 / L ^ 2 * L ^ 2` (the cutoff sum itself) and `Emod = 0`, the
pinned trade-off rows `H5bPinnedRowsPow` (G105, `H5PinnedRowsPow.lean`) have an inhabitant with
`p = 2` (`hs2 J = L ^ 2`, `hs2 K = 1 / L ^ 2 = o(L ^ 0)`), while the pinned linear rows
`H5bPinnedRows` (G101) have none: `massLin` would force `L ^ 2 ≤ m * L` for all `L ≥ 1`.
Since G105's `ofPinned` embeds G101 into G105, G105 is strictly weaker on pinned data.

F table text: with the data pinned, the trade-off rows admit data the linear rows reject.

What this file does NOT prove: no row is proved for any operator; `qD` is a toy family, not the
cutoff data of the Steklov operator of the tetrahedron, which is not defined in Lean. No DtN
operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional. This is an audit only.
-/

namespace SteklovAudit.H5PinnedRowsPowStrict

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5GlobalLipRowsEv
  SteklovAudit.H5GlobalLipRowsPow SteklovAudit.H5PinnedRows SteklovAudit.H5PinnedRowsPow

/-- One-point index sizes. -/
abbrev oA : ℝ → ℝ → ℝ → ℕ := fun _ _ _ => 1

/-- Nonempty one-by-one cutoff data: `a = 1 / L ^ 2`, `b = 0`, overlap `J = L`. -/
noncomputable def qD : ∀ ε γ L : ℝ, Data (Fin 1) (Fin 1) :=
  fun _ _ L => ⟨fun _ => 1 / L ^ 2, fun _ => 0, fun _ _ => L⟩

/-- The identity function at every `(ε, γ, L)`. -/
def idF : ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ x => x

/-- The energy: exactly the cutoff sum of `qD`. -/
noncomputable def eQ : ℝ → ℝ → ℝ → ℝ := fun _ _ L => 1 / L ^ 2 * L ^ 2

/-- The cutoff sum of `qD` is `1 / L ^ 2 * L ^ 2`. -/
theorem q_sum (ε γ L : ℝ) :
    ∑ i : Fin 1, ∑ j : Fin 1, (idF ε γ L ((qD ε γ L).a i) - idF ε γ L ((qD ε γ L).b j)) *
      (qD ε γ L).J i j ^ 2 = 1 / L ^ 2 * L ^ 2 := by
  first
    | (simp [qD, idF]; done)
    | (simp [qD, idF, Fin.sum_univ_one]; done)
    | (simp [qD, idF, Fin.sum_univ_one]; ring)
    | (rw [Fin.sum_univ_one, Fin.sum_univ_one]; simp only [qD, idF]; ring)

/-- The overlap mass of `qD` is `L ^ 2`. -/
theorem qD_hs2J (ε γ L : ℝ) : hs2 (qD ε γ L).J = L ^ 2 := by
  first
    | (simp [hs2, qD]; done)
    | (simp [hs2, qD, Fin.sum_univ_one]; done)
    | (simp [hs2, qD, Fin.sum_univ_one]; ring)
    | (rw [hs2, Fin.sum_univ_one, Fin.sum_univ_one]; simp only [qD]; ring)

/-- The defect of `qD`: `hs2 K = 1 / L ^ 2` for `L ≠ 0`. -/
theorem qD_hs2K (ε γ L : ℝ) (hL : L ≠ 0) : hs2 (qD ε γ L).K = 1 / L ^ 2 := by
  first
    | (simp [hs2, Data.K, qD]; done)
    | (simp [hs2, Data.K, qD]; field_simp; done)
    | (simp [hs2, Data.K, qD]; field_simp; ring)
    | (simp [hs2, Data.K, qD, Fin.sum_univ_one]; field_simp; ring)
    | (rw [hs2, Fin.sum_univ_one, Fin.sum_univ_one]; simp only [Data.K, qD]; field_simp; ring)

/-- **G106.** Pinned trade-off rows (`p = 2`) for the data `qD`. -/
noncomputable def qRowsPow : H5bPinnedRowsPow eQ (fun _ _ _ => 0) oA oA qD idF where
  disc := fun _ _ _ => 0
  cutoff := by
    intro ε γ L
    first
      | (simp [eQ, qD, idF, oA]; done)
      | (rw [q_sum]; simp [eQ])
      | (simp only [eQ]; rw [q_sum]; simp)
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
  p := fun _ _ => 2
  hp := fun _ _ => ⟨by norm_num, by norm_num⟩
  massPow := by
    intro ε γ
    refine ⟨1, fun L _ => ?_⟩
    show hs2 (qD ε γ L).J ≤ 1 * L ^ (2 : ℝ)
    rw [qD_hs2J, one_mul]
    first
      | (rw [Real.rpow_two])
      | (rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast])
      | (exact le_of_eq (Real.rpow_natCast L 2).symm)
  defectPow := by
    intro ε γ _ _ η hη
    refine ⟨max 1 (1 / η), fun L hL => ?_⟩
    show hs2 (qD ε γ L).K ≤ η * L ^ ((2 : ℝ) - 2)
    have h1 : 1 ≤ L := le_trans (le_max_left _ _) hL
    have h2 : 1 / η ≤ L := le_trans (le_max_right _ _) hL
    have hLpos : 0 < L := by linarith
    rw [show (2 : ℝ) - 2 = 0 by norm_num, Real.rpow_zero, mul_one, qD_hs2K ε γ L hLpos.ne']
    have hsq : L ≤ L ^ 2 := by nlinarith
    have h3 : 1 / L ^ 2 ≤ 1 / L := one_div_le_one_div_of_le hLpos hsq
    have h4 : 1 / L ≤ η := by
      have h5 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / η) h2
      rwa [one_div_one_div] at h5
    linarith

/-- **G106.** The pinned trade-off rows hold for `qD`. -/
theorem pinnedPow_nonempty_q :
    Nonempty (H5bPinnedRowsPow eQ (fun _ _ _ => 0) oA oA qD idF) :=
  ⟨qRowsPow⟩

/-- **G106.** The pinned linear rows fail for `qD`: `massLin` would give `L ^ 2 ≤ m * L`. -/
theorem not_pinnedRows_q :
    ¬ Nonempty (H5bPinnedRows eQ (fun _ _ _ => 0) oA oA qD idF) := by
  rintro ⟨H⟩
  have hA : (1 : ℝ) ≤ |H.m 1 1| + 2 := by linarith [abs_nonneg (H.m 1 1)]
  have h := H.massLin 1 1 (|H.m 1 1| + 2) hA
  rw [qD_hs2J] at h
  have ha : 0 < |H.m 1 1| + 2 - H.m 1 1 := by linarith [le_abs_self (H.m 1 1)]
  have hb : 0 < |H.m 1 1| + 2 := by linarith [abs_nonneg (H.m 1 1)]
  nlinarith [mul_pos ha hb]

/-- **G106 (F table).** On the same pinned data the trade-off rows hold and the linear rows
fail: G105 is strictly weaker than G101. -/
theorem pinnedPow_strictly_weaker :
    Nonempty (H5bPinnedRowsPow eQ (fun _ _ _ => 0) oA oA qD idF) ∧
      ¬ Nonempty (H5bPinnedRows eQ (fun _ _ _ => 0) oA oA qD idF) :=
  ⟨pinnedPow_nonempty_q, not_pinnedRows_q⟩

end SteklovAudit.H5PinnedRowsPowStrict
