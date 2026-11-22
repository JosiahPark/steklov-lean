import Mathlib
import SteklovAudit.H5PinnedRows

/-!
# G103: pinned nonempty data makes the rows strictly stronger than the target

Roadmap item G103. With the cutoff data of `H5bPinnedRows` (G101, `H5PinnedRows.lean`) pinned
to a nonempty one-by-one family `bumpD` (`a = 1`, `b = 0`, `J = L`) and `F = id`, the target
`H5bTarget 0 0` holds but the pinned rows for `E = Emod = 0` have no inhabitant: the `cutoff`
row forces `L ^ 2 ≤ disc 1 1 L`, while `discVanish` forces `disc 1 1 L ≤ L` for large `L`.
So once the data is pinned, the target does not imply the rows; the `cutoff` row is no longer
the target in disguise (contrast G102, `H5PinnedZeroAudit.lean`, for the empty data).

What this file does NOT prove: no row is proved for any operator; `bumpD` is a toy family, not
the cutoff data of the Steklov operator of the tetrahedron, which is not defined in Lean. No DtN
operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional. This is an audit only.
-/

namespace SteklovAudit.H5PinnedNotTarget

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5PinnedRows

/-- One-point index sizes. -/
abbrev oA : ℝ → ℝ → ℝ → ℕ := fun _ _ _ => 1

/-- Nonempty one-by-one cutoff data: `a = 1`, `b = 0`, overlap `J = L`. -/
noncomputable def bumpD : ∀ ε γ L : ℝ, Data (Fin 1) (Fin 1) :=
  fun _ _ L => ⟨fun _ => 1, fun _ => 0, fun _ _ => L⟩

/-- The identity function at every `(ε, γ, L)`. -/
def idF : ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ x => x

/-- The cutoff sum of the bump data is `L ^ 2`. -/
theorem bump_sum (ε γ L : ℝ) :
    ∑ i : Fin 1, ∑ j : Fin 1, (idF ε γ L ((bumpD ε γ L).a i) - idF ε γ L ((bumpD ε γ L).b j)) *
      (bumpD ε γ L).J i j ^ 2 = L ^ 2 := by
  first
    | (simp [bumpD, idF]; done)
    | (simp [bumpD, idF, Fin.sum_univ_one]; ring)
    | (rw [Fin.sum_univ_one, Fin.sum_univ_one]; simp only [bumpD, idF]; ring)

/-- The target holds for `E = Emod = 0`. -/
theorem target_zero : H5bTarget (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) := by
  unfold H5bTarget
  intro ε γ _ _ η hη
  refine ⟨0, fun L hL => ?_⟩
  simp only [sub_self, abs_zero]
  exact mul_nonneg hη.le hL

/-- **G103.** Pinned to the bump data, the rows for `E = Emod = 0` have no inhabitant. -/
theorem not_pinned_bump :
    ¬ Nonempty (H5bPinnedRows (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) oA oA bumpD idF) := by
  rintro ⟨H⟩
  obtain ⟨L₀, hL₀⟩ := H.discVanish 1 1 one_pos one_pos 1 one_pos
  have key : ∀ L : ℝ, L₀ ≤ L → 2 ≤ L → False := by
    intro L hLL hL2
    have hd : H.disc 1 1 L ≤ 1 * L := hL₀ L hLL
    have hc : |((0 : ℝ) - 0) - ∑ i : Fin 1, ∑ j : Fin 1,
        (idF 1 1 L ((bumpD 1 1 L).a i) - idF 1 1 L ((bumpD 1 1 L).b j)) *
          (bumpD 1 1 L).J i j ^ 2| ≤ H.disc 1 1 L := H.cutoff 1 1 L
    rw [bump_sum] at hc
    have hn : -(((0 : ℝ) - 0) - L ^ 2) ≤ |((0 : ℝ) - 0) - L ^ 2| := by
      first
        | exact neg_le_abs _
        | exact le_abs.mpr (Or.inr le_rfl)
        | exact neg_le_abs_self _
    nlinarith
  exact key (max L₀ 2) (le_max_left _ _) (le_max_right _ _)

/-- **G103 (F table).** The target holds but the pinned rows fail: with nonempty pinned data
the rows are strictly stronger than the target. -/
theorem pinned_strictly_stronger :
    H5bTarget (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) ∧
      ¬ Nonempty (H5bPinnedRows (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) oA oA bumpD idF) :=
  ⟨target_zero, not_pinned_bump⟩

end SteklovAudit.H5PinnedNotTarget
