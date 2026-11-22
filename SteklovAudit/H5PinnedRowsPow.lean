import Mathlib
import SteklovAudit.H5PinnedRows
import SteklovAudit.H5GlobalLipRowsPow

/-!
# G105: the G98 trade-off rows for pinned cutoff data

Roadmap item G105. `H5bPinnedRowsPow E Emod nA nB D₀ F₀` has the fields of
`H5bGlobalLipRowsPow` (G98, `H5GlobalLipRowsPow.lean`) except `nA`, `nB`, `D`, `F`: the cutoff
data `D₀` and the function `F₀` are parameters, as in the pinned form `H5bPinnedRows` (G101,
`H5PinnedRows.lean`). `toRowsPow` copies a pinned trade-off family into `H5bGlobalLipRowsPow`
with `D := D₀`, `F := F₀`; `ofPinned` shows the G101 rows are the case `p = 1`; and
`h5b_of_pinnedRowsPow` gives `H5bTarget E Emod`.

F table text: for pinned data the mass and defect rows may trade powers of `L`; `p = 1` is G101.

What this file does NOT prove: `massPow` and `defectPow` are named hypotheses, proved for no
operator. The cutoff data of the Steklov operator of the tetrahedron is not defined in Lean, so
the pinned form is stated for arbitrary given data `D₀ F₀`; which data the paper pins is open.
No DtN operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5PinnedRowsPow

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5GlobalLipRowsEv
  SteklovAudit.H5GlobalLipRowsPow SteklovAudit.H5PinnedRows

/-- The G98 trade-off rows with the cutoff data `D₀` and the function `F₀` fixed in advance. -/
structure H5bPinnedRowsPow (E Emod : ℝ → ℝ → ℝ → ℝ) (nA nB : ℝ → ℝ → ℝ → ℕ)
    (D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F₀ : ℝ → ℝ → ℝ → ℝ → ℝ) where
  disc : ℝ → ℝ → ℝ → ℝ
  cutoff : ∀ ε γ L : ℝ, |(E ε γ L - Emod ε γ L) - ∑ i, ∑ j,
    (F₀ ε γ L ((D₀ ε γ L).a i) - F₀ ε γ L ((D₀ ε γ L).b j)) * (D₀ ε γ L).J i j ^ 2| ≤ disc ε γ L
  discVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    disc ε γ L ≤ η * L
  Λ : ℝ → ℝ → ℝ
  hΛ : ∀ ε γ, 0 ≤ Λ ε γ
  lip : ∀ ε γ L x y : ℝ, |F₀ ε γ L x - F₀ ε γ L y| ≤ Λ ε γ * |x - y|
  m : ℝ → ℝ → ℝ
  hm : ∀ ε γ, 0 ≤ m ε γ
  p : ℝ → ℝ → ℝ
  hp : ∀ ε γ, 0 ≤ p ε γ ∧ p ε γ ≤ 2
  /-- Row: the overlap mass of the pinned data is eventually `O(L ^ p)` (named hypothesis). -/
  massPow : ∀ ε γ : ℝ, ∃ L₁ : ℝ, ∀ L, L₁ ≤ L → hs2 (D₀ ε γ L).J ≤ m ε γ * L ^ (p ε γ)
  /-- Row: the Hilbert–Schmidt defect of the pinned data is `o(L ^ (2 - p))` (named hypothesis). -/
  defectPow : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    hs2 (D₀ ε γ L).K ≤ η * L ^ (2 - p ε γ)

variable {E Emod : ℝ → ℝ → ℝ → ℝ} {nA nB : ℝ → ℝ → ℝ → ℕ}
  {D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))} {F₀ : ℝ → ℝ → ℝ → ℝ → ℝ}

/-- **G105.** A pinned trade-off family is a G98 family whose data is `D₀`, `F₀`. -/
noncomputable def toRowsPow (H : H5bPinnedRowsPow E Emod nA nB D₀ F₀) :
    H5bGlobalLipRowsPow E Emod where
  nA := nA
  nB := nB
  D := D₀
  F := F₀
  disc := H.disc
  cutoff := H.cutoff
  discVanish := H.discVanish
  Λ := H.Λ
  hΛ := H.hΛ
  lip := H.lip
  m := H.m
  hm := H.hm
  p := H.p
  hp := H.hp
  massPow := H.massPow
  defectPow := H.defectPow

theorem toRowsPow_D (H : H5bPinnedRowsPow E Emod nA nB D₀ F₀) : (toRowsPow H).D = D₀ := rfl

/-- **G105.** The pinned G101 rows are the pinned trade-off rows with `p = 1`. -/
noncomputable def ofPinned (H : H5bPinnedRows E Emod nA nB D₀ F₀) :
    H5bPinnedRowsPow E Emod nA nB D₀ F₀ where
  disc := H.disc
  cutoff := H.cutoff
  discVanish := H.discVanish
  Λ := H.Λ
  hΛ := H.hΛ
  lip := H.lip
  m := H.m
  hm := H.hm
  p := fun _ _ => 1
  hp := fun _ _ => ⟨by norm_num, by norm_num⟩
  massPow := by
    intro ε γ
    refine ⟨1, fun L hL => ?_⟩
    show hs2 (D₀ ε γ L).J ≤ H.m ε γ * L ^ (1 : ℝ)
    rw [Real.rpow_one]
    exact H.massLin ε γ L hL
  defectPow := by
    intro ε γ hε hγ η hη
    obtain ⟨L₀, h⟩ := H.δVanish ε γ hε hγ η hη
    refine ⟨max 1 L₀, fun L hL => ?_⟩
    have h1 : 1 ≤ L := le_trans (le_max_left 1 L₀) hL
    have h2 : L₀ ≤ L := le_trans (le_max_right 1 L₀) hL
    show hs2 (D₀ ε γ L).K ≤ η * L ^ ((2 : ℝ) - 1)
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    exact le_trans (H.defectLin ε γ L h1)
      (mul_le_mul_of_nonneg_right (h L h2) (by linarith))

theorem ofPinned_p (H : H5bPinnedRows E Emod nA nB D₀ F₀) :
    (ofPinned H).p = fun _ _ => 1 := rfl

/-- **G105.** The pinned trade-off rows give the H5b comparison (7.29). -/
theorem h5b_of_pinnedRowsPow (H : H5bPinnedRowsPow E Emod nA nB D₀ F₀) : H5bTarget E Emod :=
  h5b_of_globalLipRowsPow (toRowsPow H)

end SteklovAudit.H5PinnedRowsPow
