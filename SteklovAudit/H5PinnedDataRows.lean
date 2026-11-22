import Mathlib
import SteklovAudit.H5PinnedCutoffVanish
import SteklovAudit.H5PinnedSumSmall

/-!
# G109: the pinned rows that mention only the data

Roadmap item G109. `H5bPinnedDataRows nA nB D₀ F₀` keeps the fields of `H5bPinnedRows` (G101) that
do not mention `E`, `Emod` or `disc`: the Lipschitz row (`Λ`, `hΛ`, `lip`), the mass row (`m`, `hm`,
`massLin`) and the defect rows (`δ`, `defectLin`, `δVanish`). `dataOf` forgets the other fields.

* `sumLittleO_of_dataRows`: the data rows alone force G108's `SumLittleO D₀ F₀`. Proof: the data rows
  plus the trivial cutoff row for `E := pinnedSum D₀ F₀`, `Emod := 0`, `disc := 0` form a pinned
  family (`withSum`), and `h5b_of_pinnedRows` (the G86/G90 Cauchy–Schwarz chain) gives the target
  for that `E`, which is `SumLittleO`.
* `pinned_iff_dataRows_core`: pinned rows exist iff the data rows exist and the cutoff discrepancy
  `coreDisc` (G107) is `o(L)`.

F table text: the pinned rows are data rows (mass, defect, Lipschitz) plus one `o(L)` row comparing
`E − Emod` with the data's spectral sum.

What this file does NOT prove: no row is proved for any operator. The cutoff data of the Steklov
operator of the tetrahedron is not defined in Lean; `D₀`, `F₀` are arbitrary given data. No DtN
operator is constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5PinnedDataRows

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5PinnedRows
  SteklovAudit.H5PinnedCutoffVanish SteklovAudit.H5PinnedSumSmall

/-- The rows of `H5bPinnedRows` that mention only the data `D₀`, `F₀`. -/
structure H5bPinnedDataRows (nA nB : ℝ → ℝ → ℝ → ℕ)
    (D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F₀ : ℝ → ℝ → ℝ → ℝ → ℝ) where
  Λ : ℝ → ℝ → ℝ
  hΛ : ∀ ε γ, 0 ≤ Λ ε γ
  lip : ∀ ε γ L x y : ℝ, |F₀ ε γ L x - F₀ ε γ L y| ≤ Λ ε γ * |x - y|
  m : ℝ → ℝ → ℝ
  hm : ∀ ε γ, 0 ≤ m ε γ
  massLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D₀ ε γ L).J ≤ m ε γ * L
  δ : ℝ → ℝ → ℝ → ℝ
  defectLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D₀ ε γ L).K ≤ δ ε γ L * L
  δVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    δ ε γ L ≤ η

variable {E Emod : ℝ → ℝ → ℝ → ℝ} {nA nB : ℝ → ℝ → ℝ → ℕ}
  {D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))} {F₀ : ℝ → ℝ → ℝ → ℝ → ℝ}

/-- **G109.** Forget the rows that mention `E`, `Emod`, `disc`. -/
def dataOf (H : H5bPinnedRows E Emod nA nB D₀ F₀) : H5bPinnedDataRows nA nB D₀ F₀ where
  Λ := H.Λ
  hΛ := H.hΛ
  lip := H.lip
  m := H.m
  hm := H.hm
  massLin := H.massLin
  δ := H.δ
  defectLin := H.defectLin
  δVanish := H.δVanish

theorem dataOf_Λ (H : H5bPinnedRows E Emod nA nB D₀ F₀) : (dataOf H).Λ = H.Λ := rfl

/-- The data rows with the trivial cutoff row for `E := pinnedSum`, `Emod := 0`, `disc := 0`. -/
noncomputable def withSum (R : H5bPinnedDataRows nA nB D₀ F₀) :
    H5bPinnedRows (fun ε γ L => pinnedSum D₀ F₀ ε γ L) (fun _ _ _ => 0) nA nB D₀ F₀ where
  disc := fun _ _ _ => 0
  cutoff := by
    intro ε γ L
    show |(pinnedSum D₀ F₀ ε γ L - 0) - pinnedSum D₀ F₀ ε γ L| ≤ 0
    simp
  discVanish := by
    intro ε γ _ _ η hη
    exact ⟨0, fun L hL => show (0 : ℝ) ≤ η * L from mul_nonneg hη.le hL⟩
  Λ := R.Λ
  hΛ := R.hΛ
  lip := R.lip
  m := R.m
  hm := R.hm
  massLin := R.massLin
  δ := R.δ
  defectLin := R.defectLin
  δVanish := R.δVanish

/-- **G109.** The data rows alone force the data's spectral sum to be `o(L)` (G108's property,
now without `E`). -/
theorem sumLittleO_of_dataRows (R : H5bPinnedDataRows nA nB D₀ F₀) : SumLittleO D₀ F₀ := by
  intro ε γ hε hγ η hη
  obtain ⟨L₀, h⟩ := h5b_of_pinnedRows (withSum R) ε γ hε hγ η hη
  refine ⟨L₀, fun L hL => ?_⟩
  have h' : |pinnedSum D₀ F₀ ε γ L - 0| ≤ η * L := h L hL
  rwa [sub_zero] at h'

/-- Rebuild the G107 core rows from data rows and the `o(L)` cutoff row. -/
noncomputable def coreOf (R : H5bPinnedDataRows nA nB D₀ F₀)
    (hc : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      coreDisc E Emod nA nB D₀ F₀ ε γ L ≤ η * L) :
    H5bPinnedCore E Emod nA nB D₀ F₀ where
  cutoffVanish := hc
  Λ := R.Λ
  hΛ := R.hΛ
  lip := R.lip
  m := R.m
  hm := R.hm
  massLin := R.massLin
  δ := R.δ
  defectLin := R.defectLin
  δVanish := R.δVanish

/-- **G109.** Pinned rows exist iff the data rows exist and the cutoff discrepancy is `o(L)`. -/
theorem pinned_iff_dataRows_core :
    Nonempty (H5bPinnedRows E Emod nA nB D₀ F₀) ↔
      Nonempty (H5bPinnedDataRows nA nB D₀ F₀) ∧
        ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
          coreDisc E Emod nA nB D₀ F₀ ε γ L ≤ η * L := by
  constructor
  · rintro ⟨H⟩
    exact ⟨⟨dataOf H⟩, (toCore H).cutoffVanish⟩
  · rintro ⟨⟨R⟩, hc⟩
    exact ⟨ofCore (coreOf R hc)⟩

end SteklovAudit.H5PinnedDataRows
