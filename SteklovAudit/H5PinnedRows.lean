import Mathlib
import SteklovAudit.H5GlobalLipRows

/-!
# G101: the G90 rows for pinned cutoff data

Roadmap item G101. `H5bPinnedRows E Emod nA nB D₀ F₀` has the fields of `H5bGlobalLipRows`
(G90, `H5GlobalLipRows.lean`) except `nA`, `nB`, `D`, `F`: the cutoff data `D₀` and the
function `F₀` are *parameters* of the structure, not fields the rows may choose. `toRows`
copies a pinned family into `H5bGlobalLipRows` with `D := D₀`, `F := F₀`, and
`h5b_of_pinnedRows` gives `H5bTarget E Emod`.

What this file does NOT prove: no row is proved for any operator. The cutoff data of the
Steklov operator of the tetrahedron is not defined in Lean, so the pinned form is stated for
arbitrary given data `D₀ F₀`; which data the paper pins is open. No DtN operator is
constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5PinnedRows

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows

/-- The G90 rows with the cutoff data `D₀` and the function `F₀` fixed in advance. -/
structure H5bPinnedRows (E Emod : ℝ → ℝ → ℝ → ℝ) (nA nB : ℝ → ℝ → ℝ → ℕ)
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
  /-- Row: the overlap mass of the pinned data is `O(L)` (named hypothesis). -/
  massLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D₀ ε γ L).J ≤ m ε γ * L
  δ : ℝ → ℝ → ℝ → ℝ
  /-- Row: the Hilbert–Schmidt defect of the pinned data is `δ ε γ L * L` (named hypothesis). -/
  defectLin : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D₀ ε γ L).K ≤ δ ε γ L * L
  /-- Row: `δ ε γ L → 0` as `L → ∞` (named hypothesis). -/
  δVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    δ ε γ L ≤ η

variable {E Emod : ℝ → ℝ → ℝ → ℝ} {nA nB : ℝ → ℝ → ℝ → ℕ}
  {D₀ : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))} {F₀ : ℝ → ℝ → ℝ → ℝ → ℝ}

/-- **G101.** A pinned family is a G90 family whose data is `D₀`, `F₀`. -/
noncomputable def toRows (H : H5bPinnedRows E Emod nA nB D₀ F₀) : H5bGlobalLipRows E Emod where
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
  massLin := H.massLin
  δ := H.δ
  defectLin := H.defectLin
  δVanish := H.δVanish

theorem toRows_D (H : H5bPinnedRows E Emod nA nB D₀ F₀) : (toRows H).D = D₀ := rfl

theorem toRows_F (H : H5bPinnedRows E Emod nA nB D₀ F₀) : (toRows H).F = F₀ := rfl

/-- **G101.** The pinned rows give the H5b comparison (7.29). -/
theorem h5b_of_pinnedRows (H : H5bPinnedRows E Emod nA nB D₀ F₀) : H5bTarget E Emod :=
  h5b_of_globalLipRows (toRows H)

end SteklovAudit.H5PinnedRows
