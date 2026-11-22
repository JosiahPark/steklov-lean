import Mathlib
import SteklovAudit.AffineCutoffTail
import SteklovAudit.H5CutoffInterface

/-!
# The affine probes as an exact test case of estimate (i) (roadmap item G117)

The constant family built from the four affine probes (G115; Parseval as a named hypothesis) has
cutoff ratio `16 Lf / (a² (L − μaff))`. It satisfies estimate (i) of G116 (`RatioLittleO`) with rate
`O(1/L)`: for `L ≥ 2 μaff + 1` the ratio is at most `32 Lf / (a² L)`.

What this file does NOT prove: estimate (ii) (`TraceMatches`), anything about the edge family the
paper needs, Parseval for the probes, (7.29), H5, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.H5CutoffAffineInstance

open SteklovAudit.CountableCutoffTail SteklovAudit.AffineCutoffTail SteklovAudit.H5CutoffInterface

variable {ι : Type*} {lam : ι → ℝ} {J : ι → Fin 4 → ℝ} {a : ℝ}

/-- The constant family from the four affine probes (hypothesis-parametrized). -/
noncomputable def affineFamily (P : AffineProbeParseval lam J a) (ha : 0 < a) (F : ℝ → ℝ)
    (Lf : ℝ) (hLf : 0 ≤ Lf) (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) :
    H5EdgeFamilyCutoff ι (Fin 4) where
  X := fun _ => certOf P
  F := fun _ => F
  Lip := fun _ => Lf
  muStar := fun _ => muAff a
  Lgap := muAff a + 1
  hLip := fun _ => hLf
  hF := fun _ => hF
  hmu := fun _ j => muVec_le a ha j
  hgap := fun L (hL : muAff a + 1 ≤ L) => show muAff a < L by linarith

theorem affine_ratio_eq (P : AffineProbeParseval lam J a) (ha : 0 < a) (F : ℝ → ℝ) (Lf : ℝ)
    (hLf : 0 ≤ Lf) (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (L : ℝ) :
    (affineFamily P ha F Lf hLf hF).ratio L = Lf * (16 / a ^ 2) / (L - muAff a) := rfl

/-- **G117.** For `L ≥ 2 μaff + 1` the ratio is at most `32 Lf / (a² L)`. -/
theorem affine_ratio_O_inv (P : AffineProbeParseval lam J a) (ha : 0 < a) (F : ℝ → ℝ) (Lf : ℝ)
    (hLf : 0 ≤ Lf) (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (L : ℝ) (hL : 2 * muAff a + 1 ≤ L) :
    (affineFamily P ha F Lf hLf hF).ratio L ≤ 32 * Lf / (a ^ 2 * L) := by
  rw [affine_ratio_eq]
  have hμ := (muAff_pos a ha).le
  have hLpos : 0 < L := by linarith
  have hhalf : 0 < L / 2 := by linarith
  have hle : L / 2 ≤ L - muAff a := by linarith
  have hnum : 0 ≤ Lf * (16 / a ^ 2) := mul_nonneg hLf (by positivity)
  have step : Lf * (16 / a ^ 2) / (L - muAff a) ≤ Lf * (16 / a ^ 2) / (L / 2) := by
    first
      | exact div_le_div_of_nonneg_left hnum hhalf hle
      | exact div_le_div_of_le_left hnum hhalf hle
      | (rw [div_le_div_iff₀ (by linarith) hhalf]; nlinarith)
  have ha' : a ≠ 0 := ha.ne'
  have hL' : L ≠ 0 := hLpos.ne'
  have e : Lf * (16 / a ^ 2) / (L / 2) = 32 * Lf / (a ^ 2 * L) := by
    first
      | ring
      | (field_simp; done)
      | (field_simp; ring)
  linarith [step, e.le, e.ge]

/-- **G117.** The affine family satisfies estimate (i) of G116. -/
theorem affine_ratioLittleO (P : AffineProbeParseval lam J a) (ha : 0 < a) (F : ℝ → ℝ) (Lf : ℝ)
    (hLf : 0 ≤ Lf) (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) :
    (affineFamily P ha F Lf hLf hF).RatioLittleO := by
  intro η hη
  have hK : 0 ≤ 32 * Lf / a ^ 2 := div_nonneg (mul_nonneg (by norm_num) hLf) (sq_nonneg a)
  refine ⟨max (max (2 * muAff a + 1) 1) (32 * Lf / a ^ 2 / η), fun L hL => ?_⟩
  have h1 : 2 * muAff a + 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have h2 : (1 : ℝ) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have h3 : 32 * Lf / a ^ 2 / η ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := by linarith
  have r := affine_ratio_O_inv P ha F Lf hLf hF L h1
  have e : 32 * Lf / (a ^ 2 * L) = 32 * Lf / a ^ 2 / L := by
    rw [div_div]
  have s1 : 32 * Lf / a ^ 2 / L ≤ 32 * Lf / a ^ 2 := div_le_self hK h2
  have s2 : 32 * Lf / a ^ 2 ≤ η * L := by
    have h4 : 32 * Lf / a ^ 2 ≤ L * η := by
      first
        | exact (div_le_iff₀ hη).1 h3
        | exact (div_le_iff hη).1 h3
    linarith
  linarith [r, e.le, e.ge, s1, s2]

end SteklovAudit.H5CutoffAffineInstance
