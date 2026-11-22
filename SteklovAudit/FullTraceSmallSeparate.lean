import Mathlib
import SteklovAudit.H5CutoffTerminal

/-!
# Row (iii) is not the H5 target in disguise (roadmap item G132)

G122's estimate (iii) `FullTraceSmall` (full probe trace `S_L = o(L)`) is a statement about the probe
family alone. Here an explicit `H5EdgeFamilyCutoff` with zero weights (allowed by
`CountableCutoffTail.Cert`) has `S_L = 0` for all `L`: it satisfies (i) `RatioLittleO` (`ratio_small`)
and (iii) (`fullTraceSmall_zero`), while the discrepancy `idD L = L` is not `o(L)` (`not_littleO_idD`).
Hence (ii) `TraceMatches idD` fails (`traceMatches_fails`): (ii) is the only link from the probe family to
`D`, and (iii) carries no information about `E − E_mod` on its own.

What this file does NOT prove: anything about the actual edge family, the tetrahedron–wedge
discrepancy, (i), (ii) or (iii) for the Steklov problem, (7.29), H5, or Theorem 1.3 / 11.1. The
family below is a toy with zero weights.
-/

namespace SteklovAudit.FullTraceSmallSeparate

open SteklovAudit.H5CutoffInterface SteklovAudit.CountableCutoffTail

/-- The zero certificate: one eigenvalue, one probe, weight `0`. -/
noncomputable def zeroCert : Cert Unit Unit where
  lam := fun _ => 0
  mu := fun _ => 0
  w := fun _ _ => 0
  M := 0
  E := 0
  hw := fun _ _ => le_refl 0
  hM := fun s => by simp
  hE := fun s => by simp

/-- The constant family with the zero certificate, `F L x = x`, `Lip = 1`, `μ* = 0`, `Lgap = 1`. -/
noncomputable def zeroFamily : H5EdgeFamilyCutoff Unit Unit where
  X := fun _ => zeroCert
  F := fun _ x => x
  Lip := fun _ => 1
  muStar := fun _ => 0
  Lgap := 1
  hLip := fun _ => zero_le_one
  hF := fun _ x y => by simp
  hmu := fun _ _ => le_refl _
  hgap := fun L hL => by
    show (0 : ℝ) < L
    linarith

/-- The discrepancy `D L = L`. -/
def idD : ℝ → ℝ := fun L => L

theorem S_zero (L : ℝ) : (zeroFamily.X L).S (zeroFamily.F L) = 0 := by
  first
    | simp [zeroFamily, zeroCert, Cert.S, Cert.centered]
    | (unfold Cert.S Cert.centered zeroFamily zeroCert; simp)

/-- **G132.** (iii) holds for the zero family. -/
theorem fullTraceSmall_zero : zeroFamily.FullTraceSmall := by
  intro η hη
  refine ⟨0, fun L hL => ?_⟩
  rw [S_zero L, abs_zero]
  exact mul_nonneg hη.le hL

/-- **G132.** (i) holds for the zero family (the ratio is `0`). -/
theorem ratio_small : zeroFamily.RatioLittleO := by
  intro η hη
  refine ⟨0, fun L hL => ?_⟩
  have h : zeroFamily.ratio L = 0 := by
    first
      | simp [H5EdgeFamilyCutoff.ratio, zeroFamily, zeroCert]
      | (unfold H5EdgeFamilyCutoff.ratio zeroFamily zeroCert; simp)
  rw [h]
  exact mul_nonneg hη.le hL

/-- **G132.** `D L = L` is not `o(L)`. -/
theorem not_littleO_idD :
    ¬ (∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |idD L| ≤ η * L) := by
  intro h
  obtain ⟨L₀, hL₀⟩ := h (1 / 2) (by norm_num)
  have h1 := hL₀ (max L₀ 1) (le_max_left _ _)
  have h2 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  unfold idD at h1
  rw [abs_of_pos (by linarith)] at h1
  linarith

/-- **G132.** (ii) fails: with (i) and (iii) it would make `idD` `o(L)`. -/
theorem traceMatches_fails : ¬ zeroFamily.TraceMatches idD := fun h =>
  not_littleO_idD (zeroFamily.h5_of_cutoff_route idD ratio_small h fullTraceSmall_zero)

/-- **G132.** Summary: (i) and (iii) hold, the conclusion fails for `D = idD`. -/
theorem fullTraceSmall_not_target :
    zeroFamily.RatioLittleO ∧ zeroFamily.FullTraceSmall ∧
      ¬ (∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |idD L| ≤ η * L) :=
  ⟨ratio_small, fullTraceSmall_zero, not_littleO_idD⟩

end SteklovAudit.FullTraceSmallSeparate
