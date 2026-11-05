import Mathlib
import SteklovAudit.H5Split

/-!
# G3: the cutoff row of H5b with a two-parameter (`δ`-smoothed) cutoff

Roadmap item G3. `CutoffRowδ E Emod` replaces the F1 cutoff row (`cutoff` + `discVanish` of
`H5bInputs`) by a two-parameter input in the spirit of G1 (`TwoParameterSmoothing.lean`): for each
smoothing parameter `δ ∈ (0, δ₀]` a finite cutoff (data `D δ`, test `F δ`) such that

* `cutoff`: eventually `|(E − Emod) − trace(F δ)| ≤ (C δ + η) L` for every `η > 0`, with one
  constant `C ε γ` for all `δ` (a cutoff error of size `C δ L` is allowed, not only `o(L)`);
* `trace`: for each `δ`, eventually `|trace(F δ)| ≤ (ω δ + η) L`;
* `ωVanish`: `ω δ → 0` as `δ ↓ 0`.

Proved here:

* `target_of_cutoffRowδ`: `CutoffRowδ E Emod` gives `H5bTarget E Emod` (direct `δ`-then-`L` argument).
* `cutoffRowδ_of_inputs`: every `H5bInputs E Emod` gives a `CutoffRowδ E Emod` (constant in `δ`,
  `C = 0`, `ω = 0`; the `trace` field comes from G2's `trace_little_o_of_rows`). So the new row is
  no stronger than the F1 rows: on paper it asks less of the cutoff (an `O(δ L)` error is allowed).
* `cutoffRowδ_iff_target` (audit, as in F2): `Nonempty (CutoffRowδ E Emod) ↔ H5bTarget E Emod`.
  As with F1, the empty cutoff makes the row the target itself, because Lean cannot force `D δ` to be
  the actual spectral data; the gain over F1 is only visible in the paper review of the row.

What this file does NOT prove: no field is proved for the Steklov operator of the tetrahedron; no
DtN operator, wave group or smoothing family is constructed; (7.29), `[H5]` and Theorem 1.3 / 11.1
remain conditional.
-/

namespace SteklovAudit.H5CutoffSmoothed

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5Split

/-- The two-parameter cutoff row: a `δ`-family of finite cutoffs with an `O(δ L)` cutoff error
uniform in `δ`, per-`δ` trace bound `ω δ`, and `ω δ → 0`. -/
structure CutoffRowδ (E Emod : ℝ → ℝ → ℝ → ℝ) where
  δ₀ : ℝ
  hδ₀ : 0 < δ₀
  C : ℝ → ℝ → ℝ
  nA : ℝ → ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℝ → ℕ
  D : ∀ δ ε γ L : ℝ, Data (Fin (nA δ ε γ L)) (Fin (nB δ ε γ L))
  F : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  ω : ℝ → ℝ → ℝ → ℝ
  /-- Cutoff error `O(δ L)`, one constant for all `δ`. -/
  cutoff : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ η : ℝ, 0 < η →
    ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      |(E ε γ L - Emod ε γ L) - traceSum (nA δ) (nB δ) (D δ) (F δ) ε γ L| ≤ (C ε γ * δ + η) * L
  /-- For each `δ`, the trace comparison is at most `(ω δ + η) L` eventually. -/
  trace : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ η : ℝ, 0 < η →
    ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → |traceSum (nA δ) (nB δ) (D δ) (F δ) ε γ L| ≤ (ω ε γ δ + η) * L
  ωVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η →
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ω ε γ δ ≤ η

/-- **G3.** The two-parameter cutoff row gives the H5b target. -/
theorem target_of_cutoffRowδ {E Emod : ℝ → ℝ → ℝ → ℝ} (R : CutoffRowδ E Emod) :
    H5bTarget E Emod := by
  unfold H5bTarget
  intro ε γ hε hγ η hη
  obtain ⟨δ₁, hδ₁, hω⟩ := R.ωVanish ε γ hε hγ (η / 4) (by positivity)
  obtain ⟨δ, hδpos, hδ0, hδ1, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ R.δ₀ ∧ δ ≤ δ₁ ∧
      δ ≤ η / (4 * (|R.C ε γ| + 1)) :=
    ⟨min (min R.δ₀ δ₁) (η / (4 * (|R.C ε γ| + 1))), lt_min (lt_min R.hδ₀ hδ₁) (by positivity),
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _), min_le_right _ _⟩
  have hCδ : R.C ε γ * δ ≤ η / 4 := by
    have h1 : R.C ε γ * δ ≤ |R.C ε γ| * δ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hδpos.le
    have h2 : δ * (4 * (|R.C ε γ| + 1)) ≤ η := (le_div_iff₀ (by positivity)).mp hδη
    have h3 : δ * (4 * (|R.C ε γ| + 1)) = 4 * (|R.C ε γ| * δ) + 4 * δ := by ring
    linarith
  obtain ⟨L1, h1⟩ := R.cutoff ε γ hε hγ δ hδpos hδ0 (η / 4) (by positivity)
  obtain ⟨L2, h2⟩ := R.trace ε γ hε hγ δ hδpos hδ0 (η / 4) (by positivity)
  refine ⟨max (max L1 L2) 0, fun L hL => ?_⟩
  have hL1 : L1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : L2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL0 : 0 ≤ L := le_trans (le_max_right _ _) hL
  have a1 := h1 L hL1
  have a2 := h2 L hL2
  have hωδ := hω δ hδpos hδ1
  have b1 : (R.C ε γ * δ + η / 4) * L ≤ (η / 4 + η / 4) * L :=
    mul_le_mul_of_nonneg_right (by linarith) hL0
  have b2 : (R.ω ε γ δ + η / 4) * L ≤ (η / 4 + η / 4) * L :=
    mul_le_mul_of_nonneg_right (by linarith) hL0
  have a4 := abs_sub_abs_le_abs_sub (E ε γ L - Emod ε γ L)
    (traceSum (R.nA δ) (R.nB δ) (R.D δ) (R.F δ) ε γ L)
  have a5 : (η / 4 + η / 4) * L + (η / 4 + η / 4) * L = η * L := by ring
  linarith

/-- **G3.** The F1 rows give the two-parameter row (constant in `δ`, `C = 0`, `ω = 0`), so the
new row is no stronger than the old one. -/
noncomputable def cutoffRowδ_of_inputs {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) :
    CutoffRowδ E Emod where
  δ₀ := 1
  hδ₀ := one_pos
  C := fun _ _ => 0
  nA := fun _ => H.nA
  nB := fun _ => H.nB
  D := fun _ => H.D
  F := fun _ => H.F
  ω := fun _ _ _ => 0
  cutoff := by
    intro ε γ hε hγ δ _ _ η hη
    obtain ⟨L₀, h⟩ := H.discVanish ε γ hε hγ η hη
    refine ⟨L₀, fun L hL => ?_⟩
    show |(E ε γ L - Emod ε γ L) - traceSum H.nA H.nB H.D H.F ε γ L| ≤ (0 * δ + η) * L
    have hc : |(E ε γ L - Emod ε γ L) - traceSum H.nA H.nB H.D H.F ε γ L| ≤ H.disc ε γ L :=
      H.cutoff ε γ L
    have hd := h L hL
    have he : (0 * δ + η) * L = η * L := by ring
    linarith
  trace := by
    intro ε γ hε hγ δ _ _ η hη
    obtain ⟨L₀, h⟩ := trace_little_o_of_rows H ε γ hε hγ η hη
    refine ⟨L₀, fun L hL => ?_⟩
    show |traceSum H.nA H.nB H.D H.F ε γ L| ≤ (0 + η) * L
    rw [zero_add]
    exact h L hL
  ωVanish := fun _ _ _ _ η hη => ⟨1, one_pos, fun _ _ _ => hη.le⟩

/-- Audit (as F2): from the target alone, with the empty cutoff for every `δ`. -/
noncomputable def cutoffRowδ_of_target {E Emod : ℝ → ℝ → ℝ → ℝ} (hT : H5bTarget E Emod) :
    CutoffRowδ E Emod where
  δ₀ := 1
  hδ₀ := one_pos
  C := fun _ _ => 0
  nA := fun _ _ _ _ => 0
  nB := fun _ _ _ _ => 0
  D := fun _ _ _ _ => emptyData
  F := fun _ _ _ _ _ => 0
  ω := fun _ _ _ => 0
  cutoff := by
    intro ε γ hε hγ δ _ _ η hη
    obtain ⟨L₀, h⟩ := hT ε γ hε hγ η hη
    exact ⟨L₀, fun L hL => by simpa [traceSum] using h L hL⟩
  trace := by
    intro ε γ _ _ δ _ _ η hη
    exact ⟨0, fun L hL => by simpa [traceSum] using mul_nonneg hη.le hL⟩
  ωVanish := fun _ _ _ _ η hη => ⟨1, one_pos, fun _ _ _ => hη.le⟩

/-- **G3 audit.** In Lean the two-parameter row holds exactly when the target holds. -/
theorem cutoffRowδ_iff_target (E Emod : ℝ → ℝ → ℝ → ℝ) :
    Nonempty (CutoffRowδ E Emod) ↔ H5bTarget E Emod :=
  ⟨fun ⟨R⟩ => target_of_cutoffRowδ R, fun h => ⟨cutoffRowδ_of_target h⟩⟩

end SteklovAudit.H5CutoffSmoothed
