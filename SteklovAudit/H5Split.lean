import Mathlib
import SteklovAudit.H5Compare

/-!
# G2: H5b split into a statement free of `E, Emod` plus the cutoff row

Roadmap item G2. `traceSum` is the finite-cutoff trace comparison
`∑ i, ∑ j, (F a i − F b j) J i j ^ 2` of an `H5bInputs`, and `TraceLittleO` says it is
eventually `≤ η L` (in absolute value) for every `η > 0`.

* `trace_little_o_of_rows`: the rows `pde`, `tail`, `tailVanish`, `lowDefect`, `lipHi`, `lipLo`,
  `lamVanish` alone give `TraceLittleO`. The proof reruns the B4/B5 chain of `h5b_of_inputs` on
  `rowsOnly H`, which copies those rows and replaces the cutoff row by the trivial one
  (`E := traceSum`, `Emod := 0`, `disc := 0`); `rowsOnly` uses neither `H.cutoff` nor
  `H.discVanish`.
* `h5b_of_cutoff_and_trace`: the cutoff row (`cutoff` + `discVanish`) together with
  `TraceLittleO` gives `H5bTarget E Emod`.

So rows 2–5 of the F table yield a statement that never mentions `E − Emod`; all of F2's
"target in disguise" content (`inputs_iff_target`) sits in the cutoff row.

What this file does NOT prove: no row is proved for the Steklov operator of the tetrahedron;
the cutoff row is not weakened here (that is G3); (7.29) and Theorem 1.3 / 11.1 stay conditional.
-/

namespace SteklovAudit.H5Split

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare

/-- The finite-cutoff trace comparison of the data `D` with test `F`. -/
noncomputable def traceSum (nA nB : ℝ → ℝ → ℝ → ℕ)
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F : ℝ → ℝ → ℝ → ℝ → ℝ) (ε γ L : ℝ) : ℝ :=
  ∑ i, ∑ j, (F ε γ L ((D ε γ L).a i) - F ε γ L ((D ε γ L).b j)) * (D ε γ L).J i j ^ 2

/-- The trace comparison is `o(L)` for each `ε, γ > 0`. Mentions neither `E` nor `Emod`. -/
def TraceLittleO (nA nB : ℝ → ℝ → ℝ → ℕ)
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    |traceSum nA nB D F ε γ L| ≤ η * L

/-- The rows of `H` other than the cutoff row, with the trivial cutoff row
(`E := traceSum`, `Emod := 0`, `disc := 0`). Uses neither `H.cutoff` nor `H.discVanish`. -/
noncomputable def rowsOnly {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) :
    H5bInputs (traceSum H.nA H.nB H.D H.F) (fun _ _ _ => 0) where
  nA := H.nA
  nB := H.nB
  D := H.D
  F := H.F
  disc := fun _ _ _ => 0
  cutoff := by intro ε γ L; simp [traceSum]
  discVanish := fun _ _ _ _ η hη => ⟨0, fun L hL => by
    show (0 : ℝ) ≤ η * L
    exact mul_nonneg hη.le hL⟩
  Cm := H.Cm
  Ck := H.Ck
  hCm := H.hCm
  pde := H.pde
  τ := H.τ
  tail := H.tail
  tailVanish := H.tailVanish
  κ2 := H.κ2
  lowDefect := H.lowDefect
  Λ0 := H.Λ0
  hΛ0 := H.hΛ0
  lam := H.lam
  hlam := H.hlam
  lipHi := H.lipHi
  lipLo := H.lipLo
  lamVanish := H.lamVanish

/-- **G2.** Rows 2–5 (mass/defect, tail, low-energy defect, Lipschitz) give `TraceLittleO`. -/
theorem trace_little_o_of_rows {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) :
    TraceLittleO H.nA H.nB H.D H.F := by
  unfold TraceLittleO
  intro ε γ hε hγ η hη
  obtain ⟨L₀, h⟩ := h5b_of_inputs (rowsOnly H) ε γ hε hγ η hη
  exact ⟨L₀, fun L hL => by simpa using h L hL⟩

/-- **G2.** The cutoff row plus `TraceLittleO` give the H5b target. -/
theorem h5b_of_cutoff_and_trace {E Emod : ℝ → ℝ → ℝ → ℝ} (nA nB : ℝ → ℝ → ℝ → ℕ)
    (D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L)))
    (F : ℝ → ℝ → ℝ → ℝ → ℝ) (disc : ℝ → ℝ → ℝ → ℝ)
    (hcut : ∀ ε γ L : ℝ,
      |(E ε γ L - Emod ε γ L) - traceSum nA nB D F ε γ L| ≤ disc ε γ L)
    (hdisc : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      disc ε γ L ≤ η * L)
    (htr : TraceLittleO nA nB D F) : H5bTarget E Emod := by
  unfold H5bTarget
  intro ε γ hε hγ η hη
  obtain ⟨L1, h1⟩ := hdisc ε γ hε hγ (η / 2) (half_pos hη)
  obtain ⟨L2, h2⟩ := htr ε γ hε hγ (η / 2) (half_pos hη)
  refine ⟨max L1 L2, fun L hL => ?_⟩
  have a1 := h1 L (le_trans (le_max_left _ _) hL)
  have a2 := h2 L (le_trans (le_max_right _ _) hL)
  have a3 := hcut ε γ L
  have a4 := abs_sub_abs_le_abs_sub (E ε γ L - Emod ε γ L) (traceSum nA nB D F ε γ L)
  have a5 : η / 2 * L + η / 2 * L = η * L := by ring
  linarith

/-- `h5b_of_inputs` recovered through the split: cutoff row, then rows 2–5. -/
theorem h5b_via_split {E Emod : ℝ → ℝ → ℝ → ℝ} (H : H5bInputs E Emod) : H5bTarget E Emod :=
  h5b_of_cutoff_and_trace H.nA H.nB H.D H.F H.disc H.cutoff H.discVanish
    (trace_little_o_of_rows H)

end SteklovAudit.H5Split
