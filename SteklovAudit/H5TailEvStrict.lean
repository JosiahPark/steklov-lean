import Mathlib

/-!
# G68: the eventual tail row is strictly weaker than the L-uniform one

The F-table row "High-energy defect tail τ(M), σ(M) → 0" was stated in `H5bLowLInputs` (G62) with a
tail bound `τ ε γ M` that is uniform in every `L`. G66 (`H5TailEv.lean`) only asks for a tail
`τ ε γ M L` (for `1 ≤ L`) that becomes small along `L → ∞` for some `M`. This file shows, on the
row's shape alone, that the G66 form is strictly weaker: a function `t M L` (standing for
`hs2 (mask (hiE _ M) K)` at scale `L`) can satisfy the eventual form while no `L`-uniform tail
`τ M → 0` dominates it.

`bumpTail M L` puts unit defect mass at energy `1 / (2 - L)` for `L ∈ [1, 2)` and none for `L ≥ 2`.

What this file does NOT prove: it is a statement about the shape of a hypothesis on toy scalar
functions. It does not prove the tail row, (7.29), any `[H…]`, or the main theorem
(Theorem 1.3 / 11.1) for the actual Dirichlet-to-Neumann operator, which is not defined in Lean.
-/

namespace SteklovAudit.H5TailEvStrict

/-- Unit defect mass at energy `1 / (2 - L)` for `L ∈ [1, 2)`, none otherwise. -/
noncomputable def bumpTail (M L : ℝ) : ℝ :=
  if 1 ≤ L ∧ L < 2 ∧ M < 1 / (2 - L) then 1 else 0

/-- The eventual (G66) tail form holds for `bumpTail`, with `M = 0`, `L₀ = 2`. -/
theorem bumpTail_eventual :
    ∀ δ : ℝ, 0 < δ → ∃ M L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → bumpTail M L ≤ δ := by
  intro δ hδ
  refine ⟨0, 2, fun L hL => ?_⟩
  have h : ¬ (1 ≤ L ∧ L < 2 ∧ (0 : ℝ) < 1 / (2 - L)) := by
    rintro ⟨_, h2, _⟩
    linarith
  unfold bumpTail
  rw [if_neg h]
  exact hδ.le

/-- No `L`-uniform tail `τ M` with `τ M → 0` (in the G62 sense) dominates `bumpTail`. -/
theorem bumpTail_not_uniform :
    ¬ ∃ τ : ℝ → ℝ, (∀ M L : ℝ, 1 ≤ L → bumpTail M L ≤ τ M) ∧
      ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, τ M ≤ δ := by
  rintro ⟨τ, hτ, hv⟩
  obtain ⟨M, hM⟩ := hv (1 / 2) (by norm_num)
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have hMle : M ≤ |M| := le_abs_self M
  have hapos : 0 < |M| + 1 := by linarith
  have hinv_pos : 0 < 1 / (|M| + 1) := by positivity
  have hinv_le : 1 / (|M| + 1) ≤ 1 := by
    first
      | (rw [div_le_iff₀ hapos]; linarith)
      | (rw [div_le_one hapos]; linarith)
      | exact (div_le_one hapos).mpr (by linarith)
  have h1 : 1 ≤ 2 - 1 / (|M| + 1) := by linarith
  have h2 : 2 - 1 / (|M| + 1) < 2 := by linarith
  have h3 : M < 1 / (2 - (2 - 1 / (|M| + 1))) := by
    have e : 2 - (2 - 1 / (|M| + 1)) = 1 / (|M| + 1) := by ring
    rw [e, one_div_one_div]
    linarith
  have hb : bumpTail M (2 - 1 / (|M| + 1)) = 1 := by
    unfold bumpTail
    rw [if_pos ⟨h1, h2, h3⟩]
  have hle := hτ M (2 - 1 / (|M| + 1)) h1
  linarith

/-- G68: the eventual tail row holds for `bumpTail` while no `L`-uniform tail does.
F table text: the tail row needs only `τ(M, L) → 0` along `L → ∞` for some `M`, not a bound
uniform in `L ≥ 1`. -/
theorem tailEv_strictly_weaker :
    (∀ δ : ℝ, 0 < δ → ∃ M L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → bumpTail M L ≤ δ) ∧
      ¬ ∃ τ : ℝ → ℝ, (∀ M L : ℝ, 1 ≤ L → bumpTail M L ≤ τ M) ∧
        ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, τ M ≤ δ :=
  ⟨bumpTail_eventual, bumpTail_not_uniform⟩

end SteklovAudit.H5TailEvStrict
