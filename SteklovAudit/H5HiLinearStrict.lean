import Mathlib

/-!
# G71: the G69 high row is strictly weaker than the G66 tail row

G66 (`H5TailEv.lean`) asks for a defect tail `τ ε γ M L` that becomes small along `L → ∞` for some
`M` (`tailVanish`), and pays for the high-energy mass with the `O((1 + L)²)` PDE mass bound. G69
(`H5HiLinear.lean`) replaces this by one product row `Λ0 · √(τ · mHi) ≤ δ · L` at a single `M`, with
a separate high-energy mass `mHi`. This file shows, on the row's shape alone, that the G69 form is
strictly weaker: with a tail that never decays (`constTail = 1`) and a high-energy mass that is
`O(1)` (`unitMass = 1`), the G69 product row holds for every `Λ ≥ 0`, while the G66 tail row fails.

What this file does NOT prove: it is a statement about the shape of a hypothesis on toy scalar
functions. It does not prove the high row, the tail row, (7.29), any `[H…]`, or the main theorem
(Theorem 1.3 / 11.1) for the actual Dirichlet-to-Neumann operator, which is not defined in Lean.
-/

namespace SteklovAudit.H5HiLinearStrict

/-- A defect tail that never decays. -/
def constTail (_M _L : ℝ) : ℝ := 1

/-- A high-energy mass that is `O(1)`, not `O(L²)`. -/
def unitMass (_M _L : ℝ) : ℝ := 1

/-- The G69 product row holds for `constTail`, `unitMass`: `M = 0`, `L₀ = Λ / δ`. -/
theorem constTail_hiVanish :
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ δ : ℝ, 0 < δ → ∃ M L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      Λ * Real.sqrt (constTail M L * unitMass M L) ≤ δ * L := by
  intro Λ _hΛ δ hδ
  refine ⟨0, Λ / δ, fun L hL => ?_⟩
  have hs : Real.sqrt (constTail 0 L * unitMass 0 L) = 1 := by
    simp [constTail, unitMass]
  rw [hs, mul_one]
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have e : δ * (Λ / δ) = Λ := by
    first
      | field_simp
      | (field_simp; ring)
  have hm : δ * (Λ / δ) ≤ δ * L := mul_le_mul_of_nonneg_left hL hδ.le
  linarith

/-- The G66 tail row fails for `constTail`: it is never `≤ 1/2`. -/
theorem constTail_not_tailEv :
    ¬ ∃ M L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → constTail M L ≤ 1 / 2 := by
  rintro ⟨M, L₀, h⟩
  have h1 := h L₀ le_rfl
  unfold constTail at h1
  norm_num at h1

/-- G71: the G69 high row (here at `Λ = 1`) holds while the G66 tail row fails.
F table text: the high-energy row can hold with no tail decay at all if the high-energy mass is
`o(L²)`. -/
theorem hiL_strictly_weaker :
    (∀ δ : ℝ, 0 < δ → ∃ M L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      1 * Real.sqrt (constTail M L * unitMass M L) ≤ δ * L) ∧
      ¬ ∃ M L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → constTail M L ≤ 1 / 2 :=
  ⟨constTail_hiVanish 1 zero_le_one, constTail_not_tailEv⟩

end SteklovAudit.H5HiLinearStrict
