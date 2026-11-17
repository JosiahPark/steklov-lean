import Mathlib

/-!
# G74: the joint row is strictly weaker than "high row at some `M`, low row at every `M`"

G69 (`H5HiLinear.lean`) asks for the high-energy row at some split energy `M` (`hiVanish`) and for
the low-energy row at every `M` (`lowVanish`). G72 (`H5Joint.lean`) merges them into one joint row
that needs the low-energy term to be `o(L)` only at the split energy actually chosen. This file
shows, on the row's shape alone, that the joint form is strictly weaker: with a zero high-energy
term (`hiZero`) and a low-energy term that is `o(L)` only for `M ≤ 0` (`loBad`), the joint row holds
while "low row at every `M`" fails.

What this file does NOT prove: it is a statement about the shape of a hypothesis on toy scalar
functions. It does not prove the joint row, the high or low row, (7.29), any `[H…]`, or the main
theorem (Theorem 1.3 / 11.1) for the actual Dirichlet-to-Neumann operator, which is not defined in
Lean.
-/

namespace SteklovAudit.H5JointStrict

/-- A high-energy term that vanishes identically. -/
def hiZero (_M _L : ℝ) : ℝ := 0

/-- A low-energy term that is `o(L)` only for split energies `M ≤ 0`. -/
noncomputable def loBad (M L : ℝ) : ℝ := if 0 < M then L else 0

/-- The joint row holds for `hiZero`, `loBad`: take `M = 0`, `L₀ = 0`. -/
theorem joint_holds :
    ∀ η : ℝ, 0 < η → ∃ M L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → hiZero M L + loBad M L ≤ η * L := by
  intro η hη
  refine ⟨0, 0, fun L hL => ?_⟩
  have h0 : hiZero 0 L + loBad 0 L = 0 := by
    simp [hiZero, loBad]
  rw [h0]
  exact mul_nonneg hη.le hL

/-- The low row at every `M` fails for `loBad`: at `M = 1`, `η = 1/2`. -/
theorem lowEvery_fails :
    ¬ ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → loBad M L ≤ η * L := by
  intro h
  obtain ⟨L₀, hL₀⟩ := h 1 (1 / 2) (by norm_num)
  have h1 := hL₀ (max L₀ 1) (le_max_left L₀ 1)
  have hge : (1 : ℝ) ≤ max L₀ 1 := le_max_right L₀ 1
  have e : loBad 1 (max L₀ 1) = max L₀ 1 := by
    unfold loBad
    exact if_pos one_pos
  rw [e] at h1
  linarith

/-- G74: the joint row holds while "low row at every `M`" fails.
F table text: the low-energy row is needed only at the split energy used for the high row. -/
theorem joint_strictly_weaker :
    (∀ η : ℝ, 0 < η → ∃ M L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → hiZero M L + loBad M L ≤ η * L) ∧
      ¬ ∀ M η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → loBad M L ≤ η * L :=
  ⟨joint_holds, lowEvery_fails⟩

end SteklovAudit.H5JointStrict
