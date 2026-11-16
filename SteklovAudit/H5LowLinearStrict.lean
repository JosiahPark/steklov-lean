import Mathlib
import SteklovAudit.H5EvLowCountIndep

/-!
# G65: the linear low count is strictly weaker than the L-uniform low count

Roadmap item G65. G64 (`H5LowLinearRows`) derives the G62 low rows from a low-energy count that may
grow linearly, `card {i | a i ≤ M} ≤ c(M) · (1 + |L|)`, instead of the L-uniform `lowCount` field.
Here we check on G61's test family `flatD ⌊L⌋₊` that this is a strict weakening:
`flatD_linearCount` shows the linear count holds with `c = 1` for every `M` and `L`, while G61's
`flatD_not_lowCount` shows no constant bounds the count of eigenvalues `≤ 0` uniformly in `L`.
`linearCount_strictly_weaker` packages both facts.

What this file does NOT prove: `flatD` is a test family, not a model of the Steklov spectrum; no row
(low count, linear low count, defect, mass, normalization) is proved for any actual coupling or for
the Steklov operator of the tetrahedron; no Dirichlet-to-Neumann operator is constructed; (7.29),
every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5LowLinearStrict

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5EvLowCountIndep

/-- `⌊L⌋₊ ≤ 1 + |L|` for every real `L`. -/
theorem floor_le_one_add_abs (L : ℝ) : (⌊L⌋₊ : ℝ) ≤ 1 + |L| := by
  rcases le_or_lt 0 L with hL | hL
  · have h1 : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hL
    have h2 : L ≤ |L| := le_abs_self L
    linarith
  · have h0 : ⌊L⌋₊ = 0 := Nat.floor_of_nonpos hL.le
    rw [h0, Nat.cast_zero]
    positivity

/-- The number of eigenvalues of `flatD n` below any level is at most `n`. -/
theorem flatD_filter_card_le (n : ℕ) (M : ℝ) :
    (Finset.univ.filter fun i => (flatD n).a i ≤ M).card ≤ n := by
  first
    | exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    | (have h := Finset.card_filter_le (Finset.univ : Finset (Fin n))
          (fun i => (flatD n).a i ≤ M)
       rw [Finset.card_univ, Fintype.card_fin] at h
       exact h)
    | simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n))
          (fun i => (flatD n).a i ≤ M)

/-- **G65 (a).** On `flatD ⌊L⌋₊` the linear low count of G64 holds with `c = 1`. -/
theorem flatD_linearCount : ∀ M L : ℝ,
    ((Finset.univ.filter fun i => (flatD ⌊L⌋₊).a i ≤ M).card : ℝ) ≤ 1 * (1 + |L|) := by
  intro M L
  have h1 : ((Finset.univ.filter fun i => (flatD ⌊L⌋₊).a i ≤ M).card : ℝ) ≤ (⌊L⌋₊ : ℝ) := by
    exact_mod_cast flatD_filter_card_le ⌊L⌋₊ M
  have h2 := floor_le_one_add_abs L
  rw [one_mul]
  exact h1.trans h2

/-- The linear low count in existential form, with a constant independent of `M` and `L`. -/
theorem flatD_linearCount_exists : ∃ c : ℝ, 0 ≤ c ∧ ∀ M L : ℝ,
    ((Finset.univ.filter fun i => (flatD ⌊L⌋₊).a i ≤ M).card : ℝ) ≤ c * (1 + |L|) :=
  ⟨1, zero_le_one, flatD_linearCount⟩

/-- **G65.** The G64 linear low count is strictly weaker than the L-uniform low count: on
`flatD ⌊L⌋₊` the former holds with `c = 1`, while (G61) no constant bounds the count of
eigenvalues `≤ 0` uniformly in `L ≥ 1`. -/
theorem linearCount_strictly_weaker :
    (∀ M L : ℝ, ((Finset.univ.filter fun i => (flatD ⌊L⌋₊).a i ≤ M).card : ℝ) ≤ 1 * (1 + |L|)) ∧
    ¬ ∃ c : ℝ, ∀ L : ℝ, 1 ≤ L →
      ((Finset.univ.filter fun i => (flatD ⌊L⌋₊).a i ≤ 0).card : ℝ) ≤ c :=
  ⟨flatD_linearCount, flatD_not_lowCount⟩

end SteklovAudit.H5LowLinearStrict
