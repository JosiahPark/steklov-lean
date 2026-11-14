import Mathlib
import SteklovAudit.H5HighMassAudit

/-!
# G32: an L-uniform low count from linear eigenvalue growth

Roadmap item G32.

* `card_low_le_floor`: over `Fin n` with values `a`, if `0 < s` and `k * s ≤ a k` for every index `k`,
  then the number of `k` with `a k ≤ M` is at most `⌊M / s⌋₊ + 1` (indices map injectively into
  `Finset.range (⌊M / s⌋₊ + 1)`).
* `lowCount_of_linear_growth` (for `0 ≤ M`): the count is at most `M / s + 1`.
  `lowCount_of_linear_growth_abs` (all `M`): at most `|M| / s + 1`.
  (The roadmap text stated `M / s + 1` without `0 ≤ M`; that is false for `M < -s`, where the count is
  `0`, so the `M / s + 1` form carries `0 ≤ M` and the all-`M` form uses `|M|`.)
* `exists_lowCount_of_linear_growth`: for a family over `L` with one slope `s` for all `L`, the
  `lowCount` row shape `∃ c, ∀ M L, card ≤ c M` holds (`c M = |M| / s + 1`).
* `count_not_lowCount`: the Weyl `count` row (`card ≤ 1 * (1 + L) ^ 2`) holds for `Fin ⌈L⌉₊` with all
  eigenvalues `0`, while no `c M` bounds the low count for all `L` (G30's `zero_not_lowCount`). So
  `lowCount` (and its model mirror `modelLowCount`) is a genuine row, not implied by `count`.

F table text: each low-count row (true `lowCount`, model `modelLowCount`) follows from linear growth of
the indexed eigenvalues with an L-independent slope.

What this file does NOT prove: no growth bound, low count or Weyl count is proved for the Steklov
operator of the tetrahedron, for the model operator, or for any concrete operator; no
Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain
conditional on the named inputs.
-/

namespace SteklovAudit.H5LowCountGrowth

/-- G32. Linear growth `k * s ≤ a k` bounds the low count by `⌊M / s⌋₊ + 1`, for every `M`. -/
theorem card_low_le_floor {n : ℕ} (a : Fin n → ℝ) {s : ℝ} (hs : 0 < s)
    (ha : ∀ k : Fin n, ((k : ℕ) : ℝ) * s ≤ a k) (M : ℝ) :
    (Finset.univ.filter fun k => a k ≤ M).card ≤ ⌊M / s⌋₊ + 1 := by
  have hsub : (Finset.univ.filter fun k => a k ≤ M).image Fin.val ⊆
      Finset.range (⌊M / s⌋₊ + 1) := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    have hak : a k ≤ M := (Finset.mem_filter.mp hk).2
    have h1 : ((k : ℕ) : ℝ) * s ≤ M := le_trans (ha k) hak
    have h2 : ((k : ℕ) : ℝ) ≤ M / s := by
      first
        | exact (le_div_iff₀ hs).mpr h1
        | (rw [le_div_iff₀ hs]; exact h1)
        | exact (le_div_iff hs).mpr h1
    have h3 : (k : ℕ) ≤ ⌊M / s⌋₊ := Nat.le_floor h2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le h3)
  have h := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at h

/-- **G32.** For `0 ≤ M`, linear growth bounds the low count by `M / s + 1`. -/
theorem lowCount_of_linear_growth {n : ℕ} (a : Fin n → ℝ) {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M)
    (ha : ∀ k : Fin n, ((k : ℕ) : ℝ) * s ≤ a k) :
    ((Finset.univ.filter fun k => a k ≤ M).card : ℝ) ≤ M / s + 1 := by
  have hc : ((Finset.univ.filter fun k => a k ≤ M).card : ℝ) ≤ (⌊M / s⌋₊ : ℝ) + 1 := by
    exact_mod_cast card_low_le_floor a hs ha M
  have hfl : (⌊M / s⌋₊ : ℝ) ≤ M / s := Nat.floor_le (div_nonneg hM hs.le)
  linarith

/-- G32. For every `M`, linear growth bounds the low count by `|M| / s + 1`. -/
theorem lowCount_of_linear_growth_abs {n : ℕ} (a : Fin n → ℝ) {s : ℝ} (hs : 0 < s)
    (ha : ∀ k : Fin n, ((k : ℕ) : ℝ) * s ≤ a k) (M : ℝ) :
    ((Finset.univ.filter fun k => a k ≤ M).card : ℝ) ≤ |M| / s + 1 := by
  have hc : ((Finset.univ.filter fun k => a k ≤ M).card : ℝ) ≤ (⌊M / s⌋₊ : ℝ) + 1 := by
    exact_mod_cast card_low_le_floor a hs ha M
  have hdiv : M / s ≤ |M| / s := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_abs_self M) (inv_nonneg.mpr hs.le)
  have hmono : ⌊M / s⌋₊ ≤ ⌊|M| / s⌋₊ := Nat.floor_mono hdiv
  have hmono' : (⌊M / s⌋₊ : ℝ) ≤ (⌊|M| / s⌋₊ : ℝ) := by exact_mod_cast hmono
  have hfl : (⌊|M| / s⌋₊ : ℝ) ≤ |M| / s := Nat.floor_le (div_nonneg (abs_nonneg M) hs.le)
  linarith

/-- G32. A family over `L` with one slope `s` for all `L` satisfies the L-uniform `lowCount` row
shape, with rate `c M = |M| / s + 1`. -/
theorem exists_lowCount_of_linear_growth {n : ℝ → ℕ} (a : ∀ L : ℝ, Fin (n L) → ℝ) {s : ℝ}
    (hs : 0 < s) (ha : ∀ (L : ℝ) (k : Fin (n L)), ((k : ℕ) : ℝ) * s ≤ a L k) :
    ∃ c : ℝ → ℝ, ∀ M L : ℝ,
      ((Finset.univ.filter fun k => a L k ≤ M).card : ℝ) ≤ c M :=
  ⟨fun M => |M| / s + 1, fun M L => lowCount_of_linear_growth_abs (a L) hs (ha L) M⟩

/-- G32 example: `⌈L⌉₊` eigenvalues meet the Weyl `count` row with `Cm = 1`. -/
theorem ceil_count (L : ℝ) : (Fintype.card (Fin ⌈L⌉₊) : ℝ) ≤ 1 * (1 + L) ^ 2 := by
  rw [Fintype.card_fin]
  by_cases hL : 0 ≤ L
  · have h1 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hL
    nlinarith [mul_nonneg hL hL]
  · push_neg at hL
    have h0 : ⌈L⌉₊ = 0 := by
      first
        | exact Nat.ceil_eq_zero.mpr hL.le
        | simp [Nat.ceil_eq_zero, hL.le]
    rw [h0, Nat.cast_zero]
    positivity

/-- **G32.** The Weyl `count` row does not imply an L-uniform low count: with `⌈L⌉₊` eigenvalues all
at `0`, `count` holds with `Cm = 1` for every `L`, but no `c M` bounds the low count for all `L`. -/
theorem count_not_lowCount :
    (∀ L : ℝ, (Fintype.card (Fin ⌈L⌉₊) : ℝ) ≤ 1 * (1 + L) ^ 2) ∧
    ¬ ∃ c : ℝ → ℝ, ∀ M L : ℝ,
      ((Finset.univ.filter fun i : Fin ⌈L⌉₊ => (fun _ : Fin ⌈L⌉₊ => (0 : ℝ)) i ≤ M).card : ℝ)
        ≤ c M :=
  ⟨ceil_count, SteklovAudit.H5HighMassAudit.zero_not_lowCount⟩

end SteklovAudit.H5LowCountGrowth
