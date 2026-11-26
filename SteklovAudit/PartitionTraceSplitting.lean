import Mathlib

/-!
# K9: trace splitting for normalized spectral data (shape of ledger field H1)

For any measure space `(X, μ)`, a finite index set `s`, eigenvalues `lam`, real eigenfunctions
`φ k` normalized by `∫ φ k ^ 2 ∂μ = 1`, and a finite weight family `w j` with `∑ j, w j x = 1`
for every `x`, the counting function `#{k ∈ s | lam k ≤ L}` equals the sum over `j` of the
localized masses `∑_{lam k ≤ L} ∫ w j * φ k ^ 2`. Grouping the weights into vertex, edge and
face families gives the `splitting` shape `N L = V L + E L + F L`.

No analytic input is assumed: this is pure measure theory once normalized spectral data and a
partition of unity are given.

What this file does NOT prove: it does not construct a Dirichlet-to-Neumann operator or its
eigenbasis, it does not prove any ledger input H1–H6 for the actual operator (that needs the
actual eigenbasis, which Lean does not have), it does not prove the pointwise partition identity
for the tetrahedral partition (item K11), and it does not prove Theorem 1.3 / 11.1.
-/

open MeasureTheory

namespace SteklovAudit.PartitionTraceSplitting

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {ι J : Type*} [Fintype J]

/-- Localized mass below `L` of the spectral data in the weight `w j`. -/
noncomputable def localMass (μ : Measure X) (s : Finset ι) (lam : ι → ℝ) (φ : ι → X → ℝ)
    (w : J → X → ℝ) (j : J) (L : ℝ) : ℝ :=
  ∑ k ∈ s.filter (fun k => lam k ≤ L), ∫ x, w j x * φ k x ^ 2 ∂μ

/-- For one function, the weighted masses add up to its full mass. -/
theorem sum_weights_integral (φk : X → ℝ) (w : J → X → ℝ)
    (hsum : ∀ x, ∑ j, w j x = 1)
    (hint : ∀ j, Integrable (fun x => w j x * φk x ^ 2) μ) :
    ∑ j, ∫ x, w j x * φk x ^ 2 ∂μ = ∫ x, φk x ^ 2 ∂μ := by
  have h := integral_finset_sum (μ := μ) Finset.univ
    (fun j (_ : j ∈ Finset.univ) => hint j)
  calc ∑ j, ∫ x, w j x * φk x ^ 2 ∂μ = ∫ x, ∑ j, w j x * φk x ^ 2 ∂μ := h.symm
    _ = ∫ x, φk x ^ 2 ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show ∑ j, w j x * φk x ^ 2 = φk x ^ 2
        rw [← Finset.sum_mul, hsum x, one_mul]

/-- Trace splitting: the eigenvalue count is the sum of the localized masses. -/
theorem count_eq_sum_localized (s : Finset ι) (lam : ι → ℝ) (φ : ι → X → ℝ)
    (w : J → X → ℝ)
    (hnorm : ∀ k ∈ s, ∫ x, φ k x ^ 2 ∂μ = 1)
    (hsum : ∀ x, ∑ j, w j x = 1)
    (hint : ∀ k ∈ s, ∀ j, Integrable (fun x => w j x * φ k x ^ 2) μ) (L : ℝ) :
    ((s.filter (fun k => lam k ≤ L)).card : ℝ) = ∑ j, localMass μ s lam φ w j L := by
  unfold localMass
  rw [Finset.sum_comm, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hks : k ∈ s := (Finset.mem_filter.mp hk).1
  rw [sum_weights_integral (φ k) w hsum (hint k hks), hnorm k hks]

/-- Grouping the weights into vertex, edge and face families gives the `splitting` shape
`N L = V L + E L + F L`. -/
theorem splitting_of_partition {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    (s : Finset ι) (lam : ι → ℝ) (φ : ι → X → ℝ)
    (wV : V → X → ℝ) (wE : E → X → ℝ) (wF : F → X → ℝ)
    (hnorm : ∀ k ∈ s, ∫ x, φ k x ^ 2 ∂μ = 1)
    (hsum : ∀ x, ∑ v, wV v x + ∑ e, wE e x + ∑ f, wF f x = 1)
    (hintV : ∀ k ∈ s, ∀ v, Integrable (fun x => wV v x * φ k x ^ 2) μ)
    (hintE : ∀ k ∈ s, ∀ e, Integrable (fun x => wE e x * φ k x ^ 2) μ)
    (hintF : ∀ k ∈ s, ∀ f, Integrable (fun x => wF f x * φ k x ^ 2) μ) (L : ℝ) :
    ((s.filter (fun k => lam k ≤ L)).card : ℝ) =
      ∑ v, localMass μ s lam φ wV v L + ∑ e, localMass μ s lam φ wE e L
        + ∑ f, localMass μ s lam φ wF f L := by
  have hw : ∀ x, ∑ j, Sum.elim (Sum.elim wV wE) wF j x = 1 := by
    intro x
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact hsum x
  have hi : ∀ k ∈ s, ∀ j,
      Integrable (fun x => Sum.elim (Sum.elim wV wE) wF j x * φ k x ^ 2) μ := by
    rintro k hk ((v | e) | f)
    · exact hintV k hk v
    · exact hintE k hk e
    · exact hintF k hk f
  rw [count_eq_sum_localized s lam φ (Sum.elim (Sum.elim wV wE) wF) hnorm hw hi L]
  simp only [Fintype.sum_sum_type, localMass, Sum.elim_inl, Sum.elim_inr]

/-- The counting function is the sum of the localized masses for any `L` (pointwise in `L`),
stated as an equality of functions, the form of the `splitting` field. -/
theorem splitting_fun {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    (s : Finset ι) (lam : ι → ℝ) (φ : ι → X → ℝ)
    (wV : V → X → ℝ) (wE : E → X → ℝ) (wF : F → X → ℝ)
    (hnorm : ∀ k ∈ s, ∫ x, φ k x ^ 2 ∂μ = 1)
    (hsum : ∀ x, ∑ v, wV v x + ∑ e, wE e x + ∑ f, wF f x = 1)
    (hintV : ∀ k ∈ s, ∀ v, Integrable (fun x => wV v x * φ k x ^ 2) μ)
    (hintE : ∀ k ∈ s, ∀ e, Integrable (fun x => wE e x * φ k x ^ 2) μ)
    (hintF : ∀ k ∈ s, ∀ f, Integrable (fun x => wF f x * φ k x ^ 2) μ) :
    (fun L => ((s.filter (fun k => lam k ≤ L)).card : ℝ)) =
      fun L => ∑ v, localMass μ s lam φ wV v L + ∑ e, localMass μ s lam φ wE e L
        + ∑ f, localMass μ s lam φ wF f L := by
  funext L
  exact splitting_of_partition s lam φ wV wE wF hnorm hsum hintV hintE hintF L

end SteklovAudit.PartitionTraceSplitting
