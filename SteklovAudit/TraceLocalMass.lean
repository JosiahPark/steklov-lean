import Mathlib
import SteklovAudit.AbstractTransfer
import SteklovAudit.AbstractTransferB

/-!
# G141: the trace comparison with local mass `O(h⁻¹)`

Roadmap item G141. In the spectral coordinates of `AbstractTransfer.Data` (finite cutoff), the
localized trace comparison `Σ (f(aᵢ) − f(bⱼ)) Jᵢⱼ²` is bounded, for an `Lf`-Lipschitz `f`, by
`Lf · ‖K‖_HS · ‖J‖_HS` (`trace_cs`: `trace_transfer` followed by Cauchy–Schwarz
`abs_pair_le_sqrt`). With the two named inputs at scale `h`
* defect: `hs2 D.K ≤ ε²`,
* local mass: `hs2 D.J ≤ Mloc / h`,
this gives `≤ Lf · |ε| · √(Mloc / h)` (`trace_local_mass_le`). The scalar corollary
`littleO_of_bounded_defect` shows that with `h = 1/L`, a Lipschitz constant bounded by `Λ` and a
defect bounded by `ε₀`, the bound `Λ ε₀ √(Mloc L)` is `o(L)`.

F table text: with a bounded defect and `O(h⁻¹)` local mass, the Lipschitz trace comparison is
`O(√L)`, hence `o(L)`, for multipliers with bounded Lipschitz constant.

What this file does NOT prove:
* The Lipschitz constants `Lf` of the paper's cumulative multipliers may grow with `L`; the
  corollary `littleO_of_bounded_defect` is the bounded-Lipschitz case only and does not give
  (7.29) for the paper's multipliers.
* The defect bound and the local mass bound are named hypotheses, not proved for any operator.
  No Dirichlet-to-Neumann operator is constructed; the data `D` are arbitrary.
* Nothing here proves Lemma 7.1′, Prop. 7.3, (7.29), any of H1–H6, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.TraceLocalMass

open SteklovAudit.AbstractTransfer

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G141.** Trace comparison with Cauchy–Schwarz:
`|Σ (f(a) − f(b)) J²| ≤ Lf · √‖K‖²_HS · √‖J‖²_HS`. -/
theorem trace_cs (D : Data ι κ) (f : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hf : ∀ x y, |f x - f y| ≤ Lf * |x - y|) :
    |∑ i, ∑ j, (f (D.a i) - f (D.b j)) * D.J i j ^ 2|
      ≤ Lf * Real.sqrt (hs2 D.K) * Real.sqrt (hs2 D.J) := by
  have h1 := trace_transfer D f Lf hf
  have h2 := abs_pair_le_sqrt D.K D.J
  rw [Real.sqrt_mul (hs2_nonneg D.K)] at h2
  calc |∑ i, ∑ j, (f (D.a i) - f (D.b j)) * D.J i j ^ 2|
      ≤ Lf * ∑ i, ∑ j, |D.K i j| * |D.J i j| := h1
    _ ≤ Lf * (Real.sqrt (hs2 D.K) * Real.sqrt (hs2 D.J)) :=
        mul_le_mul_of_nonneg_left h2 hLf
    _ = Lf * Real.sqrt (hs2 D.K) * Real.sqrt (hs2 D.J) := by ring

/-- **G141.** With the named defect input `hs2 K ≤ ε²` and the named local mass input
`hs2 J ≤ Mloc / h`, the trace comparison is `≤ Lf · |ε| · √(Mloc / h)`. -/
theorem trace_local_mass_le (D : Data ι κ) (f : ℝ → ℝ) (Lf ε Mloc h : ℝ) (hLf : 0 ≤ Lf)
    (hf : ∀ x y, |f x - f y| ≤ Lf * |x - y|)
    (hK : hs2 D.K ≤ ε ^ 2) (hJ : hs2 D.J ≤ Mloc / h) :
    |∑ i, ∑ j, (f (D.a i) - f (D.b j)) * D.J i j ^ 2|
      ≤ Lf * |ε| * Real.sqrt (Mloc / h) := by
  have h1 := trace_cs D f Lf hLf hf
  have hk : Real.sqrt (hs2 D.K) ≤ |ε| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hj : Real.sqrt (hs2 D.J) ≤ Real.sqrt (Mloc / h) := Real.sqrt_le_sqrt (by linarith)
  have a1 : Lf * Real.sqrt (hs2 D.K) ≤ Lf * |ε| := mul_le_mul_of_nonneg_left hk hLf
  have a2 : 0 ≤ Lf * |ε| := mul_nonneg hLf (abs_nonneg _)
  calc |∑ i, ∑ j, (f (D.a i) - f (D.b j)) * D.J i j ^ 2|
      ≤ Lf * Real.sqrt (hs2 D.K) * Real.sqrt (hs2 D.J) := h1
    _ ≤ Lf * |ε| * Real.sqrt (Mloc / h) := mul_le_mul a1 hj (Real.sqrt_nonneg _) a2

/-- **G141.** Scalar corollary, bounded-Lipschitz case only: with `h = 1/L` (so `Mloc / h =
Mloc · L`), Lipschitz constant `≤ Λ` and defect `≤ ε₀`, the bound `Λ ε₀ √(Mloc L)` is `o(L)`. -/
theorem littleO_of_bounded_defect (Λ ε₀ Mloc : ℝ) (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε₀) (hM : 0 ≤ Mloc) :
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → Λ * ε₀ * Real.sqrt (Mloc * L) ≤ η * L := by
  intro η hη
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = Λ * ε₀ * Real.sqrt Mloc := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    positivity
  refine ⟨(C / η) ^ 2 + 1, fun L hL => ?_⟩
  have hL0 : 0 ≤ L := by linarith [sq_nonneg (C / η)]
  have hs : C / η ≤ Real.sqrt L := by
    rw [show C / η = Real.sqrt ((C / η) ^ 2) from (Real.sqrt_sq (div_nonneg hC0 hη.le)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs1 : C ≤ Real.sqrt L * η := by
    first
    | exact (div_le_iff₀ hη).mp hs
    | exact (div_le_iff hη).mp hs
  have hs' : C ≤ η * Real.sqrt L := by
    calc C ≤ Real.sqrt L * η := hs1
      _ = η * Real.sqrt L := mul_comm _ _
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  calc Λ * ε₀ * Real.sqrt (Mloc * L) = C * Real.sqrt L := by
        rw [Real.sqrt_mul hM, hC]
        ring
    _ ≤ η * Real.sqrt L * Real.sqrt L := mul_le_mul_of_nonneg_right hs' hsL
    _ = η * L := by rw [mul_assoc, hsq]

/-- Non-vacuity of the named inputs: the zero coefficient array has `hs2 = 0`, so `J = 0`
satisfies the defect input with `ε = 0` and the local mass input with `Mloc = 0`. -/
theorem hs2_zero_array : hs2 (fun (_ : ι) (_ : κ) => (0 : ℝ)) = 0 := by
  simp [hs2]

end SteklovAudit.TraceLocalMass
