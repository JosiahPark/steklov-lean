# Continuation 176 (2026-11-10): two-channel low-axial-frequency wedge coercivity

Source: `Steklov_Lean_Continuation_176_2026-11-10.zip` (`Continuation176.md`, an uncompiled `Candidate.lean`,
a floating-point `check.py`). Added by the interactive session on 2026-11-15. Continuation 175, which defines
the form `Eκ`, is not in this repo.

**Lean status: scalar fragments only** (`SteklovAudit/WedgeChannel.lean`, roadmap item S8).

## Setting

A straight wedge of opening α > 0, `t = log r ∈ [a, b]`, axial Fourier frequency κ, face traces
`f(t) = u(t, 0)`, `g(t) = u(t, α)`. The channels are `s = (f+g)/√2` and `d = (f−g)/√2`, and `m(t) = |κ| e^t`.
This is a variational model that looks only at the faces, with natural end-cap conditions. It is **not** the
Dirichlet-to-Neumann operator of the tetrahedron.

## Results and where they stand

| Result | Statement | Lean |
|---|---|---|
| 176.1 | `Eκ[u] ≥ ∫ [m tanh(αm/2)\|s\|² + m coth(αm/2)\|d\|²] dt` (also for the infimum `Qκ`) | Eigenvalue step only: the endpoint matrix `m[[coth mα, −csch mα], [−csch mα, coth mα]]` has eigenvalues `m tanh(mα/2)`, `m coth(mα/2)`, which is `SectorTrace.endpoint_eigen_minus/plus` (S1). The angular minimization, Sobolev traces and the `t`-integral are not formalized. |
| 176.2 | `x/(1+x) ≤ tanh x ≤ x`, `1/x ≤ coth x ≤ 1 + 1/x`; hence `αm²/(2+αm) ≤ m tanh(αm/2) ≤ αm²/2` and `2/α ≤ m coth(αm/2) ≤ 2/α + m` | `div_one_add_le_tanh`, `tanh_le_id`, `inv_le_coth`, `coth_le_one_add_inv`, `sym_lower`, `sym_upper`, `anti_lower`, `anti_upper`, `channel_lower` (antisymmetric bounds for `m > 0`; Lean's `coth 0 = 0`, so the `m = 0` extension `2/α` is not stated) |
| 176.3 | If `s = 0` and `t ≤ b`, then `Qκ ≥ (2e^{−b}/α) ∫ e^t(\|f\|²+\|g\|²)` | Scalar step `antisym_physical` only |
| channel algebra | `s² + d² = f² + g²`, `(f−g)² = 2d²` | `channel_sum`, `channel_difference` (replace `Candidate.lean`, which was never compiled) |

## Caveats (from the report, kept)

- The antisymmetric channel has a gap that depends on neither κ nor the scale, in `∫|d|² dt`. The symmetric
  channel degenerates like `(|κ|r)²`. This gives no uniform gap in the weighted face norm `∫ e^t|·|² dt`.
- Corollary 176.3 depends on the chart's outer radius `e^b` and applies only to purely antisymmetric traces.
- No spectral edge coefficient, localized Hilbert–Schmidt estimate, trace transfer, propagation or counting
  theorem follows. The result moves no `[H…]` input and no row of the F table.
- `check.py` is a floating-point diagnostic (20000 random samples), not a proof.