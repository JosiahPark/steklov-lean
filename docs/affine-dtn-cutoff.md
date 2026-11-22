# A spectral cutoff bound from the regular tetrahedron's affine harmonic traces

Let A be the positive Dirichlet-to-Neumann operator of the solid regular tetrahedron of edge length a. A four-dimensional space of boundary probes gives an explicit example where the coefficients in the archive's finite spectral comparison come from A itself. For this space the total squared intertwining defect is exactly 16/a². It controls the part of a Lipschitz spectral trace lost above a cutoff. The comparison operator in this calculation is the affine compression of A. The edge analysis in the paper requires comparison with an infinite wedge model.

## 1. Compute the boundary form on harmonic functions

Write the vertices as t times the four sign vectors v with coordinate product +1, where t = a/(2√2). Use the probability surface measure on the boundary (surface measure divided by total area). Write x = X/t for the dimensionless coordinates of a physical point X. On the face opposite tv the outward unit normal is −v/√3: the other vertices satisfy v·X = −t. For the trace u = c + b·x the harmonic extension is the same affine function. Its conormal derivative is

    Au = −(b·v)/(√3 t)   on the face opposite tv.

This is the weak DtN action: integration by parts against a smooth test function gives precisely the sum of these face integrals. Density extends the Green identity to energy-space test functions. The facewise flux is in boundary L², hence u belongs to the L² operator domain. Normalizing the boundary inner product also normalizes the interior Green pairing by the same total area.

Let V be the span of 1,x₁,x₂,x₃, and let Π denote orthogonal projection onto V. To integrate the product of two affine functions on a triangular face, average the three edge-midpoint values of that product. Indeed, normalized integration gives 1/6 for the square of a barycentric coordinate and 1/12 for the product of distinct barycentric coordinates, by integrating on the reference triangle. The three equally weighted midpoints give the same six moments. All faces have equal area. For u = c+b·x and w = d+e·x this gives

    ⟨u,w⟩ = cd + (b·e)/3,
    ⟨Au,w⟩ = (b·e)/(3√3 t).

Set μ = 1/(√3 t) and B = ΠA restricted to V. Then B1 = 0 and Bxⱼ = μxⱼ. In particular μ is a Ritz value. The affine coordinate traces have nonzero flux outside V, as the next calculation quantifies.

## 2. Compute exactly what the compression loses

Let J: V → L²(∂T) be the inclusion. For R = AJ − JB the residual is orthogonal to V. On the face opposite tv, its value at u is −(b·v + b·x)/(√3 t). Integrating the product of residuals by the same midpoint rule gives

    ⟨Ru,Rw⟩ = 2(b·e)/(9t²).

The vectors φ₀ = 1 and φⱼ = √3 xⱼ (1 ≤ j ≤ 3) form an orthonormal basis of V. Thus Rφ₀ = 0, while each other residual has squared norm 2/(3t²). In particular

    ‖R‖²_HS = 2/t² = 16/a².

The distinction between the eigenvalues of B and those of A matters here. Replacing the Ritz vectors by purported exact Steklov eigenvectors would incorrectly give zero for this defect.

## 3. Turn the defect into a high-energy cutoff bound

Choose a real orthonormal Steklov eigenbasis (ψᵢ) of the tetrahedron, with Aψᵢ = λᵢψᵢ. Put μ₀ = 0 and μ₁ = μ₂ = μ₃ = μ. These are genuine overlap coefficients:

    Jᵢⱼ = ⟨ψᵢ,φⱼ⟩,
    (λᵢ − μⱼ)Jᵢⱼ = ⟨ψᵢ,Rφⱼ⟩.

The second identity uses self-adjointness and the operator-domain calculation in §1. Parseval and §2 give ∑ᵢⱼ |Jᵢⱼ|² = 4 and ∑ᵢⱼ (λᵢ−μⱼ)² |Jᵢⱼ|² = 16/a². In particular no boundary estimate uniform in individual eigenfunctions is required.

For a real Lipschitz multiplier F, let S(F) = ∑ᵢⱼ (F(λᵢ)−F(μⱼ)) |Jᵢⱼ|². This series converges absolutely by Cauchy–Schwarz and the two preceding bounds. Write S≤L for its restriction to λᵢ ≤ L. For L > μ and every omitted term, d = λᵢ−μⱼ ≥ L−μ > 0. Therefore |F(λᵢ)−F(μⱼ)| ≤ Lip(F)d ≤ Lip(F)d²/(L−μ). Summing gives

    |S(F) − S≤L(F)| ≤ 16 Lip(F) / [a² (L−μ)].

Equivalently S(F) is the trace on V of J*F(A)J − F(B). Since |F(s)| grows at most linearly, every φⱼ belongs to the domain of F(A). The same estimate applies to a family F_L with its actual Lipschitz constant at each L. For uniformly bounded Lipschitz constants this gives an O(1/L) cutoff discrepancy on these probes. The edge problem uses a growing family of probes and a different B. To transfer the argument one would need bounds for their *summed* defects and for the discrepancy between their trace and the paper's localized E−Emod.

## Verification and provenance

The companion module SteklovAudit/TetraAffineFlux.lean proves the barycentric midpoint coefficient identity, the boundary mass and Green pairings, orthogonality, the residual pairing, and the finite-sum spectral tail inequality. The pairing in Lean uses the sign-normal flux and twelve times normalized area on the reference tetrahedron. Divide by twelve, then divide each flux factor by √3 t to obtain the physical formulas. The weak Green identity, the integration interpretation of the midpoint rule, and the spectral-theorem passage above are mathematical arguments in this note. The module does not yet implement the infinite-dimensional DtN operator.

The operator and localization target are specified in the repository's preprint, Sections 1 and 7. For the boundary eigenbasis used above see G. Auchmuty, *Steklov Eigenproblems and the Representation of Solutions of Elliptic Boundary Value Problems*. [Preprint](../preprint/steklov_tetrahedron.tex) · [Auchmuty](https://www.math.uh.edu/~giles/PDFpapers/NFAOpfs.pdf) · [Lean certificate](../SteklovAudit/TetraAffineFlux.lean)
