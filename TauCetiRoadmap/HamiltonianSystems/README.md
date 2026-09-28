# Roadmap: Hamiltonian systems and moment maps

Tau Ceti has the symplectic manifold. It has smooth two-forms on a manifold modelled on any real
normed space (`TauCeti.SmoothTwoForm`), closedness read in charts (`SmoothTwoForm.IsClosed`),
fiberwise nondegeneracy (`SmoothTwoForm.IsNondegenerate`), their conjunction
(`SmoothTwoForm.IsSymplectic`), the canonical form on the linear cotangent models `V × Module.Dual ℝ V`
and `V × StrongDual ℝ V`, and maximal flows of vector fields
(`TauCeti.maximalIntegralCurve`). What it does not have is the mechanics that lives on a symplectic
manifold: the Hamiltonian vector field of a function, the Poisson bracket, conservation laws, the
symplectic nature of Hamiltonian flows, infinitesimal symmetries and their moment maps, and the
cohomological obstruction to equivariance that makes the mass of a Galilean particle a
cohomology class. Mathlib has none of it either: its symplectic content is the matrix group
`Matrix.symplecticGroup`.

This roadmap builds that layer, at the generality of Banach manifolds with a weakly nondegenerate
form (so that phase spaces of field theories fit without change). Its summit is **Souriau's mass
theorem in algebraic form**: for the Galilean Lie algebra acting on the space of motions of a free
particle of mass `m`, the moment map exists, its cocycle is `m` times a fixed 2-cocycle, and the
second cohomology `H²(𝔤𝔞𝔩, ℝ)` is one-dimensional, spanned by that class. The mass of a particle is
the cohomology class of its moment map.

## Standing conventions

These are pinned. Every item below uses them.

- **Setting.** `E` is a real Banach space (`[NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]`,
  the hypothesis under which Mathlib's `VectorField.mlieBracket` API is available), `I : ModelWithCorners ℝ E H`,
  and `M` a manifold with `[IsManifold I ∞ M]`. A symplectic form is `ω : TauCeti.SmoothTwoForm I M`
  with `ω.IsSymplectic`. Nondegeneracy is Tau Ceti's fiberwise `LinearMap.BilinForm.Nondegenerate`,
  that is **weak** nondegeneracy (`v ↦ ω x v` injective). Results needing more carry
  `[FiniteDimensional ℝ E]` or the strong nondegeneracy of Layer 1, and say so.
- **Vector fields** are Mathlib's `(x : M) → TangentSpace I x`, smooth when
  `ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M))`, with Mathlib's bracket
  `VectorField.mlieBracket I` (in a chart, `[U, V] = DV·U - DU·V`). Integral curves are Mathlib's
  `IsMIntegralCurveOn`. The differential of a real function is Mathlib's `mvfderiv I F x`, which
  takes its values in `ℝ` directly (Tau Ceti's `mvfderiv_apply_eq_mfderiv_apply` relates it to
  `mfderiv I 𝓘(ℝ, ℝ) F x`).
- **Hamiltonian vector field:** `ι_{X_F} ω = dF`, that is `ω x (X x) v = mvfderiv I F x v`
  for all `x` and `v`.
- **Poisson bracket:** `{F, G} x = mvfderiv I F x (X_G x)`, so that `{F, G} = ω(X_F, X_G)`
  when `F` is Hamiltonian, and `d/dt F(γ t) = {F, H}(γ t)` along an integral curve `γ` of `X_H`.
  With Mathlib's bracket these conventions give `X_{{F, G}} = -[X_F, X_G]`.
- **Canonical model.** The manifold is `V × StrongDual ℝ V`, since a manifold needs a normed model
  space and `Module.Dual ℝ V` carries no norm in Mathlib. Tau Ceti's
  `strongDualCotangentSymplecticForm` on it is `ω((q, α), (q', β)) = β q - α q'`, the same formula
  as the algebraic `cotangentSymplecticForm` on `V × Module.Dual ℝ V`. Its Hamiltonian vector
  fields are `(∂H/∂α, -∂H/∂q)` (`q̇ = ∂H/∂p`, `ṗ = -∂H/∂q`), where `∂H/∂α` lies in the bidual and is
  read in `V` through the canonical isomorphism when `V` is finite-dimensional; the coordinate
  functions satisfy `{q_i, p_j} = δ_ij`.
- **Infinitesimal action** of a real Lie algebra `𝔤`: a linear map `Z ↦ Z_M` into smooth vector
  fields with `(⁅Z, Z'⁆)_M = -[Z_M, Z'_M]`. This is the relation satisfied by the fundamental vector
  fields of a left action; Layer 3 verifies it on each example.
- **Moment map:** `μ : M → Module.Dual ℝ 𝔤` with `ι_{Z_M} ω = d⟨μ, Z⟩` for every `Z`, each
  `x ↦ μ x Z` smooth.
- **Cocycle of a moment map:** `c(Z, Z') = {μ_Z, μ_Z'} - μ_{⁅Z, Z'⁆}`. Its class lives in the second
  cohomology of `𝔤` with coefficients in `TrivialLieModule ℝ 𝔤 ℝ`, in Mathlib's
  `LieModule.Cohomology` vocabulary (`twoCochain`, `d₁₂`, `twoCocycle`).
- **Dictionary with Souriau** (*Structure des systèmes dynamiques*, 1970; equation numbers of that
  edition). For a symplectic form `σ = ω`:
  - the symplectic gradient `grad u` of (9.16), `-∇u = σ(grad u)`, is `-X_u`;
  - the Poisson bracket (9.22), `σ(grad u)(grad v)`, is `{u, v}`;
  - (9.24), `grad [u, v] = [grad u, grad v]` with Souriau's bracket of vector fields (2.45), which
    is Mathlib's, is `X_{{u, v}} = -[X_u, X_v]`;
  - the moment of (11.7), `σ(Z_V(x)) = -∇[μ.Z]`, is `-μ`.

  Three further differences:
  - Souriau's phase-space form (9.12), `σ(dy)(δy) = dP(δQ) - δP(dQ)` for `y = (P, Q)`, is
    `-cotangentSymplecticForm` under `(P, Q) ↦ (Q, P)`: on the canonical model the dictionary
    applies with `σ = -ω`.
  - Souriau defines the bracket of `𝔤` by `[Z, Z']_V = [Z_V, Z'_V]` ((6.12 b), with the bracket of
    vector fields (2.45)), so that `Z ↦ Z_V` is a homomorphism. For the same vector fields, his
    bracket on `𝔤` is therefore the opposite of the one pinned here; on the Galilean Lie algebra it
    is the opposite of the matrix commutator.
  - With `σ = ω`, his cocycle `f` of (11.17) is the `c` of this roadmap.

## What Mathlib and Tau Ceti already have (consume)

- **Tau Ceti, symplectic layer.**
  - Smooth two-forms and their API: `TauCeti.SmoothTwoForm`, evaluation `form x v w`,
    `SmoothTwoForm.bilinFormAt`, `SmoothTwoForm.contMDiff_apply` (smoothness of `ω(U, V)`), and
    `SmoothTwoForm.const` for a continuous alternating bilinear form on a model space.
  - Closedness in charts: `SmoothTwoForm.IsClosed`, `SmoothTwoForm.inChartAt`,
    `SmoothTwoForm.isClosed_iff_forall_extDerivWithin_inChartAt_self`, `SmoothTwoForm.isClosed_const`.
  - Nondegeneracy and symplectic forms: `SmoothTwoForm.IsNondegenerate`,
    `SmoothTwoForm.isNondegenerate_iff_separatingLeft`, `SmoothTwoForm.IsSymplectic`,
    `SymplecticForm.constSmooth`, `SymplecticForm.isSymplectic_constSmooth`.
  - The linear symplectic form `TauCeti.SymplecticForm` and `SymplecticForm.IsSymplectomorphism`.
  - Cotangent models: `cotangentSymplecticForm` on `V × Module.Dual ℝ V`;
    `strongDualCotangentSymplecticForm` on `V × StrongDual ℝ V`, for any normed `V`;
    `cotangentLiouvilleForm`.
- **Tau Ceti, flows.**
  - `maximalIntegralCurve`, `maximalIntegralCurveInterval`, `maximalIntegralCurveFlowDomain`,
    `isOpen_maximalIntegralCurveFlowDomain`, the flow law `maximalIntegralCurve_add`, and
    `contMDiffOn_maximalIntegralCurve` (finite dimension, boundaryless, Hausdorff).
  - `IsMIntegralCurveOn.map_of_mfderiv_eq`, and `mvfderiv_mlieBracket` (the manifold bracket read
    through a differential).
- **Mathlib, differential calculus.**
  - `extDeriv` and `extDerivWithin` on normed spaces, with `extDeriv_apply_vectorField`, the
    invariant formula for `dω` evaluated on vector fields.
  - `VectorField.lieBracket` and `VectorField.mlieBracket`, `ContMDiffAt.mlieBracket_vectorField`,
    `VectorField.leibniz_identity_mlieBracket`.
  - Integral curves (`IsMIntegralCurveOn`, `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`),
    smooth functions `C^∞⟮I, M; ℝ⟯` with their algebra structure, `contDiffAt_map_inverse`.
- **Mathlib, Lie algebras.**
  - `LieRing`, `LieAlgebra`, `LieSubalgebra`, the commutator Lie algebra of matrices, and
    `skewAdjointLieSubalgebra`.
  - `TrivialLieModule`, and `LieModule.Cohomology.twoCochain`, `d₁₂`, `twoCocycle`,
    `mem_twoCocycle_iff_of_trivial`.
  - The central extension of a Lie algebra by a 2-cocycle, `LieAlgebra.ofTwoCocycle`, with
    `LieAlgebra.bracket_ofTwoCocycle`.

## What is missing (build here)

- Hamiltonian vector fields, Hamiltonian functions, and the Poisson bracket on a weakly symplectic
  Banach manifold; the Lie algebra of Hamiltonian functions.
- The invariant formula for a closed two-form on a manifold.
- Symplectomorphisms between manifolds, conservation laws, and symplecticity of Hamiltonian flows.
- Infinitesimal actions, moment maps, their cocycle and its class.
- 2-coboundaries and `H²` of a Lie algebra with trivial coefficients, which Mathlib does not
  have: `twoCoboundary` (the range of `d₁₂`) and `secondCohomology` (the 2-cocycles modulo the
  2-coboundaries) in `LieModule.Cohomology`, next to Mathlib's `twoCocycle`.
- The Galilean Lie algebra and the space of motions of a free particle.

## The build, in layers

The ordering is the dependency order. Layer 1 is the substrate of everything else. Layers 2 and 3
both consume Layer 1 and may proceed in parallel.

### Layer 1: Hamiltonian vector fields and the Poisson bracket

- **Hamiltonian vector fields.**
  - The predicate `IsHamiltonianVectorField ω F X`.
  - The pointwise `hamiltonianVectorField ω F x`: the unique `v` with `ω x v = dF_x` when it exists,
    `0` otherwise.
  - The predicate `IsHamiltonian ω F`: `F` is smooth and admits a smooth Hamiltonian vector field.
  - Uniqueness, from weak nondegeneracy.
  - Linearity: `X_{aF + bG} = a X_F + b X_G`.
  - `X_F = 0` exactly when `dF = 0`.
  - Leibniz: `X_{FG} = F • X_G + G • X_F`.
  - Locality: `X_F` at `x` depends only on the germ of `F` at `x`.
- **Strong nondegeneracy.**
  - `ω` is strongly nondegenerate when, at every point, `v ↦ ω x v` is onto
    `TangentSpace I x →L[ℝ] ℝ`.
  - A nondegenerate form on a finite-dimensional manifold is strongly nondegenerate.
  - For a strongly nondegenerate `ω`, every smooth function is Hamiltonian and
    `hamiltonianVectorField ω F` is smooth. The inverse of `v ↦ ω x v` is a continuous linear
    equivalence by the open mapping theorem, and its smooth dependence on `x` comes from
    `contDiffAt_map_inverse` in charts.
- **The Poisson bracket** `poissonBracket ω F G`, with the pinned definition.
  - It is bilinear.
  - It is antisymmetric on Hamiltonian functions, and equals `ω(X_F, X_G)` there.
  - It satisfies the Leibniz rule in each argument.
  - `{F, G}` is smooth when `F` and `G` are Hamiltonian.
- **The invariant formula for a closed two-form on a manifold.** For a closed smooth two-form `ω`
  and vector fields `U`, `V`, `W` that are smooth near `x`,
  `U(ω(V, W)) - V(ω(U, W)) + W(ω(U, V)) - ω([U, V], W) + ω([U, W], V) - ω([V, W], U) = 0` at `x`.
  - The directional derivatives are `mvfderiv` of the evaluated functions.
  - It is obtained from Mathlib's `extDeriv_apply_vectorField` in the chart at `x`, through
    `SmoothTwoForm.inChartAt` and the chart description of `mlieBracket`.
  - The statement is local, so it needs no global extension of tangent vectors to vector fields
    (smooth bump functions need not exist on a Banach manifold).
- **Milestone 1: Hamiltonian functions form a Lie algebra.** For `ω` symplectic and `F`, `G`
  Hamiltonian, `{F, G}` is Hamiltonian with `X_{{F, G}} = -[X_F, X_G]`, and the Jacobi identity
  holds. The Hamiltonian functions form a real Lie algebra under `{·, ·}` (bundled as `LieRing` and
  `LieAlgebra ℝ` on the subtype) and a subalgebra of `C^∞⟮I, M; ℝ⟯` for the pointwise product,
  related by the Leibniz rule. The map `F ↦ X_F` is linear, sends `{F, G}` to `-[X_F, X_G]`, and
  has as kernel the functions with `dF = 0`: the constants when `M` is preconnected.
- **Examples and acceptance tests.**
  - On a real finite-dimensional `V`, `SymplecticForm.constSmooth strongDualCotangentSymplecticForm`
    on `V × StrongDual ℝ V` is symplectic.
  - Its Hamiltonian vector fields are `(∂H/∂α, -∂H/∂q)`, with `∂H/∂α` read in `V` through the
    canonical isomorphism of `V` with its bidual.
  - For a basis of `V`, the coordinate functions satisfy `{q_i, p_j} = δ_ij`, `{q_i, q_j} = 0` and
    `{p_i, p_j} = 0`.
  - On any real Banach space `V`, the canonical form on `V × StrongDual ℝ V`, packaged as a
    constant `SmoothTwoForm` through `SmoothTwoForm.const`, is symplectic (weakly nondegenerate)
    and is strongly nondegenerate exactly when `V` is reflexive, that is, when
    `NormedSpace.inclusionInDoubleDual ℝ V` is surjective. This constant packaging is itself a
    target.

### Layer 2: dynamics

- **Conservation along integral curves.** Let `γ` be an integral curve of `X_H` on an open set, and
  `F` differentiable. Then `F ∘ γ` has derivative `{F, H} ∘ γ`, and `H` is constant along `γ`
  (conservation of energy). On a boundaryless manifold, where local integral curves exist through
  every point, a smooth `F` is constant along every integral curve of `X_H` if and only if
  `{F, H} = 0`. First integrals are closed under the Poisson bracket (Poisson's theorem, from the
  Jacobi identity).
- **Symplectomorphisms.**
  - A smooth map `φ : M → M'` is a symplectomorphism from `ω` to `ω'` when
    `ω' (φ x) (dφ v) (dφ w) = ω x v w` everywhere, with `dφ = mfderiv I I' φ x`.
  - Identities, compositions, and the inverse of a symplectic `Diffeomorph` are symplectic.
  - A symplectomorphism transports Hamiltonian vector fields
    (`dφ (X_{H ∘ φ} x) = X_H (φ x)`), Poisson brackets
    (`{F ∘ φ, G ∘ φ} = {F, G} ∘ φ`), and integral curves (through
    `IsMIntegralCurveOn.map_of_mfderiv_eq`).
  - A linear symplectomorphism of symplectic vector spaces (`SymplecticForm.IsSymplectomorphism`)
    is a symplectomorphism of the constant forms.
- **The variational equation.** Let `X` be a smooth vector field on a finite-dimensional,
  boundaryless, Hausdorff manifold, `x ∈ M`, `v ∈ T_x M`, and `φ_s = fun y ↦ maximalIntegralCurve X y s`.
  For `s₀` with `(x, s₀) ∈ maximalIntegralCurveFlowDomain X`, write `X̃` for the coordinate
  expression of `X` in the chart at `φ_{s₀} x` and `J(s)` for the coordinate expression of
  `mfderiv I I φ_s x v` in that chart. Then, for `s` near `s₀`, `J'(s) = DX̃(φ̃_s x) (J s)`, where
  `φ̃_s x` is the chart coordinate of `φ_s x`. This follows from the joint smoothness of the flow
  (`contMDiffOn_maximalIntegralCurve`) and the symmetry of second derivatives.
- **Milestone 2: Hamiltonian flows are symplectic.** In the same finite-dimensional setting, for
  `H` smooth and `ω` symplectic, let `(x, t) ∈ maximalIntegralCurveFlowDomain (X_H)` and
  `φ_t = fun y ↦ maximalIntegralCurve X_H y t`. Then
  `ω (φ_t x) (dφ_t v) (dφ_t w) = ω x v w`. Also, `H ∘ φ_t = H` and every first integral is
  preserved.

### Layer 3: infinitesimal symmetries and moment maps

- **Infinitesimal actions.** A structure holding a real Lie algebra `𝔤`, a linear map
  `𝔤 →ₗ[ℝ] ((x : M) → TangentSpace I x)` with smooth values, and the pinned relation
  `(⁅Z, Z'⁆)_M = -[Z_M, Z'_M]`. It is Hamiltonian when it admits a moment map.
- **Moment maps.**
  - The predicate `IsMomentMap ω a μ`.
  - Uniqueness: two moment maps `μ`, `μ'` of the same action differ by a function
    `ν : M → Module.Dual ℝ 𝔤` each of whose components `x ↦ ν x Z` has vanishing differential
    (`Module.Dual ℝ 𝔤` carries no norm, so the statement is componentwise), hence by a constant
    when `M` is preconnected.
  - **Noether's theorem:** if `H` is invariant (`dH (Z_M) = 0`), then `{μ_Z, H} = 0` and `μ_Z` is
    constant along every integral curve of `X_H`.
- **The cocycle.** Let `μ` be a moment map on a preconnected `M`.
  - `c(Z, Z') = {μ_Z, μ_Z'} - μ_{⁅Z, Z'⁆}` is constant, since its Hamiltonian vector field is
    `-[Z_M, Z'_M] - (⁅Z, Z'⁆)_M = 0`.
  - It is an element of `LieModule.Cohomology.twoCocycle ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ)`.
  - Replacing `μ` by `μ + ν` changes `c` by the coboundary of `ν`.
  - The class of `c` in `H²(𝔤, ℝ)` (built here: `twoCoboundary`, `secondCohomology`) is therefore
    an invariant of the Hamiltonian action.
  - `μ` can be chosen infinitesimally equivariant (`{μ_Z, μ_Z'} = μ_{⁅Z, Z'⁆}`) if and only if the
    class vanishes.
  - The central extension `LieAlgebra.ofTwoCocycle` of `𝔤` by `c` acts through the vector fields
    `(Z, s) ↦ Z_M`, and `(Z, s) ↦ μ_Z + s` is an equivariant moment map for it: the obstruction
    disappears on the central extension.
- **Examples and acceptance tests.**
  - *Translations.* The abelian Lie algebra `V` acts on a symplectic Banach space `(V, ω)` by
    constant vector fields.
    - The moment map is `μ_Z(x) = ω(Z, x)`.
    - The cocycle is `c = ω`, and its class is nonzero when `ω ≠ 0`, in every dimension: the
      Heisenberg extension.
  - *Linear symplectic action.* For finite-dimensional `(V, ω)`, the Lie algebra
    `skewAdjointLieSubalgebra` of `ω` acts by `A ↦ (x ↦ A x)`.
    - The moment map is `μ_A(x) = ½ ω(A x, x)`.
    - It is equivariant: the cocycle is zero.
  - *Cotangent lift.* For finite-dimensional `V`, `Module.End ℝ V` acts on `V × StrongDual ℝ V` by
    `A ↦ ((q, α) ↦ (A q, -(α ∘L A)))`, with `A` read as a continuous linear map
    (`LinearMap.toContinuousLinearMap`).
    - The moment map is `μ_A(q, α) = α (A q)`.
    - It is equivariant.
- **Milestone 3: Souriau's mass theorem, algebraic form.**
  - **The Galilean Lie algebra.** `𝔤𝔞𝔩` is the Lie subalgebra of `Matrix (Fin 5) (Fin 5) ℝ` of the
    matrices `[[j(ρ), β, γ], [0, 0, ε], [0, 0, 0]]` in blocks of sizes `3, 1, 1`, where `ρ, β, γ` are
    in `Fin 3 → ℝ`, `ε ∈ ℝ`, and `j(ρ)` is the skew matrix with `j(ρ) *ᵥ v = ρ ⨯₃ v`. It has
    dimension 10. `ρ` is an infinitesimal rotation, `β` a boost, `γ` a space translation and `ε` a
    time translation, acting on space-time by `(x, t) ↦ (j(ρ) x + t β + γ, ε)`.
  - **The space of motions** of a free particle of mass `m > 0` is
    `(Fin 3 → ℝ) × (Fin 3 → ℝ)` (position `q` and momentum `p` at time `0` of the straight line
    `t ↦ q + (t / m) • p`), with `ω((q, p), (q', p')) = p' ⬝ᵥ q - p ⬝ᵥ q'`: the canonical form of
    the Standing conventions, through the identification of `Fin 3 → ℝ` with its dual by `⬝ᵥ`.
  - **The action** of `Z = (ρ, β, γ, ε)` is the transport of its action on space-time to straight
    lines: `Z_M(q, p) = (ρ ⨯₃ q + γ - (ε / m) • p, ρ ⨯₃ p + m • β)`.
  - **Targets.**
    - This is an infinitesimal action in the pinned sense, for the commutator bracket of matrices.
    - `μ_Z(q, p) = ρ ⬝ᵥ (q ⨯₃ p) + γ ⬝ᵥ p - m (β ⬝ᵥ q) - ε (p ⬝ᵥ p) / (2 m)` is a moment map
      (angular momentum, momentum, `-m q`, and `-` the kinetic energy).
    - Its cocycle is `c(Z, Z') = m f₀(Z, Z')` with `f₀(Z, Z') = β' ⬝ᵥ γ - β ⬝ᵥ γ'`. In particular
      the boost `B e₁` (`β = e₁`) and the translation `T e₁` (`γ = e₁`) commute and
      `c(B e₁, T e₁) = -m`.
    - `H²(𝔤𝔞𝔩, ℝ)` is one-dimensional: every 2-cocycle `c'` is a coboundary plus
      `(-c'(B e₁, T e₁)) • f₀`, and `f₀` is not a coboundary.
    - The class of the free particle of mass `m` is `m [f₀]`: nonzero, and proportional to the
      mass.
  - **The `N`-particle version.** For `N` free particles of masses `m_j`, on the product of their
    spaces of motions with the sum of the forms and the diagonal action, the class is
    `(Σ m_j) [f₀]`: the total mass.

## Boundaries

- **Heegaard Floer (analytic).** Almost complex structures, `J`-holomorphic curves, Lagrangian
  Floer theory, and the Darboux and Moser theorems belong to that roadmap; this roadmap uses none of
  them.
- **Lie groups.** Group-level objects are not in this roadmap:
  - actions of Lie groups and their fundamental vector fields;
  - group-level equivariance of moment maps and the symplectic cocycle `θ : G → 𝔤*` of a group
    action;
  - coadjoint orbits and their Kirillov-Kostant-Souriau form;
  - symplectic reduction.
  They need the exponential map and `Ad` of the Lie groups roadmap
  (`RepresentationTheory/LieGroups`), and this roadmap does not depend on it.
- **Poisson manifolds.** General Poisson manifolds, the Lie-Poisson structure on the dual of a Lie
  algebra, and the statement that a moment map is a Poisson map are not in this roadmap.
- **Lagrangian mechanics and integrable systems.** The Euler-Lagrange equations, the Legendre
  transform, Liouville-Arnold, action-angle variables and KAM theory are not in this roadmap. A
  roadmap on them consumes Layers 1 and 2.
- **Infinite dimensions.** The Hamiltonian formalism of Layers 1 and 3 is proved on Banach
  manifolds with weakly nondegenerate forms. Existence and smoothness of flows (Layer 2) use Tau
  Ceti's finite-dimensional flow theory. Partial differential equations and specific field theories
  are not in this roadmap.

## References

- J.-M. Souriau, *Structure des systèmes dynamiques*, Maîtrises de mathématiques, Dunod, Paris, 1970.
  - §2 and §6: (2.45), (6.12).
  - §9: (9.12), (9.16), (9.22), (9.24)-(9.26).
  - §11: (11.7), (11.8), (11.12), (11.17), (11.24), (11.27), (11.33).
  - §12: (12.119), (12.131)-(12.136).
  - English translation: *Structure of Dynamical Systems: A Symplectic View of Physics*, translated
    by C. H. Cushman-de Vries, translation edited by R. H. Cushman and G. M. Tuynman, Progress in
    Mathematics 149, Birkhäuser, Boston, 1997,
    [doi:10.1007/978-1-4612-0281-3](https://doi.org/10.1007/978-1-4612-0281-3).
- V. Bargmann, *On unitary ray representations of continuous groups*, Ann. of Math. (2) 59 (1954),
  1-46, [doi:10.2307/1969831](https://doi.org/10.2307/1969831).
- D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford Graduate Texts
  in Mathematics 27, Oxford University Press, 2017,
  [doi:10.1093/oso/9780198794899.001.0001](https://doi.org/10.1093/oso/9780198794899.001.0001).
- J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in
  Applied Mathematics 17, Springer, New York, 1999,
  [doi:10.1007/978-0-387-21792-5](https://doi.org/10.1007/978-0-387-21792-5).
- P. R. Chernoff and J. E. Marsden, *Properties of Infinite Dimensional Hamiltonian Systems*,
  Lecture Notes in Mathematics 425, Springer, Berlin, 1974,
  [doi:10.1007/BFb0073665](https://doi.org/10.1007/BFb0073665).

## Provenance

Part of this material is formalized, in a less general setting, in the physics library
[physlib](https://github.com/leanprover-community/physlib), by the author of this roadmap under the
Apache 2.0 licence:

- `PhyslibAlpha/ClassicalMechanics/MomentMap/Basic.lean`: moment maps of affine infinitesimally
  symplectic actions on a finite-dimensional symplectic vector space, the cocycle and its cyclic
  identity, Noether's theorem, and the translations of the plane;
- `PhyslibAlpha/ClassicalMechanics/MomentMap/Cohomology.lean`: the cohomology class at group level
  for the affine symplectic group;
- `PhyslibAlpha/ClassicalMechanics/MomentMap/GalileanMass.lean`: the Galilean Lie algebra in
  Souriau's parametrization, his cocycle `f₀` (the opposite of the `f₀` of Milestone 3), and the
  total mass.

These files work in Souriau's sign conventions, not the pinned ones (see the dictionary above).
They are a source to consult, not a specification.
