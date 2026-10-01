import Mathlib
import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Cotangent.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Flow

/-!
# Hamiltonian systems and moment maps: target signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is
`README.md`. The statements here suggest Lean forms for particular milestones, so that
contributors and reviewers converge on names and signatures; discharging all of them
finishes neither a layer nor the roadmap.

The symplectic form is written `σ` here (Souriau's letter) because `ω` is a notation under
`open scoped ContDiff`; `README.md` writes it `ω`.
-/

namespace TauCetiRoadmap.HamiltonianSystems

open TauCeti
open scoped ContDiff Manifold

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Layer 1: Hamiltonian vector fields and the Poisson bracket -/

/-- `X` is a Hamiltonian vector field of `F` for `σ`: `ι_X σ = dF`. -/
def IsHamiltonianVectorField (σ : SmoothTwoForm I M) (F : M → ℝ)
    (X : (x : M) → TangentSpace I x) : Prop :=
  ∀ x v, σ x (X x) v = mvfderiv I F x v

open Classical in
/-- The Hamiltonian vector field of `F` at `x`: the unique `v` with `σ x v = dF_x` when it exists,
`0` otherwise. -/
def hamiltonianVectorField (σ : SmoothTwoForm I M) (F : M → ℝ) (x : M) : TangentSpace I x :=
  if h : ∃ v : TangentSpace I x, ∀ w, σ x v w = mvfderiv I F x w then h.choose else 0

/-- `F` is smooth and has a smooth Hamiltonian vector field. -/
def IsHamiltonian (σ : SmoothTwoForm I M) (F : M → ℝ) : Prop :=
  ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ ∃ X : (x : M) → TangentSpace I x,
    ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) ∧
      IsHamiltonianVectorField σ F X

/-- Strong nondegeneracy: at every point, `v ↦ σ x v` is onto the continuous dual. -/
def IsStronglyNondegenerate (σ : SmoothTwoForm I M) : Prop :=
  ∀ (x : M) (α : TangentSpace I x →L[ℝ] ℝ), ∃ v : TangentSpace I x, ∀ w, σ x v w = α w

/-- The Poisson bracket `{F, G} = dF (X_G)`. -/
def poissonBracket (σ : SmoothTwoForm I M) (F G : M → ℝ) (x : M) : ℝ :=
  mvfderiv I F x (hamiltonianVectorField σ G x)

/-- Layer 1: uniqueness of the Hamiltonian vector field under weak nondegeneracy. -/
theorem IsHamiltonianVectorField.eq {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    {F : M → ℝ} {X Y : (x : M) → TangentSpace I x} (hX : IsHamiltonianVectorField σ F X)
    (hY : IsHamiltonianVectorField σ F Y) : X = Y := by
  sorry

/-- Layer 1: in finite dimension, a nondegenerate form is strongly nondegenerate. -/
theorem isStronglyNondegenerate_of_finiteDimensional [FiniteDimensional ℝ E]
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) : IsStronglyNondegenerate σ := by
  sorry

/-- Layer 1: for a strongly nondegenerate form, every smooth function is Hamiltonian. -/
theorem isHamiltonian_of_contMDiff {σ : SmoothTwoForm I M} (hσ : IsStronglyNondegenerate σ)
    {F : M → ℝ} (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F) : IsHamiltonian σ F := by
  sorry

/-- Layer 1: the invariant formula for a closed two-form, at a point, for vector fields smooth near
that point. -/
theorem invariant_formula {σ : SmoothTwoForm I M} (hσ : σ.IsClosed)
    {U V W : (x : M) → TangentSpace I x} {x : M}
    (hU : ContMDiffAt I I.tangent ∞ (fun y ↦ (⟨y, U y⟩ : TangentBundle I M)) x)
    (hV : ContMDiffAt I I.tangent ∞ (fun y ↦ (⟨y, V y⟩ : TangentBundle I M)) x)
    (hW : ContMDiffAt I I.tangent ∞ (fun y ↦ (⟨y, W y⟩ : TangentBundle I M)) x) :
    mvfderiv I (fun y ↦ σ y (V y) (W y)) x (U x)
      - mvfderiv I (fun y ↦ σ y (U y) (W y)) x (V x)
      + mvfderiv I (fun y ↦ σ y (U y) (V y)) x (W x)
      - σ x (VectorField.mlieBracket I U V x) (W x)
      + σ x (VectorField.mlieBracket I U W x) (V x)
      - σ x (VectorField.mlieBracket I V W x) (U x) = 0 := by
  sorry

/-- Milestone 1: the Poisson bracket of two Hamiltonian functions is Hamiltonian, with Hamiltonian
vector field `-[X_F, X_G]`. -/
theorem IsHamiltonian.poissonBracket {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    {F G : M → ℝ} (hF : IsHamiltonian σ F) (hG : IsHamiltonian σ G) :
    IsHamiltonian σ (poissonBracket σ F G) ∧
      IsHamiltonianVectorField σ (poissonBracket σ F G)
        (-VectorField.mlieBracket I (hamiltonianVectorField σ F) (hamiltonianVectorField σ G)) := by
  sorry

/-- Milestone 1: the Jacobi identity. -/
theorem poissonBracket_jacobi {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    {F G K : M → ℝ} (hF : IsHamiltonian σ F) (hG : IsHamiltonian σ G) (hK : IsHamiltonian σ K) :
    poissonBracket σ F (poissonBracket σ G K) + poissonBracket σ G (poissonBracket σ K F)
      + poissonBracket σ K (poissonBracket σ F G) = 0 := by
  sorry

/-! ## Layer 2: dynamics -/

/-- Layer 2: along an integral curve of `X_H`, `F` has derivative `{F, H}`. -/
theorem hasDerivAt_comp_of_isMIntegralCurveOn {σ : SmoothTwoForm I M} {F H : M → ℝ}
    {γ : ℝ → M} {s : Set ℝ} (hs : IsOpen s)
    (hγ : IsMIntegralCurveOn γ (hamiltonianVectorField σ H) s)
    (hF : ContMDiff I 𝓘(ℝ, ℝ) 1 F) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (F ∘ γ) (poissonBracket σ F H (γ t)) t := by
  sorry

/-- `φ` is a symplectic map from `σ` to `σ'`: it pulls `σ'` back to `σ`. The model spaces of
`M` and `M'` may differ, and `φ` need not be invertible: symplectic embeddings are symplectic
maps. -/
def IsSymplecticMap
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    (σ : SmoothTwoForm I M) (σ' : SmoothTwoForm I' M') (φ : M → M') : Prop :=
  ∀ x v w, σ' (φ x) (mfderiv I I' φ x v) (mfderiv I I' φ x w) = σ x v w

/-- A diffeomorphism `φ` is a symplectomorphism from `σ` to `σ'` when it is a symplectic map.
Like the linear `SymplecticForm.IsSymplectomorphism`, this is a predicate on an equivalence. -/
def IsSymplectomorphism
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {n : WithTop ℕ∞} (σ : SmoothTwoForm I M) (σ' : SmoothTwoForm I' M')
    (φ : M ≃ₘ^n⟮I, I'⟯ M') : Prop :=
  IsSymplecticMap σ σ' φ

/-- Milestone 2: the flow of a Hamiltonian vector field preserves `σ` (finite dimension,
boundaryless, Hausdorff). -/
theorem symplectic_maximalIntegralCurve [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold I M] {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) {F : M → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F) {x : M} {t : ℝ}
    (hxt : (x, t) ∈ maximalIntegralCurveFlowDomain (hamiltonianVectorField σ F))
    (v w : TangentSpace I x) :
    σ (maximalIntegralCurve (hamiltonianVectorField σ F) x t)
        (mfderiv I I (fun y ↦ maximalIntegralCurve (hamiltonianVectorField σ F) y t) x v)
        (mfderiv I I (fun y ↦ maximalIntegralCurve (hamiltonianVectorField σ F) y t) x w) =
      σ x v w := by
  sorry

/-! ## Layer 3: infinitesimal symmetries and moment maps -/

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

variable (I M) in
/-- An infinitesimal action of `𝔤` on `M` by smooth vector fields, with the convention of the
fundamental vector fields of a left action: `(⁅Z, Z'⁆)_M = -[Z_M, Z'_M]`. -/
structure InfinitesimalAction where
  /-- The vector field of an element of `𝔤`. -/
  toLinearMap : 𝔤 →ₗ[ℝ] ((x : M) → TangentSpace I x)
  contMDiff : ∀ Z, ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, toLinearMap Z x⟩ : TangentBundle I M))
  map_lie : ∀ Z Z', toLinearMap ⁅Z, Z'⁆ =
    -VectorField.mlieBracket I (toLinearMap Z) (toLinearMap Z')

variable {𝔤}

/-- `μ` is a moment map: `ι_{Z_M} σ = d⟨μ, Z⟩`, with each component smooth. -/
def IsMomentMap (σ : SmoothTwoForm I M) (a : InfinitesimalAction I M 𝔤)
    (μ : M → Module.Dual ℝ 𝔤) : Prop :=
  ∀ Z, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ μ x Z) ∧
    IsHamiltonianVectorField σ (fun x ↦ μ x Z) (a.toLinearMap Z)

/-- The cocycle of a moment map at a point: `{μ_Z, μ_Z'} - μ_{⁅Z, Z'⁆}`. -/
def momentCocycle (σ : SmoothTwoForm I M) (μ : M → Module.Dual ℝ 𝔤) (x : M) (Z Z' : 𝔤) : ℝ :=
  poissonBracket σ (fun y ↦ μ y Z) (fun y ↦ μ y Z') x - μ x ⁅Z, Z'⁆

/-- Layer 3: Noether's theorem. -/
theorem IsMomentMap.poissonBracket_eq_zero {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    {a : InfinitesimalAction I M 𝔤} {μ : M → Module.Dual ℝ 𝔤} (hμ : IsMomentMap σ a μ)
    {F : M → ℝ} (hF : IsHamiltonian σ F)
    {Z : 𝔤} (hinv : ∀ x, mvfderiv I F x (a.toLinearMap Z x) = 0) :
    poissonBracket σ (fun y ↦ μ y Z) F = 0 := by
  sorry

/-- Layer 3: on a preconnected manifold, the cocycle of a moment map is a constant Lie algebra
2-cocycle with trivial coefficients. -/
theorem IsMomentMap.exists_twoCocycle [PreconnectedSpace M] {σ : SmoothTwoForm I M}
    (hσ : σ.IsSymplectic) {a : InfinitesimalAction I M 𝔤} {μ : M → Module.Dual ℝ 𝔤}
    (hμ : IsMomentMap σ a μ) :
    ∃ c ∈ LieModule.Cohomology.twoCocycle ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ),
      ∀ x Z Z', ((c : LieModule.Cohomology.twoCochain ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ)) Z Z' :
        TrivialLieModule ℝ 𝔤 ℝ) = (TrivialLieModule.equiv ℝ 𝔤 ℝ).symm (momentCocycle σ μ x Z Z') := by
  sorry

end

end TauCetiRoadmap.HamiltonianSystems
