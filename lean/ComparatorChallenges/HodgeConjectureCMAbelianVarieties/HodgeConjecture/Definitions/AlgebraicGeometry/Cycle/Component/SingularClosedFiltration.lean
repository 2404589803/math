/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.ClosedFiltration
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.SingularLocusDimension
import HodgeConjecture.Lemmas.Topology.Dimension.ClosedSubset
import Mathlib.Topology.NoetherianSpace
import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Analytification
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.AffineRelativeDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration

open _root_.AlgebraicGeometry

/-!
# Ambient closed supports for singular-component localization induction

The singular boundary of an integral cycle component carries its canonical finite reduced
smooth filtration, whose images are closed both algebraically and analytically in the ambient
variety, and whose successive differences are the complex-point images of smooth locally
closed strata. Their local relative dimensions are strictly below `d - p`, so their ambient
normal codimensions are at least `p + 1`.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

section

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. Start with `S₀ = Z_sing` and obtain `S_{k+1}` by removing the smooth locus
of the reduced scheme on `S_k`. This is the closed subset `S_k` of `Z`, for a natural number
`k`. -/
abbrev cycleComponentSingularClosedFiltration (k : ℕ) : Closeds (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponent X.left x) :=
  _root_.OAI.AlgebraicGeometry.Stratification.Basic.reducedSmoothClosedFiltration (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (_root_.OAI.AlgebraicGeometry.Stratification.Basic.singularLocusClosed (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom)) k

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. Start with `S₀ = Z_sing` and obtain `S_{k+1}` by removing the smooth locus
of the reduced scheme on `S_k`. This is the image of `S_k` as a closed subset of the ambient
scheme `X`. -/
def cycleComponentSingularAmbientClosedFiltration (k : ℕ) : Closeds X.left :=
  ⟨_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x '' (cycleComponentSingularClosedFiltration X x k : Set _),
    (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x).isClosedEmbedding.isClosedMap _
      (cycleComponentSingularClosedFiltration X x k).isClosed⟩

namespace ComplexPoint

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. Start with `S₀ = Z_sing` and obtain `S_{k+1}` by removing the smooth locus
of the reduced scheme on `S_k`. This is the analytically closed subset `S_k(ℂ) ⊆ X(ℂ)`, formed
by taking complex points whose underlying scheme points lie in `S_k`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration (k : ℕ) : Closeds (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
  ⟨_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.underlying ⁻¹' (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k : Set X.left),
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k).isClosed.preimage
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_underlying_to_zariski X)⟩

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. This is the smooth locus `Z_reg` as a scheme over `ℂ`, with structure
morphism induced by its inclusion in `Z` and then in `X`. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver : Over (Spec ↧ℂ) :=
  Over.mk (((_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x) ≫ X.hom)

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_locallyOfFiniteType :
    LocallyOfFiniteType (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x).hom := by
  change LocallyOfFiniteType
    (((_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
      _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration
