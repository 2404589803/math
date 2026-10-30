/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration
import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.SourceOpen
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension
import Mathlib.RingTheory.DedekindDomain.Basic

namespace OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift

open _root_.AlgebraicGeometry

/-!
# The smooth-locus closed lift of an integral cycle component

The ambient open is the complement of the first canonical singular-boundary support, and
the smooth locus embeds closed in it. Its constant relative dimension is `d-p`, by smooth
equidimensionality together with the coheight formula for a closed point of the integral
component.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

section

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the Zariski open subset `X \ Z_sing`, obtained by
removing the singular locus of `Z`, viewed as a closed subset of `X`. -/
def cycleComponentSmoothLocusAmbientOpen : X.left.Opens :=
  (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x 0).compl

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the open subscheme `X \ Z_sing` together with its
structure morphism to `Spec ℂ`, restricted from that of `X`. -/
abbrev cycleComponentSmoothLocusAmbientOpenOver : Over (Spec ↧ℂ) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X (cycleComponentSmoothLocusAmbientOpen X x)

instance cycleComponentSmoothLocusAmbientOpenOver_locallyOfFiniteType :
    LocallyOfFiniteType (cycleComponentSmoothLocusAmbientOpenOver X x).hom := by
  change LocallyOfFiniteType ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom)
  infer_instance

instance cycleComponentSmoothLocusAmbientOpenInclusion_isImmersion :
    IsImmersion
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)).left := by
  change IsImmersion (cycleComponentSmoothLocusAmbientOpen X x).ι
  infer_instance

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. The smooth locus `Z_reg` is closed in `X \ Z_sing`. This is its
closed immersion into that open subscheme, obtained by restricting the inclusion `Z → X`. -/
def cycleComponentSmoothLocusClosedLift :
    (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.toScheme ⟶
      (cycleComponentSmoothLocusAmbientOpen X x).toScheme :=
  _root_.OAI.AlgebraicGeometry.ClosedImmersion.SourceOpen.closedImmersionSourceOpenLift (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x) (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance cycleComponentSmoothLocusClosedLift_isClosedImmersion :
    IsClosedImmersion (cycleComponentSmoothLocusClosedLift X x) := by
  dsimp [cycleComponentSmoothLocusClosedLift]
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] in
@[reassoc (attr := simp)]
theorem cycleComponentSmoothLocusClosedLift_ι :
    cycleComponentSmoothLocusClosedLift X x ≫ (cycleComponentSmoothLocusAmbientOpen X x).ι =
      (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x :=
  _root_.OAI.AlgebraicGeometry.ClosedImmersion.SourceOpen.closedImmersionSourceOpenLift_ι _ _

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the closed immersion `Z_reg → X \ Z_sing` as a morphism
of schemes over `ℂ`; both structure maps are induced by that of `X`. -/
def cycleComponentSmoothLocusClosedLiftOver :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x ⟶
      cycleComponentSmoothLocusAmbientOpenOver X x :=
  Over.homMk (cycleComponentSmoothLocusClosedLift X x) (by
    change cycleComponentSmoothLocusClosedLift X x ≫
      ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom) =
        ((_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
          _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x) ≫ X.hom
    rw [← Category.assoc, cycleComponentSmoothLocusClosedLift_ι])

instance cycleComponentSmoothLocusClosedLiftOver_isClosedImmersion :
    IsClosedImmersion (cycleComponentSmoothLocusClosedLiftOver X x).left := by
  change IsClosedImmersion (cycleComponentSmoothLocusClosedLift X x)
  infer_instance

variable {d p : ℕ} [SmoothOfRelativeDimension d X.hom]

/-- The ambient open retains the original smooth relative dimension. These stay generic in
`d`: they are instances, found by resolution, and narrowing them to `dim X.left` would make
them fire less often. -/
instance cycleComponentSmoothLocusAmbientOpen_smoothOfRelativeDimension :
    SmoothOfRelativeDimension d ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (cycleComponentSmoothLocusAmbientOpen X x).ι X.hom

instance cycleComponentSmoothLocusAmbientOpenOver_smoothOfRelativeDimension :
    SmoothOfRelativeDimension d (cycleComponentSmoothLocusAmbientOpenOver X x).hom := by
  change SmoothOfRelativeDimension d
    ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom)
  infer_instance

namespace ComplexPoint

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is `Z(ℂ)` as a closed subset of the analytic space `X(ℂ)`,
namely the complex points whose underlying scheme points lie in `Z`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport : Closeds (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
  ⟨_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x, _root_.OAI.AlgebraicGeometry.Cycle.SupportEq.isClosed_cycleComponentSupport X x⟩

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift
