/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothClosedLift

namespace OAI.AlgebraicGeometry.Cycle.ComponentSmoothCoe

open _root_.AlgebraicGeometry

/-!
# The smooth-locus closed lift of an integral cycle component

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothClosedLift`.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

section

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

omit [IsIntegral X.left] [Smooth X.hom] in
/-- `X ∖ Z_sing` is the complement of the image of the component's singular locus: the
filtration index `0` in the definition contributes nothing. -/
@[simp] theorem coe_cycleComponentSmoothLocusAmbientOpen :
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x : Set X.left) =
      (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ''
        (_root_.OAI.AlgebraicGeometry.Stratification.Basic.singularLocusClosed (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom) : Set _))ᶜ := rfl

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The image of the lift is the restriction of the full component support. -/
theorem range_cycleComponentSmoothLocusClosedLift :
    Set.range (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x) =
      (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι ⁻¹' closure ({x} : Set X.left) := by
  rw [← _root_.OAI.AlgebraicGeometry.Cycle.SupportEq.range_cycleComponentι X.left x]
  exact _root_.OAI.AlgebraicGeometry.ClosedImmersion.SourceOpen.range_closedImmersionSourceOpenLift _ _

variable {p : ℕ}

/-- The smooth locus has the relative dimension of the integral component, constantly. -/
theorem cycleComponentSmoothLocus_smoothOfRelativeDimension (hx : Order.coheight x = p) :
    SmoothOfRelativeDimension (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p)
      ((_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom) := by
  let A := (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus
  let g := A.ι ≫ _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom
  let : Smooth g := _root_.OAI.AlgebraicGeometry.Cycle.SupportEq.cycleComponent_smoothLocus_smooth X x
  obtain ⟨m, hm⟩ := _root_.OAI.AlgebraicGeometry.Smooth.Equidimensional.exists_smoothOfRelativeDimension g
  obtain ⟨z, hzA, hzClosed⟩ := (_root_.OAI.AlgebraicGeometry.Cycle.ComponentNormal.dense_cycleComponent_smooth_closedPoints X x).nonempty
  let zA : A.toScheme := ⟨z, hzA⟩
  have hzAClosed : IsClosed ({zA} : Set A) := by
    have he : A.ι ⁻¹' ({z} : Set (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponent X.left x)) = {zA} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hzClosed.preimage A.ι.continuous
  have hmEq : m = _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p := by
    exact_mod_cast calc
      (m : ℕ∞) = Order.coheight zA :=
        (_root_.OAI.AlgebraicGeometry.Cycle.ComponentNormalCoordinates.SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
          (f := g) (d := m) zA hzAClosed).symm
      _ = Order.coheight z := (coheight_eq_of_isOpenImmersion (x := zA) A.ι).symm
      _ = _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p := _root_.OAI.AlgebraicGeometry.Cycle.ComponentClosedPointDimension.cycleComponent_closedPoint_coheight_eq_sub X x z hx hzClosed
  subst m
  exact hm

namespace ComplexPoint

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The analytic image of the algebraic boundary complement is the open used by the original
ambient supported resolution. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusAmbientOpen_analytic_image :
    Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x))) =
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x 0).compl : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion X]
  change (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.underlying : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X → X.left) ⁻¹'
      Set.range (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι = _
  rw [Scheme.Opens.range_ι]
  rfl

/-- The complex-point image of the closed lift is precisely the restricted full support. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusClosedLift_complexPoints_range :
    Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x)) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x)) ⁻¹'
          (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x) := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion]
  change (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.underlying : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x) →
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x).left) ⁻¹'
      Set.range (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x) = _
  rw [_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothCoe.range_cycleComponentSmoothLocusClosedLift]
  rfl

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.ComponentSmoothCoe
