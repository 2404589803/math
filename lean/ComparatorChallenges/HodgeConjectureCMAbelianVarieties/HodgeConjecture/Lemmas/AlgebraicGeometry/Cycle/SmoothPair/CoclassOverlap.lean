/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap

namespace OAI.AlgebraicGeometry.Cycle.SmoothPairOpen

open _root_.AlgebraicGeometry

/-!
# Exactly normalized smooth-support coclasses on overlaps

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap`.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace
open _root_.OAI.AlgebraicTopology.Singular

section
namespace ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y)

/-- Restriction is the map induced by the inclusion of support-complement pairs. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass_restrict
    {W V : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)} (hWV : W ⊆ V)
    (hV : V ⊆ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * (d - m))
      (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap hWV (Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i)))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z V hV) =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z W (hWV.trans hV) :=
  _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionTop.Singular.chartNormalProjectionCoclass_restrict _ _ _ _ _ hWV hV

variable (z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y)

/-- Exactly normalized ambient coclass agreement for the closed-immersion charts, from
smoothness, the closed immersion, and membership in its chart overlap and image. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_open_smoothClosedSupportChartCoclass_eq
    (x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hxS : x ∈ Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i))
    (hx : x ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hx' : x ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z').source) :
    ∃ (W : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
      (hW : (W : Set _) ⊆ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
      (hW' : (W : Set _) ⊆ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z').source),
      x ∈ W ∧ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z W hW =
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z' W hW' := by
  let e := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e' := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z'
  have ht : e x ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').source := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rwa [e.left_inv hx]
  exact _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionOverlap.Singular.exists_open_chartNormalProjectionCoclass_eq (d - m) e e' (Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i))
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z')
    x hx ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff
      X Y i m d z x hx).mp hxS) hx'
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition X Y i m d z z' (e x) ht)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition_symm X Y i m d z z' (e x) ht)

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.SmoothPairOpen
