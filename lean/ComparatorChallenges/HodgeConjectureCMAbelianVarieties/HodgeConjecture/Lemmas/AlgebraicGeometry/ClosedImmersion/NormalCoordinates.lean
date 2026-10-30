/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.NormalCoordinates

namespace OAI.AlgebraicGeometry.ClosedImmersion.NormalCoordinatesAt

open _root_.AlgebraicGeometry

/-!
# Normal coordinates for smooth closed immersions

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.NormalCoordinates`.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology Filter

section
namespace ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y)

/-- The normal parametrization is complex analytic at its center. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart :
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by
  let P := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z
  exact ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts X Y i m d z).comp
    (f := (ContinuousLinearMap.fst ℂ (Fin m → ℂ) P.ker))
    (x := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0))
    ((ContinuousLinearMap.fst ℂ (Fin m → ℂ) P.ker).analyticAt _)).add
      ((P.ker.subtypeL.analyticAt _).comp
        ((ContinuousLinearMap.snd ℂ (Fin m → ℂ) P.ker).analyticAt _))

/-- The inverse normal coordinates are complex analytic as well, by the analytic inverse
function theorem applied to the invertible complex derivative. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart_symm :
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)) := by
  let P := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z
  let e := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z
  have ha := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts X Y i m d z
  have hd := (_root_.OAI.Analysis.Foundations.SplitDerivativeNormalChart.HasStrictFDerivAt.add_kernel ha.hasStrictFDerivAt) P
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection_leftInverse X Y i m d z)
  have hder : fderiv ℂ e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) =
      ((_root_.OAI.Analysis.Foundations.SplitDerivativeNormalChart.ContinuousLinearMap.splitKernelEquiv (fderiv ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z)
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z))) P
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection_leftInverse X Y i m d z)).toContinuousLinearMap :=
    hd.hasFDerivAt.fderiv
  have h := e.analyticAt_symm'
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_source X Y i m d z)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart X Y i m d z) hder
  simpa only [e, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_apply, Submodule.coe_zero, add_zero,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts_at_center] using h

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_mem_source :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z).source :=
  ⟨⟨_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z),
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_target X Y i m d z⟩,
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_open_normalCriterion X Y i m d z).choose_spec.2.1⟩

/-- The chart flattens the whole geometric support. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_mem_range_iff (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i) ↔
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z y).2 = 0 :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_open_normalCriterion X Y i m d z).choose_spec.2.2 y hy.2

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_source :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z).source := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_source]
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_mem_source X Y i m d z

/-- The support is exactly the zero-normal plane throughout the chart source. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_range_iff (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i) ↔
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z y).2 = 0 := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_source] at hy
  simpa only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_apply, ContinuousLinearEquiv.map_eq_zero_iff] using
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_mem_range_iff X Y i m d z y hy

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.ClosedImmersion.NormalCoordinatesAt
