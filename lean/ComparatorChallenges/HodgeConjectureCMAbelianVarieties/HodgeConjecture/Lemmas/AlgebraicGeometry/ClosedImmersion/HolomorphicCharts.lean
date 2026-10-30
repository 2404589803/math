/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts

namespace OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicChartsAt

open _root_.AlgebraicGeometry
open _root_.OpenPartialHomeomorph

/-!
# Holomorphic support-flattening charts

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts`.
-/

/-! ### Constructions used only in proofs -/

noncomputable section

open _root_.CategoryTheory _root_.Topology Filter

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  (e : OpenPartialHomeomorph E F)

theorem biAnalyticRestrict_mem_source_iff (x : E) :
    x ∈ (_root_.OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e).source ↔
      x ∈ e.source ∧ AnalyticAt ℂ e x ∧ AnalyticAt ℂ e.symm (e x) := by
  change (x ∈ e.source ∧ AnalyticAt ℂ e x ∧ x ∈ e.source ∧ AnalyticAt ℂ e.symm (e x)) ↔ _
  aesop

end OpenPartialHomeomorph

section
namespace ComplexPoint

open _root_.OAI.AlgebraicTopology.Singular
variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y)

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i) ↔
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z y).2 = 0 :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_range_iff X Y i m d z y hy.2

end ComplexPoint
end

section
namespace ComplexPoint

open _root_.OAI.AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y)

/-- The underlying normal coordinate change and its inverse are analytic at every ambient
source point. -/
theorem closedImmersionHolomorphicFlatteningChart_analytic (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) y) ∧
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).symm
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z y) :=
  ((_root_.OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicChartsAt.OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mp hy.1.2).2

theorem closedImmersionNormalCoordinateChange_symm_at_chart (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).symm
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z y) =
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) y :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).left_inv hy.1.2.1

variable (z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y)

/-- Let `i : Y → X` be a closed immersion of smooth schemes over `ℂ` of dimensions `m` and `d`,
respectively. Choose points `z,z′ ∈ Y(ℂ)` and their holomorphic charts `e_z,e_z′` in `ℂ^m ×
ℂ^{d-m}` that identify the image of `Y(ℂ)` with the locus where the second coordinate is zero.
This local homeomorphism is the coordinate change `e_z′ ∘ e_z⁻¹` on the overlap. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition :
    OpenPartialHomeomorph ((Fin m → ℂ) × (Fin (d - m) → ℂ))
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).symm.trans
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z')

/-- These transitions are holomorphic throughout their domains. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').source) :
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z') v := by
  let e := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e' := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z'
  let C := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)
  let C' := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z')
  let A := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z
  let A' := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z'
  let y := e.symm v
  have hyv : y ∈ e.source := e.map_target hv.1
  have hyv' : y ∈ e'.source := hv.2
  have hyC : y ∈ C.source := hyv.1.1
  have hyC' : y ∈ C'.source := hyv'.1.1
  have hAv := closedImmersionNormalCoordinateChange_symm_at_chart
    X Y i m d z y hyv
  rw [e.right_inv hv.1] at hAv
  have hA := (closedImmersionHolomorphicFlatteningChart_analytic
    X Y i m d z y hyv).2
  rw [e.right_inv hv.1] at hA
  have hA' := (closedImmersionHolomorphicFlatteningChart_analytic
    X Y i m d z' y hyv').1
  have hCC : AnalyticAt ℂ (fun w => C' (C.symm w)) (C y) := by
    apply _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_transition X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z')
    refine ⟨C.map_source hyC, ?_⟩
    change C.symm (C y) ∈ C'.source
    rw [C.left_inv hyC]
    exact hyC'
  have hCC' : AnalyticAt ℂ (fun w => C' (C.symm w)) (A.symm v) := hAv ▸ hCC
  have hmiddle := hCC'.comp hA
  have himage : C' (C.symm (A.symm v)) = C' y := by rw [hAv, C.left_inv hyC]
  have hlast : AnalyticAt ℂ A' (C' (C.symm (A.symm v))) := himage ▸ hA'
  exact hlast.comp (f := fun w => C' (C.symm (A.symm w))) (x := v) hmiddle

/-- The inverse transition is holomorphic at the image of every source point. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition_symm
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').source) :
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').symm
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z' v) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition X Y i m d z' z
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z' v)
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').map_source hv)

end ComplexPoint
end

end

noncomputable section

open _root_.CategoryTheory _root_.Topology Filter

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  (e : OpenPartialHomeomorph E F)

@[simp] theorem biAnalyticRestrict_apply (x : E) : (_root_.OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e) x = e x := rfl
@[simp] theorem biAnalyticRestrict_symm_apply (y : F) : (_root_.OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e).symm y = e.symm y := rfl

end OpenPartialHomeomorph

section
namespace ComplexPoint

open _root_.OAI.AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y)

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange_mem_source :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).source :=
  ⟨_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_target X Y i m d z, trivial⟩

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange_center :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)) =
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by
  change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv X Y i m d z
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm _) = _
  simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv]

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalCoordinateChange :
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)) :=
  ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv X Y i m d z).toContinuousLinearMap.analyticAt
    _).comp (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart_symm X Y i m d z)

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalCoordinateChange_symm :
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).symm
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by
  let K := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv X Y i m d z
  have hK : K.symm (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) = (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by
    simp [K, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv]
  have hA' : AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z)
      (K.symm (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0)) := hK ▸ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart X Y i m d z
  exact hA'.comp (K.symm.toContinuousLinearMap.analyticAt _)

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_apply (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z y := rfl

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_symm_apply
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ)) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).symm v =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)).symm
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).symm v) := rfl

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_source :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source := by
  refine ⟨⟨_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z), ?_⟩,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_source X Y i m d z⟩
  apply (_root_.OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicChartsAt.OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mpr
  refine ⟨_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange_mem_source X Y i m d z,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalCoordinateChange X Y i m d z, ?_⟩
  simp only [OpenPartialHomeomorph.symm_symm]
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange_center]
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalCoordinateChange_symm X Y i m d z

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_center :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_center X Y i m d z

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicChartsAt
