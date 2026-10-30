/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.NormalCoordinates
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition

namespace OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts

open _root_.AlgebraicGeometry
open _root_.OpenPartialHomeomorph

/-!
# Holomorphic support-flattening charts

Restricting to the open loci where a normal coordinate change and its inverse are analytic
upgrades centerwise analyticity to analyticity throughout each selected chart. All coordinate
changes come from the smooth closed immersion constructed earlier.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology Filter

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  (e : OpenPartialHomeomorph E F)

/-- Let `E` and `F` be complex Banach spaces and `e` a homeomorphism between open subsets of them.
This is the open set of points `x` in the source where `e` is complex analytic at `x` and its
inverse is complex analytic at `e(x)`. -/
def biAnalyticLocus : Set E :=
  {x | AnalyticAt ℂ e x} ∩ (e.source ∩ e ⁻¹' {y | AnalyticAt ℂ e.symm y})

theorem biAnalyticLocus_isOpen : IsOpen (biAnalyticLocus e) :=
  (isOpen_analyticAt ℂ e).inter (e.isOpen_inter_preimage (isOpen_analyticAt ℂ e.symm))

/-- Let `E` and `F` be complex Banach spaces and `e` a homeomorphism between open subsets. Restrict
its source to those `x` where both `e` at `x` and `e⁻¹` at `e(x)` are complex analytic. This is
the resulting homeomorphism between open subsets, analytic in both directions. -/
def biAnalyticRestrict : OpenPartialHomeomorph E F :=
  e.restrOpen (biAnalyticLocus e) (biAnalyticLocus_isOpen e)

end OpenPartialHomeomorph

section
namespace ComplexPoint

open _root_.OAI.AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y)

/-- Let `i : Y → X` be a closed immersion of smooth schemes over `ℂ`, of respective dimensions `m`
and `d`, and let `z ∈ Y(ℂ)`. Let `P` be the chosen left inverse of the coordinate derivative of
`i`. This continuous complex linear equivalence `ℂ^m × ker P ≃ ℂ^m × ℂ^{d-m}` leaves the first
coordinate fixed and uses a chosen basis on the normal space `ker P`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv :
    ((Fin m → ℂ) ×
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z).ker) ≃L[ℂ]
        ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)).prodCongr
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalKernelEquiv X Y i m d z)

/-- Let `i : Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`, and let `z
∈ Y(ℂ)`. In the chosen analytic charts write `g = e_X ∘ i ∘ e_Y⁻¹` and `a = e_Y(z)`. Choose a
complex linear left inverse `P` of `Dg(a)`. This local homeomorphism from `ℂ^d` to `ℂ^m ×
ℂ^{d-m}` inverts `(v,w) ↦ g(v)+w` near `(a,0)` and identifies `ker P` with `ℂ^{d-m}` using a
chosen basis. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange :
    OpenPartialHomeomorph (Fin d → ℂ) ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm.trans
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv X Y i m d z).toHomeomorph.toOpenPartialHomeomorph

/-- Let `i : Y → X` be a closed immersion of smooth schemes over `ℂ`, of respective dimensions `m`
and `d`, and let `z ∈ Y(ℂ)`. This chart maps a neighborhood of `i(z)` in `X(ℂ)` into `ℂ^m ×
ℂ^{d-m}`, with the image of `Y(ℂ)` equal to the zero set of the normal coordinate on the source.
The coordinate change from an ambient analytic chart and its inverse are holomorphic throughout
their domains. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart :
    OpenPartialHomeomorph (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)).trans
    (_root_.OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z))).restrOpen
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z).source
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z).open_source

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts
