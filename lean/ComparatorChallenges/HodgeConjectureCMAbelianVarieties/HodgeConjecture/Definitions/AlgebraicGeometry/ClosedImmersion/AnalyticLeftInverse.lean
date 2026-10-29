/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

namespace OAI.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse

open _root_.AlgebraicGeometry

/-!
# Analytic local left inverses from section lifting

Intrinsic regular coordinate functions lift through a closed immersion on a common affine
ambient neighborhood. Their analytic evaluations give a local left inverse to the inclusion
written in complex charts, and in particular the inclusion has injective derivative.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace Filter

section
namespace ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]

/-- Let `i : Y → X` be a morphism of smooth complex schemes of respective dimensions `m` and `d`,
and let `z ∈ Y(ℂ)`. If `eY` and `eX` are the chosen analytic charts at `z` and `i(z)`, this is
the coordinate expression `eX ∘ i ∘ eY⁻¹ : ℂ^m → ℂ^d`, valid where both charts are defined. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y) :
    (Fin m → ℂ) → (Fin d → ℂ) :=
  fun v => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z).symm v))

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse
