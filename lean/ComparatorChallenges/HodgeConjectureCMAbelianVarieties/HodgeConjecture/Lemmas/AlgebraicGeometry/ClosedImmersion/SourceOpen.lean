/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.SourceOpen

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicGeometry.ClosedImmersion.SourceOpenIs

open _root_.AlgebraicGeometry

/-!
# Restricting the source of a closed immersion without losing closedness

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.SourceOpen`.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

section
namespace ComplexPoint

/-- The actual immersion image formula, with structure-map compatibility bundled in `i`. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion_of_comm (X Y : Over (Spec ↧ℂ))
    (i : Y ⟶ X) [IsImmersion i.left] [LocallyOfFiniteType X.hom] :
    Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i) =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.underlying : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X → X.left) ⁻¹' Set.range i.left := by
  let : LocallyOfFiniteType Y.hom := by
    rw [← i.w]
    infer_instance
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion X i

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.ClosedImmersion.SourceOpenIs
