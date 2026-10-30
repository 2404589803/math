/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension

namespace OAI.AlgebraicGeometry.Cycle.ComponentSupportIsoHom

open _root_.AlgebraicGeometry

/-!
# Unique extension across a cycle component's singular boundary

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension`.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite

section
namespace ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportExtensionIso_hom :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportExtensionIso X x hx).hom =
      HomologicalComplex.homologyMap (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ)) := rfl

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.ComponentSupportIsoHom
