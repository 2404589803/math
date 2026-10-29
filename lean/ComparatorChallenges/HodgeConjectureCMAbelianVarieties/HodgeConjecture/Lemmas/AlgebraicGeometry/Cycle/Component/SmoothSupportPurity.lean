/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity

namespace OAI.AlgebraicGeometry.Cycle.ComponentSmoothIsoHom

open _root_.AlgebraicGeometry

/-!
# Purity along the smooth locus of an integral cycle component

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity`.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace Opposite

section
namespace ComplexPoint

open _root_.OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- Its forward map displays the open-section identification, canonical
sheafification comparison on the open, and exact open-restriction homology comparison. -/
@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportLowestSectionCohomologyIso_hom :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx).hom =
      HomologicalComplex.homologyMap
        (_root_.OAI.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology.TopCat.openRestrictionTopSectionComplexIso (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))).inv
        (2 * (p : ℤ)) ≫
      _root_.OAI.AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection
        (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x))
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothRestrictedInjectiveComplex X x) (2 * (p : ℤ)) ⊤ ≫
      (_root_.OAI.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology.TopCat.openRestrictionHomologyTopSectionsIso (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))
        (2 * (p : ℤ))).hom := rfl

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.ComponentSmoothIsoHom
