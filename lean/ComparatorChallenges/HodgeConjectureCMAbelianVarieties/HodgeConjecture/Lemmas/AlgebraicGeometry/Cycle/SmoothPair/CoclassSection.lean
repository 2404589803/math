/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection

namespace OAI.AlgebraicGeometry.Cycle.SmoothPairGerm

open _root_.AlgebraicGeometry

/-!
# The global exactly normalized smooth-support coclass section

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection`.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite
open _root_.OAI.AlgebraicTopology.Singular
open _root_.TopCat.Presheaf

section
namespace ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection_germ (x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection X Y i m d) =
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk X Y i m d x :=
  _root_.OAI.AlgebraicTopology.Sheaf.MapOfLocalStalks.TopCat.sectionOfLocallyRepresentable_germ
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk X Y i m d)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_locallyRepresentable X Y i m d) x

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.SmoothPairGerm
