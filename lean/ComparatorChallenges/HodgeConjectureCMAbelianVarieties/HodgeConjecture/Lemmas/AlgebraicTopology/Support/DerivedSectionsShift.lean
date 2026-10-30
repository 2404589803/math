/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSections
import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusShift

namespace OAI.AlgebraicTopology.Support.DerivedSectionsShift

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Coherent shifts of concrete derived sections with support

Both concrete bounded-below support functors commute coherently with every
integer shift. This is constructed from their injective-resolution derived
units, via the generic `rightDerivedFunctorPlusCommShift` theorem. There is no
shift-comparison input. The localization/cone comparison and membership of a
proposed dualizing complex in the bounded-below category remain separate tasks.
-/

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace

universe u

namespace TopCat
open _root_.TopCat
namespace Sheaf
open _root_.TopCat
open _root_.TopCat.Sheaf

variable (X : TopCat.{u})

local instance : HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

local instance : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}

/-- Sheaf-valued derived sections with support commute coherently with shifts. -/
instance derivedSheafSectionsWithClosedSupport_commShift (Z : Closeds X) :
    (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsOn.TopCat.Sheaf.derivedSheafSectionsWithClosedSupport X Z).CommShift ℤ := by
  dsimp only [_root_.OAI.AlgebraicTopology.Support.DerivedSectionsOn.TopCat.Sheaf.derivedSheafSectionsWithClosedSupport]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sheaf-valued derived unit respects the shifts. -/
instance derivedSheafSectionsWithClosedSupportUnit_commShift (Z : Closeds X) :
    NatTrans.CommShift (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsOn.TopCat.Sheaf.derivedSheafSectionsWithClosedSupportUnit X Z) ℤ :=
  _root_.OAI.Algebra.Homology.DerivedFunctorPlusShift.CategoryTheory.Functor.rightDerivedFunctorPlusUnitCommShift (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsOn.TopCat.Sheaf.sheafSectionsWithClosedSupport X Z)

/-- Group-valued derived sections with support commute coherently with shifts. -/
instance derivedClosedSupportSections_commShift (Z : Closeds X) :
    (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsOn.TopCat.Sheaf.derivedClosedSupportSections X Z).CommShift ℤ := by
  dsimp only [_root_.OAI.AlgebraicTopology.Support.DerivedSectionsOn.TopCat.Sheaf.derivedClosedSupportSections]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The group-valued derived unit respects the shifts. -/
instance derivedClosedSupportSectionsUnit_commShift (Z : Closeds X) :
    NatTrans.CommShift (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsOn.TopCat.Sheaf.derivedClosedSupportSectionsUnit X Z) ℤ :=
  _root_.OAI.Algebra.Homology.DerivedFunctorPlusShift.CategoryTheory.Functor.rightDerivedFunctorPlusUnitCommShift (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsOn.TopCat.Sheaf.closedSupportSections X Z)

end Sheaf
end TopCat

end

end OAI.AlgebraicTopology.Support.DerivedSectionsShift
