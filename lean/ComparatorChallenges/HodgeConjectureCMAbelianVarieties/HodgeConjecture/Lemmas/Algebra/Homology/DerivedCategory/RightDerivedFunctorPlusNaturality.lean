/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

namespace OAI.Algebra.Homology.DerivedFunctorPlusNaturality

open _root_.CategoryTheory
open _root_.CategoryTheory.NatTrans

/-!
# Natural transformations on bounded-below right derived functors

A natural transformation of additive functors induces a transformation of their
right derived functors. The construction uses the derived universal property,
and its compatibility with the derived units is proved. This supplies, for
example, the canonical support-enlargement and forget-support maps.
-/

noncomputable section

open _root_.CategoryTheory

namespace CategoryTheory
open _root_.CategoryTheory
namespace NatTrans
open _root_.CategoryTheory
open _root_.CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- Let `F,G : C → D` be additive functors between abelian categories and `α : F → G` a natural
transformation. Applying `α` in each degree of a bounded-below cochain complex gives this
transformation between the induced functors on bounded-below homotopy categories. -/
def mapHomotopyCategoryPlus (α : F ⟶ G) :
    F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus where
  app K := ObjectProperty.homMk ((α.mapHomotopyCategory ℤᵘᵖ).app K.obj)
  naturality K L f := by
    ext
    exact (α.mapHomotopyCategory ℤᵘᵖ).naturality f.hom

@[simp]
theorem mapHomotopyCategoryPlus_id (F : C ⥤ D) [F.Additive] :
    _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.mapHomotopyCategoryPlus (𝟙 F) = 𝟙 F.mapHomotopyCategoryPlus := rfl

@[simp]
theorem mapHomotopyCategoryPlus_comp (α : F ⟶ G) (β : G ⟶ H) :
    _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.mapHomotopyCategoryPlus (α ≫ β) =
      _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.mapHomotopyCategoryPlus α ≫ _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.mapHomotopyCategoryPlus β := rfl

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- Let `F,G : C → D` be additive functors between abelian categories with derived categories, and
assume `C` has enough injectives. A natural transformation `α : F → G` induces this
transformation `RF → RG` on bounded-below derived categories. It is computed by applying `α`
degreewise to an injective resolution. -/
def rightDerivedFunctorPlus (α : F ⟶ G) :
    F.rightDerivedFunctorPlus ⟶ G.rightDerivedFunctorPlus :=
  Functor.rightDerivedNatTrans F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso C)
        (Functor.whiskerRight (_root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.mapHomotopyCategoryPlus α) DerivedCategory.Plus.Qh)

/-- Compatibility with the derived units on every bounded-below homotopy complex. -/
@[reassoc (attr := simp)]
theorem rightDerivedFunctorPlus_unit (α : F ⟶ G) :
    F.rightDerivedFunctorPlusUnith ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (_root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus α) =
      Functor.whiskerRight (_root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.mapHomotopyCategoryPlus α) DerivedCategory.Plus.Qh ≫
        G.rightDerivedFunctorPlusUnith :=
  Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

/-- The pointwise form pins the derived transformation to the coefficient transformation
when computing on an injective resolution. -/
@[reassoc (attr := simp)]
theorem rightDerivedFunctorPlus_unit_app (α : F ⟶ G)
    (K : HomotopyCategory.Plus C) :
    F.rightDerivedFunctorPlusUnith.app K ≫
        (_root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus α).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((_root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.mapHomotopyCategoryPlus α).app K) ≫
        G.rightDerivedFunctorPlusUnith.app K :=
  Functor.rightDerivedNatTrans_app _ _ _ _ _ _ _

@[simp]
theorem rightDerivedFunctorPlus_id (F : C ⥤ D) [F.Additive] :
    _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus (𝟙 F) = 𝟙 F.rightDerivedFunctorPlus := by
  simp [_root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus]

@[simp]
theorem rightDerivedFunctorPlus_comp (α : F ⟶ G) (β : G ⟶ H) :
    _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus (α ≫ β) =
      _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus α ≫ _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus β := by
  simp [_root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus]

end NatTrans
end CategoryTheory

namespace CategoryTheory
open _root_.CategoryTheory
namespace NatIso
open _root_.CategoryTheory
open _root_.CategoryTheory.NatIso

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- Let `F,G : C → D` be additive functors between abelian categories with derived categories, and
assume `C` has enough injectives. A natural isomorphism `e : F ≅ G` induces this isomorphism `RF
≅ RG` on bounded-below derived categories, by applying `e` degreewise to injective resolutions. -/
def rightDerivedFunctorPlus (e : F ≅ G) :
    F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus where
  hom := (_root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus e.hom)
  inv := (_root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus e.inv)
  hom_inv_id := by
    rw [← _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus_comp, e.hom_inv_id,
      _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus_id]
  inv_hom_id := by
    rw [← _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus_comp, e.inv_hom_id,
      _root_.OAI.Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus_id]

end NatIso
end CategoryTheory

end

end OAI.Algebra.Homology.DerivedFunctorPlusNaturality
