/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyInjectiveModel

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

namespace OAI.AlgebraicTopology.Support.CohomologyInjectiveRestrict

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Naturality of the injective model in the pair

For `U' ≤ U` and `V' ≤ V`, the identification `H^n(V, V ⊓ U; F) ≃ H^n(Γ_{X ∖ U}(V, I))` commutes
with the map of pairs on the left and with support enlargement followed by restriction on the
right.
-/

noncomputable section

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace

namespace TopCat
open _root_.TopCat
namespace Sheaf
open _root_.TopCat
open _root_.TopCat.Sheaf

variable (X : TopCat.{0})

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable {U V W U' V' W' : Opens X} (hW : V ⊓ U = W) (hW' : V' ⊓ U' = W')
  (hU : U' ≤ U) (hV : V' ≤ V) (hWW : W' ≤ W)

lemma pairSheafHomEvaluation_restrict (G : Sheaf AddCommGrpCat X) :
    (preadditiveCoyoneda.map (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafMap
        (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _)).op).app G ≫
        _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomEvaluation X U' V' W' hW' G =
      _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomEvaluation X U V W hW G ≫ G.obj.map (homOfLE hV).op := by
  apply AddCommGrpCat.hom_ext
  refine AddMonoidHom.ext (fun φ => ?_)
  exact _root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafHomAddEquiv_pairSheafMap_comp
    (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
    (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) G φ

lemma pairSheafHomIsoSupportedSections_restrict (G : Sheaf AddCommGrpCat X) :
    (preadditiveCoyoneda.map (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafMap
        (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _)).op).app G ≫
        (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections X U' V' W' hW' G).hom =
      (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections X U V W hW G).hom ≫
        ((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU).app G).hom.app (op V) ≫
          ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').obj G).obj.map (homOfLE hV).op := by
  apply (cancel_mono (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V'))).1
  have h1 : ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').obj G).obj.map (homOfLE hV).op ≫
      ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V') =
      ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V) ≫
        G.obj.map (homOfLE hV).op :=
    ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.naturality (homOfLE hV).op
  have h2 : ((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU).app G).hom.app (op V) ≫
      ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V) =
      ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app G).hom.app (op V) := by
    change (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU).app G ≫
      (_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V)) = _
    rw [← NatTrans.comp_app, _root_.OAI.AlgebraicTopology.Support.DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap_inclusion]
  rw [Category.assoc, _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections_hom_inclusion,
    pairSheafHomEvaluation_restrict X hW hW' hV hWW, Category.assoc, Category.assoc, h1,
    ← Category.assoc (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU).app G).hom.app (op V)), h2,
    ← Category.assoc, _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections_hom_inclusion]

lemma homComplexPairSheafIsoSupportedSections_restrict
    (K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ) :
    _root_.OAI.Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap ((CochainComplex.singleFunctor _ 0).map
        (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafMap
          (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
          (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _))) K ≫
        (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections X U' V' W' hW' K).hom =
      (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections X U V W hW K).hom ≫
        _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K := by
  dsimp only [_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections, Iso.trans_hom]
  rw [← Category.assoc,
    _root_.OAI.Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap_single_fromSingleZeroIsoPreadditiveCoyoneda,
    Category.assoc, Category.assoc]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  exact pairSheafHomIsoSupportedSections_restrict X hW hW' hU hV hWW (K.X n)

variable [HasExt.{1} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

local instance :
    HasDerivedCategory (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
  HasDerivedCategory.standard _

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The injective model is natural in the pair. -/
theorem relHAddEquivSupportedSectionsHomology_restrict
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ)
    (x : _root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology X U' V' W' hW' F I ι n
        (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict F _ _ (homOfLE hWW) (homOfLE hV)
          (Subsingleton.elim _ _) n x) =
      HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV I) n
        (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology X U V W hW F I ι n x) := by
  obtain ⟨g, hg⟩ : ∃ g : _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U' V' W' hW' ⟶ _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW,
      g = _root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafMap
        (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) := ⟨_, rfl⟩
  have hA : Ext.homAddEquiv (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict F
      (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
      (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) n x) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map g) ≫ Ext.homAddEquiv x := by
    rw [hg]
    simp only [_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict, Ext.homAddEquiv_apply,
      Ext.bilinearComp_apply_apply, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
    rfl
  have hB (y : ShiftedHom
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW)))
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)) (n : ℤ)) :
      _root_.OAI.Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv (Iso.refl (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor _ 0).obj (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U' V' W' hW'))))
        ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map ι)))
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map g) ≫ y) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map g) ≫
        _root_.OAI.Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv (Iso.refl (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor _ 0).obj (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW))))
        ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map ι))) y := by
    simp [_root_.OAI.Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv_apply]
  have hD (c : CochainComplex.HomComplex.CohomologyClass
      ((CochainComplex.singleFunctor _ 0).obj (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW)) I n) :
      (CochainComplex.HomComplex.homologyAddEquiv _ I n).symm
        (_root_.OAI.Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompClass ((CochainComplex.singleFunctor _ 0).map g) I n c) =
      HomologicalComplex.homologyMap (_root_.OAI.Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap
        ((CochainComplex.singleFunctor _ 0).map g) I) n
        ((CochainComplex.HomComplex.homologyAddEquiv _ I n).symm c) := by
    apply (CochainComplex.HomComplex.homologyAddEquiv _ I n).injective
    rw [_root_.OAI.Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.homologyAddEquiv_precompMap, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]
  have hE : HomologicalComplex.homologyMap (_root_.OAI.Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap
        ((CochainComplex.singleFunctor _ 0).map g) I) n ≫
        HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections X U' V' W' hW' I).hom n =
      HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections X U V W hW I).hom n ≫
        HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV I) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hg,
      homComplexPairSheafIsoSupportedSections_restrict X hW hW' hU hV hWW I]
  have hF (z : (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor _ 0).obj (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW)) I).homology n) :
      (HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections X U' V' W' hW' I).hom
        n).hom ((HomologicalComplex.homologyMap (_root_.OAI.Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap
          ((CochainComplex.singleFunctor _ 0).map g) I) n).hom z) =
      (HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV I) n).hom
        ((HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections X U V W hW I).hom
          n).hom z) := by
    have := congrArg AddCommGrpCat.Hom.hom hE
    rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp] at this
    exact DFunLike.congr_fun this z
  dsimp only [_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology, AddEquiv.trans_apply]
  rw [hA]
  erw [hB]
  rw [_root_.OAI.Algebra.Homology.DerivedCategoryInjectiveHom.CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_precomp, hD]
  rw [Iso.addCommGroupIsoToAddEquiv_apply, Iso.addCommGroupIsoToAddEquiv_apply,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_hom, hF]
  rfl

end Sheaf
end TopCat

end

end OAI.AlgebraicTopology.Support.CohomologyInjectiveRestrict
