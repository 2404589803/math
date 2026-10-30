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

import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyFlasqueModel
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.CohomologyInjectiveModel

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

namespace OAI.AlgebraicTopology.Support.CohomologyFlasqueRestrict

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Naturality of the flasque model in the pair

The identification `H^n(V, V ⊓ U; F) ≃ H^n(Γ_{X ∖ U}(V, K))` commutes with the map of pairs and
with support enlargement followed by restriction.
-/

noncomputable section

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace

namespace TopCat
open _root_.TopCat
namespace Sheaf
open _root_.TopCat
open _root_.TopCat.Sheaf

variable (X : TopCat.{0})

variable {U V U' V' : Opens X} (hU : U' ≤ U) (hV : V' ≤ V)

lemma supportedSectionsRestriction_naturality
    {K L : CochainComplex (Sheaf AddCommGrpCat X) ℤ} (φ : K ⟶ L) :
    _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K ≫
        ((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
          (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map φ) =
      ((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
          (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map φ) ≫
        _root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV L := by
  have h1 := (NatTrans.mapHomologicalComplex (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportEvaluationRestriction X (homOfLE hV))
    ℤᵘᵖ).naturality (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map φ)
  have h2 := (NatTrans.mapHomologicalComplex (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU)
    ℤᵘᵖ).naturality φ
  dsimp only [_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction, _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction]
  simp only [Category.assoc]
  rw [← h1]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← h2]

variable {W W' : Opens X} (hW : V ⊓ U = W) (hW' : V' ⊓ U' = W') (hWW : W' ≤ W)
  (F : Sheaf AddCommGrpCat X) (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ) [K.IsStrictlyGE 0]
  (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ K) [Mono ι] [QuasiIso ι]
  (hK : ∀ n, IsFlasque (K.X n))

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable [HasExt.{1} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The flasque model is natural in the pair. -/
theorem relHAddEquivSupportedSectionsHomologyOfFlasque_restrict (n : ℕ)
    (x : _root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    _root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque X F K ι U' V' W' hW' hK n
        (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict F _ _ (homOfLE hWW) (homOfLE hV)
          (Subsingleton.elim _ _) n x) =
      HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n
        (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque X F K ι U V W hW hK n x) := by
  have := _root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.supportedSections_map_resolutionToInjective_quasiIso X F K ι U V hK
  have := _root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.supportedSections_map_resolutionToInjective_quasiIso X F K ι U' V' hK
  have hnat : HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n ≫
      HomologicalComplex.homologyMap (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
        (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map
          (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective X F K ι))) n =
      HomologicalComplex.homologyMap (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
        (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
          (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective X F K ι))) n ≫
        HomologicalComplex.homologyMap
          (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      supportedSectionsRestriction_naturality]
  have hinv : inv (HomologicalComplex.homologyMap
        (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
          (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
            (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective X F K ι))) n) ≫
        HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n =
      HomologicalComplex.homologyMap
          (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)) n ≫
        inv (HomologicalComplex.homologyMap
          (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
            (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map
              (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective X F K ι))) n) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hF (z : (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
        (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F))).homology n) :
      (inv (HomologicalComplex.homologyMap
          (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
            (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map
              (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective X F K ι))) n)).hom
        ((HomologicalComplex.homologyMap
          (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)) n).hom z) =
      (HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n).hom
        ((inv (HomologicalComplex.homologyMap
          (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
            (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
              (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective X F K ι))) n)).hom z) := by
    have := congrArg AddCommGrpCat.Hom.hom hinv
    rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp] at this
    exact (DFunLike.congr_fun this z).symm
  dsimp only [_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque, AddEquiv.trans_apply]
  rw [@_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveRestrict.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology_restrict X U V W U' V' W' hW hW' hU hV hWW _ F
    (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F) (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex_isKInjective X F)
    (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionAugmentation X F) (_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionAugmentation_quasiIso X F) n x,
    Iso.addCommGroupIsoToAddEquiv_apply, Iso.addCommGroupIsoToAddEquiv_apply, Iso.symm_hom,
    Iso.symm_hom, asIso_inv, asIso_inv, hF]

end Sheaf
end TopCat

end

end OAI.AlgebraicTopology.Support.CohomologyFlasqueRestrict
