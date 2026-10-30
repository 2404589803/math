/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SectionRestrictionCone
import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality
import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingConeMapNaturality

namespace OAI.AlgebraicTopology.Support.SectionRestrictionConeNaturality

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Restriction naturality of the supported-section kernel comparison

Every map below is induced by the restriction of sheaf sections. In
particular the short-exact-sequence lift is the positive canonical lift; its
naturality is established before passing to homology or sheafification.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

namespace TopCat
open _root_.TopCat
namespace Sheaf
open _root_.TopCat
open _root_.TopCat.Sheaf

variable (X : TopCat.{u})

/-- Section restriction around a rectangle of open inclusions. -/
lemma sectionComplexRestriction_square {I : Type*} (c : ComplexShape I)
    (K : HomologicalComplex (Sheaf AddCommGrpCat.{u} X) c)
    {V W V' W' : Opens X} (i : W ⟶ V) (i' : W' ⟶ V')
    (a : V' ⟶ V) (b : W' ⟶ W) :
    _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X c K i ≫ _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X c K b =
      _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X c K a ≫ _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X c K i' := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (K.X n).obj.map i.op ≫ (K.X n).obj.map b.op =
    (K.X n).obj.map a.op ≫ (K.X n).obj.map i'.op
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Let `K` be an integer-indexed complex of sheaves of abelian groups on a topological space `X`.
For nested opens `W ⊆ V`, `W′ ⊆ V′`, with `V′ ⊆ V` and `W′ ⊆ W`, restriction induces this map
`Cone(K(V) → K(W)) → Cone(K(V′) → K(W′))`. -/
def sectionComplexRestrictionConeMap
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    {V W V' W' : Opens X} (i : W ⟶ V) (i' : W' ⟶ V')
    (a : V' ⟶ V) (b : W' ⟶ W) :
    CochainComplex.mappingCone (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K i) ⟶
      CochainComplex.mappingCone (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K i') :=
  CochainComplex.mappingCone.map _ _
    (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K a)
    (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K b)
    (sectionComplexRestriction_square X ℤᵘᵖ K i i' a b)

variable (U : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
  {V W : Opens X} (a : W ⟶ V)

/-- Let `K` be an integer-indexed complex of sheaves of abelian groups on a topological space `X`,
with `U` open and `W ⊆ V` open. This restricts all three complexes in `Γ_{X \ U}(V,K) → K(V) →
K(V ∩ U)` to the corresponding complexes over `W`. -/
def supportRestrictionSectionsComplexMap :
    _root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K ⟶
      _root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U W K where
  τ₁ := _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
    (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionComplexShortComplex X U K).X₁ a
  τ₂ := _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K a
  τ₃ := _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
    (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionComplexShortComplex X U K).X₃ a
  comm₁₂ := (((_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportEvaluationRestriction X a).mapHomologicalComplex ℤᵘᵖ).naturality
    (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionComplexShortComplex X U K).f).symm
  comm₂₃ := (((_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportEvaluationRestriction X a).mapHomologicalComplex ℤᵘᵖ).naturality
    (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionComplexShortComplex X U K).g).symm

/-- The pushforward/intersection identification commutes with restriction. -/
@[reassoc]
lemma supportedOutsideIntersectionIso_naturality (F : Sheaf AddCommGrpCat.{u} X) :
    ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.openRestrictionPushforward X U).obj F).obj.map a.op ≫
      (_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.supportedOutsideIntersectionIso X U W F).hom =
    (_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.supportedOutsideIntersectionIso X U V F).hom ≫
      F.obj.map (homOfLE (inf_le_inf_right U (leOfHom a))).op := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Naturality of the intersection identification on coefficient complexes. -/
@[reassoc]
lemma supportRestrictionSectionsIntersectionIso_naturality :
    (supportRestrictionSectionsComplexMap X U K a).τ₃ ≫
      (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsIntersectionIso X U W K).hom =
    (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsIntersectionIso X U V K).hom ≫
      _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K
        (homOfLE (inf_le_inf_right U (leOfHom a))) :=
  HomologicalComplex.Hom.ext
    (funext fun n ↦ supportedOutsideIntersectionIso_naturality X U a (K.X n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cone identification is a standard cone map with the specified components. -/
lemma supportRestrictionSectionsConeIso_hom (V : Opens X) :
    (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsConeIso X U V K).hom =
      CochainComplex.mappingCone.map _ _ (𝟙 _)
        (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsIntersectionIso X U V K).hom
        (by simpa using _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsIntersectionIso_restriction X U V K) :=
  _root_.OAI.Algebra.Homology.MappingConeMapNaturality.CochainComplex.mappingCone.mapArrowHom_eq_map _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cone identification respects restriction of the entire supported-section sequence. -/
@[reassoc]
lemma supportRestrictionSectionsConeIso_naturality :
    CochainComplex.mappingCone.map _ _
      (supportRestrictionSectionsComplexMap X U K a).τ₂
      (supportRestrictionSectionsComplexMap X U K a).τ₃
      (supportRestrictionSectionsComplexMap X U K a).comm₂₃.symm ≫
        (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsConeIso X U W K).hom =
    (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsConeIso X U V K).hom ≫
      sectionComplexRestrictionConeMap X K (Opens.infLELeft V U) (Opens.infLELeft W U)
        a (homOfLE (inf_le_inf_right U (leOfHom a))) := by
  rw [supportRestrictionSectionsConeIso_hom, supportRestrictionSectionsConeIso_hom]
  dsimp only [sectionComplexRestrictionConeMap]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1
  exact supportRestrictionSectionsIntersectionIso_naturality X U K a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The flasque kernel-to-cone comparison is natural on homology in the ambient open. -/
@[reassoc]
lemma supportedSectionHomologyIsoRestrictionCone_naturality
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ) :
    HomologicalComplex.homologyMap (supportRestrictionSectionsComplexMap X U K a).τ₁ n ≫
      (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U W K hK n).hom =
    (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V K hK n).hom ≫
      HomologicalComplex.homologyMap
        (sectionComplexRestrictionConeMap X K (Opens.infLELeft V U) (Opens.infLELeft W U)
          a (homOfLE (inf_le_inf_right U (leOfHom a)))) (n - 1) := by
  let S := _root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K
  let T := _root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U W K
  let hS := _root_.OAI.AlgebraicTopology.Support.FlasqueComparison.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK
  let hT := _root_.OAI.AlgebraicTopology.Support.FlasqueComparison.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U W K hK
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} ℤᵘᵖ (n - 1)
  change HomologicalComplex.homologyMap (supportRestrictionSectionsComplexMap X U K a).τ₁ n ≫
      ((_root_.OAI.Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone T hT (n - 1) n (by omega)).hom ≫
        H.map (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsConeIso X U W K).hom) =
    ((_root_.OAI.Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone S hS (n - 1) n (by omega)).hom ≫
        H.map (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsConeIso X U V K).hom) ≫ _
  rw [_root_.OAI.Algebra.Homology.DerivedCategoryConeNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone_naturality_assoc
    (supportRestrictionSectionsComplexMap X U K a) hS hT (n - 1) n (by omega)]
  simp only [Category.assoc]
  congr 1
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp, supportRestrictionSectionsConeIso_naturality]

/-- The canonical grading cone comparison is the map of its two grading isomorphisms. -/
lemma sectionComplexRestrictionExtendConeIso_hom
    (L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W : Opens X} (i : W ⟶ V) :
    (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X L i).hom =
      CochainComplex.mappingCone.map _ _
        (_root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V) L
          ComplexShape.embeddingUpNat).hom
        (_root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W) L
          ComplexShape.embeddingUpNat).hom
        (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction_extend X L i) :=
  _root_.OAI.Algebra.Homology.MappingConeMapNaturality.CochainComplex.mappingCone.mapArrowHom_eq_map _ _ _ _ _

/-- The canonical grading cone comparison respects the restriction rectangle. -/
@[reassoc]
lemma sectionComplexRestrictionExtendConeIso_naturality
    (L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W V' W' : Opens X} (i : W ⟶ V) (i' : W' ⟶ V')
    (a : V' ⟶ V) (b : W' ⟶ W) :
    sectionComplexRestrictionConeMap X (L.extend ComplexShape.embeddingUpNat) i i' a b ≫
      (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X L i').hom =
    (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X L i).hom ≫
      CochainComplex.mappingCone.map _ _
        (HomologicalComplex.extendMap (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X (.up ℕ) L a)
          ComplexShape.embeddingUpNat)
        (HomologicalComplex.extendMap (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X (.up ℕ) L b)
          ComplexShape.embeddingUpNat)
        (by rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
          sectionComplexRestriction_square X (.up ℕ) L i i' a b]) := by
  rw [sectionComplexRestrictionExtendConeIso_hom, sectionComplexRestrictionExtendConeIso_hom]
  dsimp only [sectionComplexRestrictionConeMap]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1 <;> exact _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction_extend X L _

end Sheaf
end TopCat

end

end OAI.AlgebraicTopology.Support.SectionRestrictionConeNaturality
