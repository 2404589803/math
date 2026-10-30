/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.CochainOpenSections

namespace OAI.AlgebraicTopology.Singular.SheafCochainTop

/-!
# Singular cochains compute sheafified cochains on an arbitrary open

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.CochainOpenSections`.
-/

/-! ### Constructions used only in proofs -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

section
section

variable (R : Type) [CommRing R] (X : TopCat.{0})

/-- The image of the top open of a subspace is that ambient open itself. -/
def openSubspaceImageTopIso (V : Opens X) : V.isOpenEmbedding.functor.obj ⊤ ≅ V :=
  eqToIso (Opens.isOpenEmbedding_obj_top V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be a topological space and `R` a commutative ring. For an open `V ⊆ X`,
this identifies the singular cochain presheaf on `X` evaluated at `V` with the singular cochain
presheaf on the space `V` evaluated at its whole space. Both are the complex `C^•(V;R)`,
regarded as a complex of abelian groups. -/
def openRawSingularCochainComplexIsoGlobal (V : Opens X) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularCochainComplex R X V ≅ _root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R (TopCat.of V) :=
  (NatIso.mapHomologicalComplex
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).mapIso (openSubspaceImageTopIso X V).op)
      (.up ℕ)).app (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex R X) ≪≫
    (((evaluation (Opens (TopCat.of V))ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
      (.up ℕ)).mapIso (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenRestriction.singularCochainPresheafComplexOpenRestrictionIso R X V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sections of the ambient singular sheaf on `V` identified with global
sections of its intrinsic singular sheaf, using the normalized open restriction. -/
def openSingularCochainSheafComplexIsoGlobal (V : Opens X) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openSingularCochainSheafComplex R X V ≅
      _root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R (TopCat.of V) :=
  letI : (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op V)).PreservesZeroMorphisms :=
    inferInstanceAs ((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).PreservesZeroMorphisms)
  letI : (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj
        (.op (V.isOpenEmbedding.functor.obj ⊤))).PreservesZeroMorphisms :=
    inferInstanceAs ((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X
      (V.isOpenEmbedding.functor.obj ⊤)).PreservesZeroMorphisms)
  (NatIso.mapHomologicalComplex
    (Functor.isoWhiskerLeft (TopCat.Sheaf.forget AddCommGrpCat X)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).mapIso (openSubspaceImageTopIso X V).op))
      (.up ℕ)).app (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R X) ≪≫
    ((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of V) ⊤).mapHomologicalComplex (.up ℕ)).mapIso
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenRestriction.singularCochainSheafComplexOpenRestrictionIso R X V)

end
end

end

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

section
section

variable (R : Type) [CommRing R] (X : TopCat.{0})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic/global comparison retains the sheafification unit. -/
@[reassoc]
lemma openRawToSingularCochainSheafComplex_global (V : Opens X) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawToSingularCochainSheafComplex R X V ≫
      (openSingularCochainSheafComplexIsoGlobal R X V).hom =
    (openRawSingularCochainComplexIsoGlobal R X V).hom ≫
      _root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R (TopCat.of V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (toSheafify (Opens.grothendieckTopology X) (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n)).app
      (.op V) ≫
      ((_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R X n).obj.map (openSubspaceImageTopIso X V).hom.op ≫
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenRestriction.singularCochainSheafOpenRestrictionIso R X V n).hom.hom.app (.op ⊤)) =
    ((_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n).map (openSubspaceImageTopIso X V).hom.op ≫
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenRestriction.singularCochainPresheafOpenRestrictionIso R X V n).hom.app (.op ⊤)) ≫ _
  calc
    _ = (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n).map (openSubspaceImageTopIso X V).hom.op ≫
        (toSheafify (Opens.grothendieckTopology X)
          (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n)).app
            (.op (V.isOpenEmbedding.functor.obj ⊤)) ≫
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenRestriction.singularCochainSheafOpenRestrictionIso R X V n).hom.hom.app (.op ⊤) :=
      ((toSheafify (Opens.grothendieckTopology X)
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n)).naturality_assoc
          (openSubspaceImageTopIso X V).hom.op _).symm
    _ = _ := by
      rw [Category.assoc, _root_.OAI.AlgebraicTopology.Singular.GlobalRestriction.topOpenToGlobalSingularCochainSheafComplex_f]
      exact congrArg
        (fun f => (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n).map
          (openSubspaceImageTopIso X V).hom.op ≫ f.app (.op ⊤))
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenRestriction.toSheafify_singularCochainSheafOpenRestrictionIso R X V n)

/-- On any paracompact Hausdorff ambient open, raw rational singular cochains map
quasi-isomorphically to sections of the singular sheaf. The hypothesis is on that open alone. -/
theorem openRawToSingularCochainSheafComplex_quasiIso (V : Opens X)
    [ParacompactSpace V] [T2Space V] :
    QuasiIso (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawToSingularCochainSheafComplex ℚ X V) := by
  have := _root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex_quasiIso (Y := TopCat.of V)
  have : QuasiIso
      ((openRawSingularCochainComplexIsoGlobal ℚ X V).hom ≫
        _root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℚ (TopCat.of V)) := inferInstance
  rw [← openRawToSingularCochainSheafComplex_global] at this
  exact (quasiIso_iff_comp_right _ _).mp this

/-- The open-section comparisons commute with the restriction maps.
In particular this applies to `W = V ⊓ U`. -/
@[reassoc]
lemma openSingularSheafRestriction_naturality {V W : Opens X} (i : W ⟶ V) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawToSingularCochainSheafComplex R X V ≫ _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openSingularSheafRestriction R X i =
      _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularRestriction R X i ≫ _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawToSingularCochainSheafComplex R X W := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ((toSheafify (Opens.grothendieckTopology X)
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n)).naturality i.op).symm

end
end

end

end OAI.AlgebraicTopology.Singular.SheafCochainTop
