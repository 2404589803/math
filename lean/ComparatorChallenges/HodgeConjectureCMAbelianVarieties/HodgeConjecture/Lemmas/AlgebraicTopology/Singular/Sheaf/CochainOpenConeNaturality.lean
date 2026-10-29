/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.CochainOpenCone
import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingConeMapNaturality

namespace OAI.AlgebraicTopology.Singular.CochainOpenConeNaturality

/-! # Local restriction-cone naturality -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

section
section

variable (R : Type) [CommRing R] (X : TopCat.{0})
  {V W V' W' : Opens X} (i : W ⟶ V) (i' : W' ⟶ V') (a : V' ⟶ V) (b : W' ⟶ W)

/-- Let `X` be a topological space and `W ⊆ V`, `W′ ⊆ V′` open subsets, with `V′ ⊆ V` and `W′ ⊆ W`.
This map of topological pairs `(V′,W′) → (V,W)` is given by the two inclusions. -/
def openInclusionPairMap : _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i' ⟶ _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i :=
  TopPair.ofHom ((Opens.toTopCat X).map a) ((Opens.toTopCat X).map b) (by ext x; rfl)

/-- Restriction of raw cochains around an open-inclusion square. -/
lemma openRawSingularRestriction_square :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularRestriction R X i ≫ _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularRestriction R X b =
      _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularRestriction R X a ≫ _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularRestriction R X i' := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n).map i.op ≫
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n).map b.op =
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n).map a.op ≫
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n).map i'.op
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Sheaf-section restriction around the same square. -/
lemma openSingularSheafRestriction_square :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openSingularSheafRestriction R X i ≫ _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openSingularSheafRestriction R X b =
      _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openSingularSheafRestriction R X a ≫ _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openSingularSheafRestriction R X i' := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R X n).obj.map i.op ≫
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R X n).obj.map b.op =
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R X n).obj.map a.op ≫
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R X n).obj.map i'.op
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Let `X` be a topological space and `W ⊆ V`, `W′ ⊆ V′` open subsets, with `V′ ⊆ V` and `W′ ⊆ W`.
For a commutative ring `R`, restriction of singular cochains induces this map `Cone(C^•(V;R) →
C^•(W;R)) → Cone(C^•(V′;R) → C^•(W′;R))`, with all complexes extended by zero to negative
degrees and regarded as complexes of abelian groups. -/
def openRawSingularRestrictionConeMap :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionCone R X i ⟶ _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionCone R X i' :=
  CochainComplex.mappingCone.map _ _
    (HomologicalComplex.extendMap (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularRestriction R X a) ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularRestriction R X b) ComplexShape.embeddingUpNat)
    (by rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
      openRawSingularRestriction_square R X i i' a b])

/-- Let `X` be a topological space and `W ⊆ V`, `W′ ⊆ V′` open subsets, with `V′ ⊆ V` and `W′ ⊆ W`.
Let `C` be the complex of sheafified singular cochains with coefficients in a commutative ring
`R`. Restriction of sections gives this map `Cone(C(V) → C(W)) → Cone(C(V′) → C(W′))`, after
extension by zero to negative degrees. -/
def openSingularSheafRestrictionConeMap :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openSingularSheafRestrictionCone R X i ⟶ _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openSingularSheafRestrictionCone R X i' :=
  CochainComplex.mappingCone.map _ _
    (HomologicalComplex.extendMap (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openSingularSheafRestriction R X a) ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenSections.openSingularSheafRestriction R X b) ComplexShape.embeddingUpNat)
    (by rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
      openSingularSheafRestriction_square R X i i' a b])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The local cone sheafification map is natural in the ambient open. -/
@[reassoc]
lemma openRawToSingularSheafRestrictionCone_naturality :
    openRawSingularRestrictionConeMap R X i i' a b ≫
      _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawToSingularSheafRestrictionCone R X i' =
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawToSingularSheafRestrictionCone R X i ≫
      openSingularSheafRestrictionConeMap R X i i' a b := by
  dsimp only [openRawSingularRestrictionConeMap, openSingularSheafRestrictionConeMap,
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawToSingularSheafRestrictionCone]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1 <;> rw [← HomologicalComplex.extendMap_comp,
    ← HomologicalComplex.extendMap_comp, _root_.OAI.AlgebraicTopology.Singular.SheafCochainTop.openSingularSheafRestriction_naturality]

/-- The open raw-cone identification is exactly the standard cone map
with its prescribed two components. -/
lemma openRawSingularRestrictionConeIsoRelative_hom :
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative R X i).hom =
    CochainComplex.mappingCone.map _ _
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual R X V).hom
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual R X W).hom
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionInt_transport R X i) :=
  _root_.OAI.Algebra.Homology.MappingConeMapNaturality.CochainComplex.mappingCone.mapArrowHom_eq_map _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `R` be a commutative ring and `f : (X,A) → (Y,B)` a map of topological pairs. Pullback
induces this map of abelian-group complexes `Cone(C^•(Y;R) → C^•(B;R)) → Cone(C^•(X;R) →
C^•(A;R))`. The singular cochain complexes are extended by zero to negative degrees and their
scalar structure is forgotten before taking cones. -/
def forgottenRelativeCochainConeMap {P Q : TopPair.{0}} (f : P ⟶ Q) :
    CochainComplex.mappingCone
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).map
          (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R Q)) ⟶
      CochainComplex.mappingCone
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).map
          (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R P)) :=
  CochainComplex.mappingCone.map _ _
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).map
      (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainIntMap.relativeDualCochainShortComplexIntMap R f).τ₂)
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).map
      (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainIntMap.relativeDualCochainShortComplexIntMap R f).τ₃)
    (by rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).map
          (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainIntMap.relativeDualCochainShortComplexIntMap R f).comm₂₃.symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The open raw-cone comparison preserves maps of open pairs. -/
@[reassoc]
lemma openRawSingularRestrictionConeIsoRelative_naturality :
    openRawSingularRestrictionConeMap R X i i' a b ≫
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative R X i').hom =
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative R X i).hom ≫
      forgottenRelativeCochainConeMap R (openInclusionPairMap X i i' a b) := by
  rw [openRawSingularRestrictionConeIsoRelative_hom,
    openRawSingularRestrictionConeIsoRelative_hom]
  dsimp only [openRawSingularRestrictionConeMap, forgottenRelativeCochainConeMap]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1
  · exact _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionInt_transport R X a
  · exact _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionInt_transport R X b

/-- The raw local cone identified with the forgotten relative cone,
including the canonical comparison for forgetting scalars. -/
def openRawSingularRestrictionConeIsoForgottenRelative :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionCone R X i ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).obj
        (CochainComplex.mappingCone (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i))) :=
  _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative R X i ≪≫
    (CochainComplex.mappingCone.mapHomologicalComplexIso
      (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i))
      (forget₂ (ModuleCat R) AddCommGrpCat)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the complete chain-level open raw-cone comparison. -/
@[reassoc]
lemma openRawSingularRestrictionConeIsoForgottenRelative_naturality :
    openRawSingularRestrictionConeMap R X i i' a b ≫
      (openRawSingularRestrictionConeIsoForgottenRelative R X i').hom =
    (openRawSingularRestrictionConeIsoForgottenRelative R X i).hom ≫
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).map
        (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainIntMap.relativeCochainConeMap R (openInclusionPairMap X i i' a b)) := by
  dsimp only [openRawSingularRestrictionConeIsoForgottenRelative, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, openRawSingularRestrictionConeIsoRelative_naturality, Category.assoc,
    Category.assoc]
  apply (cancel_mono (CochainComplex.mappingCone.mapHomologicalComplexIso
    (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i'))
    (forget₂ (ModuleCat R) AddCommGrpCat)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [_root_.OAI.AlgebraicTopology.Singular.RelativeCochainIntMap.relativeCochainConeMap]
  rw [_root_.OAI.Algebra.Homology.MappingConeMapNaturality.CochainComplex.mappingCone.mapHomologicalComplexIso_naturality,
    Iso.inv_hom_id_assoc]
  rfl

/-- Let `W ⊆ V` be open subsets of a topological space `X`, and let `R` be a commutative ring. This
identifies degree-`n` cohomology of the cone of raw cochain restriction from `V` to `W` with the
underlying additive group of `H^n(Cone(C^•(V;R) → C^•(W;R)))` formed in `R`-modules. It combines
the identification of open-subspace cochains with the fact that forgetting scalars commutes with
cohomology. -/
def openRawSingularRestrictionConeHomologyIso (n : ℤ) :
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionCone R X i).homology n ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((CochainComplex.mappingCone
          (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i))).homology n) :=
  HomologicalComplex.homologyMapIso
    (openRawSingularRestrictionConeIsoForgottenRelative R X i) n ≪≫
      ShortComplex.mapHomologyIso
        ((CochainComplex.mappingCone
          (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i))).sc n)
        (forget₂ (ModuleCat R) AddCommGrpCat)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The complete raw-cone homology comparison preserves restrictions. -/
@[reassoc]
lemma openRawSingularRestrictionConeHomologyIso_naturality (n : ℤ) :
    HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap R X i i' a b) n ≫
      (openRawSingularRestrictionConeHomologyIso R X i' n).hom =
    (openRawSingularRestrictionConeHomologyIso R X i n).hom ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        (HomologicalComplex.homologyMap
          (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainIntMap.relativeCochainConeMap R (openInclusionPairMap X i i' a b)) n) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ n
  change H.map (openRawSingularRestrictionConeMap R X i i' a b) ≫
      (H.map (openRawSingularRestrictionConeIsoForgottenRelative R X i').hom ≫ _) =
    (H.map (openRawSingularRestrictionConeIsoForgottenRelative R X i).hom ≫ _) ≫ _
  rw [← Category.assoc, ← H.map_comp,
    openRawSingularRestrictionConeIsoForgottenRelative_naturality, H.map_comp,
    Category.assoc, Category.assoc]
  exact congrArg (fun f => H.map
    (openRawSingularRestrictionConeIsoForgottenRelative R X i).hom ≫ f)
    (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) ℤᵘᵖ n).map
        (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainIntMap.relativeCochainConeMap R (openInclusionPairMap X i i' a b)))
      (forget₂ (ModuleCat R) AddCommGrpCat))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The open-cone equivalence factors through this canonical homology comparison and the natural
relative evaluation pairing. -/
lemma openRawSingularRestrictionConeCohomologyEquivRelative_eq (n : ℕ)
    (z : (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionCone R X i).homology ((n : ℤ) - 1)) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeCohomologyEquivRelative R X i n z =
      _root_.OAI.AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeCochainConeCohomologyEquivCanonical R (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i) n
        ((openRawSingularRestrictionConeHomologyIso R X i ((n : ℤ) - 1)).hom z) := by
  let eA := _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative R X i
  let eB := CochainComplex.mappingCone.mapHomologicalComplexIso
    (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i))
    (forget₂ (ModuleCat R) AddCommGrpCat)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ ((n : ℤ) - 1)
  change _root_.OAI.AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeCochainConeCohomologyEquivCanonical R (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i) n
    ((ShortComplex.mapHomologyIso _ (forget₂ (ModuleCat R) AddCommGrpCat)).hom
      (H.map eB.inv (H.map eA.hom z))) =
    _root_.OAI.AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeCochainConeCohomologyEquivCanonical R (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair X i) n
      ((ShortComplex.mapHomologyIso _ (forget₂ (ModuleCat R) AddCommGrpCat)).hom
        (H.map (eA.hom ≫ eB.inv) z))
  rw [H.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Exact relative-cohomology naturality of the local raw-cone
comparison, including all grading and scalar-forgetting identifications. -/
lemma openRawSingularRestrictionConeCohomologyEquivRelative_naturality (n : ℕ)
    (z : (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionCone R X i).homology ((n : ℤ) - 1)) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeCohomologyEquivRelative R X i' n
        (HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap R X i i' a b)
          ((n : ℤ) - 1) z) =
      _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap R n (openInclusionPairMap X i i' a b)
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeCohomologyEquivRelative R X i n z) := by
  rw [openRawSingularRestrictionConeCohomologyEquivRelative_eq,
    openRawSingularRestrictionConeCohomologyEquivRelative_eq]
  have h := ConcreteCategory.congr_hom
    (openRawSingularRestrictionConeHomologyIso_naturality R X i i' a b ((n : ℤ) - 1)) z
  change (openRawSingularRestrictionConeHomologyIso R X i' ((n : ℤ) - 1)).hom
      (HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap R X i i' a b)
        ((n : ℤ) - 1) z) =
    HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainIntMap.relativeCochainConeMap R (openInclusionPairMap X i i' a b))
      ((n : ℤ) - 1) ((openRawSingularRestrictionConeHomologyIso R X i ((n : ℤ) - 1)).hom z) at h
  rw [h]
  exact _root_.OAI.AlgebraicTopology.Singular.RelativeCochainIntMap.relativeCochainConeCohomologyEquivCanonical_naturality _ _ _ _

/-- Let `W ⊆ V` be open subsets of a topological space `X`, each Hausdorff and paracompact. Write
`C` for the sheafified rational singular cochain complex. Sheafification induces this
isomorphism `H^n(Cone(C^•(V;ℚ) → C^•(W;ℚ))) ≅ H^n(Cone(C(V) → C(W)))` in every integer degree,
comparing raw cochains with sections of the cochain sheaves. -/
def openRawToSingularSheafRestrictionConeHomologyIso
    [ParacompactSpace V] [T2Space V] [ParacompactSpace W] [T2Space W] (n : ℤ) :
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionCone ℚ X i).homology n ≅
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openSingularSheafRestrictionCone ℚ X i).homology n :=
  letI := _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawToSingularSheafRestrictionCone_quasiIso X i
  asIso (HomologicalComplex.homologyMap (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawToSingularSheafRestrictionCone ℚ X i) n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Inverting the sheafification quasi-isomorphism preserves the
local restriction square. -/
@[reassoc]
lemma openRawToSingularSheafRestrictionConeHomologyIso_inv_naturality
    [ParacompactSpace V] [T2Space V] [ParacompactSpace W] [T2Space W]
    [ParacompactSpace V'] [T2Space V'] [ParacompactSpace W'] [T2Space W'] (n : ℤ) :
    HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b) n ≫
      (openRawToSingularSheafRestrictionConeHomologyIso X i' n).inv =
    (openRawToSingularSheafRestrictionConeHomologyIso X i n).inv ≫
      HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap ℚ X i i' a b) n := by
  have h := congrArg (HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ n).map
    (openRawToSingularSheafRestrictionCone_naturality ℚ X i i' a b)
  rw [Functor.map_comp, Functor.map_comp] at h
  change HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap ℚ X i i' a b) n ≫
      (openRawToSingularSheafRestrictionConeHomologyIso X i' n).hom =
    (openRawToSingularSheafRestrictionConeHomologyIso X i n).hom ≫
      HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b) n at h
  apply (cancel_mono (openRawToSingularSheafRestrictionConeHomologyIso X i' n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The complete local sheaf-section cone comparison intertwines
ambient-open restriction with the relative-cohomology pullback. -/
lemma openSingularSheafRestrictionConeCohomologyEquivRelative_naturality
    [ParacompactSpace V] [T2Space V] [ParacompactSpace W] [T2Space W]
    [ParacompactSpace V'] [T2Space V'] [ParacompactSpace W'] [T2Space W'] (n : ℕ)
    (z : (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openSingularSheafRestrictionCone ℚ X i).homology ((n : ℤ) - 1)) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openSingularSheafRestrictionConeCohomologyEquivRelative X i' n
        (HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b)
          ((n : ℤ) - 1) z) =
      _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n (openInclusionPairMap X i i' a b)
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openSingularSheafRestrictionConeCohomologyEquivRelative X i n z) := by
  change _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i' n
      ((openRawToSingularSheafRestrictionConeHomologyIso X i' ((n : ℤ) - 1)).inv
        (HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b)
          ((n : ℤ) - 1) z)) =
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n (openInclusionPairMap X i i' a b)
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i n
        ((openRawToSingularSheafRestrictionConeHomologyIso X i ((n : ℤ) - 1)).inv z))
  have h := ConcreteCategory.congr_hom
    (openRawToSingularSheafRestrictionConeHomologyIso_inv_naturality X i i' a b
      ((n : ℤ) - 1)) z
  change (openRawToSingularSheafRestrictionConeHomologyIso X i' ((n : ℤ) - 1)).inv
      (HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b)
        ((n : ℤ) - 1) z) =
    HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap ℚ X i i' a b)
      ((n : ℤ) - 1) ((openRawToSingularSheafRestrictionConeHomologyIso X i ((n : ℤ) - 1)).inv z) at h
  rw [h]
  exact openRawSingularRestrictionConeCohomologyEquivRelative_naturality _ _ _ _ _ _ _ _

end
end

end

end OAI.AlgebraicTopology.Singular.CochainOpenConeNaturality
