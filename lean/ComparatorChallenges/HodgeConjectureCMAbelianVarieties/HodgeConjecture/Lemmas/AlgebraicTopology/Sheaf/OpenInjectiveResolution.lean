/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenInjectiveResolution
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueExtendNat

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicTopology.Sheaf.OpenInjectiveTo

open _root_.CochainComplex
open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Comparing an ambient resolution with a resolution on an open subspace

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenInjectiveResolution`.
-/

/-! ### Constructions used only in proofs -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

section
namespace TopCat
open _root_.TopCat

variable (X : TopCat.{0}) (U : Opens X) (A : AddCommGrpCat.{0})

/-- Let `U` be open in a topological space `X`, and let `A` be an abelian group. For the chosen
injective resolution `I` of the constant sheaf `A_X`, this is the nonnegative cochain complex
`I|_U`, obtained by restricting each sheaf and differential to `U`. -/
def restrictedAmbientConstantResolution :
    CochainComplex (Sheaf AddCommGrpCat.{0} (TopCat.of U)) ℕ :=
  ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
    (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).cocomplex

/-- Let `U` be open in a topological space `X`, and let `A` be an abelian group. For the chosen
injective resolution `I` of the constant sheaf `A_X`, this augmentation `A_U[0] → I|_U`
restricts the augmentation of `I` and identifies `A_X|_U` with `A_U`. -/
def restrictedAmbientConstantAugmentation :
    (CochainComplex.single₀ (Sheaf AddCommGrpCat.{0} (TopCat.of U))).obj
        𝓒[↧U; A] ⟶
      restrictedAmbientConstantResolution X U A :=
  (CochainComplex.single₀ _).map (_root_.OAI.AlgebraicTopology.Sheaf.OpenRestriction.TopCat.constantOpenSheafRestrictionIso X U A).hom ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat) (.up ℕ) 0).inv.app _ ≫
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
      (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).ι

set_option backward.isDefEq.respectTransparency false in
instance restrictedAmbientConstantAugmentation_mono :
    Mono (restrictedAmbientConstantAugmentation X U A) := by
  let : Mono (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).ι :=
    HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)
  dsimp only [restrictedAmbientConstantAugmentation]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance restrictedAmbientConstantAugmentation_quasiIso :
    QuasiIso (restrictedAmbientConstantAugmentation X U A) := by
  let : QuasiIso (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).ι :=
    (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).quasiIso
  have : QuasiIso
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
        (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).ι) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  dsimp only [restrictedAmbientConstantAugmentation]
  infer_instance

/-- Let `U` be open in a topological space `X`, and let `A` be an abelian group. For the chosen
injective resolutions `I,J` of the constant sheaves `A_X,A_U`, this cochain map `I|_U → J`
extends the identity on `A_U`: composing with the restricted augmentation gives the augmentation
of `J`. -/
def restrictedAmbientToOpenResolution :
    restrictedAmbientConstantResolution X U A ⟶
      (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).cocomplex :=
  _root_.OAI.Algebra.Homology.LiftToInjective.CochainComplex.liftToInjectiveNat (restrictedAmbientConstantAugmentation X U A)
    (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).ι
      (fun n => (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).injective n)

instance restrictedAmbientConstantResolution_isFlasque (n : ℕ) :
    ((restrictedAmbientConstantResolution X U A).X n).IsFlasque := by
  change ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
    ((_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).cocomplex.X n)).IsFlasque
  let : IsFlasque ((_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).cocomplex.X n) :=
    @_root_.OAI.AlgebraicTopology.Sheaf.InjectiveFlasque.TopCat.injective_isFlasque _ _ ((_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).injective n)
  exact _root_.OAI.AlgebraicTopology.Sheaf.OpenRestriction.TopCat.openSheafRestriction_isFlasque X U _

/-- Let `U` be open in a topological space `X`, with inclusion `j`, and let `A` be an abelian group.
For the chosen injective resolution `I` of `A_X`, this cochain map `I → j_*(I|_U)` restricts
sections to `U`. In degree `q`, on an open `V`, it is `I^q(V) → I^q(V ∩ U)`. -/
def ambientInjectiveRestriction :
    (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).cocomplex ⟶
      ((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).obj
        (restrictedAmbientConstantResolution X U A) where
  f n := (_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app
    ((_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).cocomplex.X n)
  comm' i j _h := ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).naturality
    ((_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).cocomplex.d i j)).symm

/-- Let `U` be open in a topological space `X`, with inclusion `j`, and let `A` be an abelian group.
For the chosen injective resolutions `I,J` of the constant sheaves `A_X,A_U`, this map `I →
j_*J` composes restriction with the direct image of the comparison `I|_U → J` extending the
identity on `A_U`. -/
def ambientToOpenInjectiveResolution :
    (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).cocomplex ⟶
      ((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).obj
        (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).cocomplex :=
  ambientInjectiveRestriction X U A ≫
    ((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).map
      (restrictedAmbientToOpenResolution X U A)

/-- Let `U` be open in a topological space `X`, with inclusion `j`, and let `A` be an abelian group.
For the chosen injective resolutions `I,J` of the constant sheaves `A_X,A_U`, this map
`Γ(U,I|_U) → Γ(U,J)` takes sections of the comparison extending the identity on `A_U`. Both
sides are expressed as global sections of direct images under `j`. -/
def globalRestrictedAmbientToOpenResolution :
    ((_root_.OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
      (.up ℕ)).obj
        (((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).obj
          (restrictedAmbientConstantResolution X U A)) ⟶
    ((_root_.OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
      (.up ℕ)).obj
        (((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).obj
          (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).cocomplex) :=
  ((_root_.OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
    (.up ℕ)).map
      (((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).map
        (restrictedAmbientToOpenResolution X U A))

end TopCat
end

end

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

namespace CochainComplex
open _root_.CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

variable {A K I : CochainComplex C ℕ} (a : A ⟶ K) [Mono a] [QuasiIso a]
  (r : A ⟶ I) (hI : ∀ n, Injective (I.X n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma comp_liftToInjectiveNat : a ≫ _root_.OAI.Algebra.Homology.LiftToInjective.CochainComplex.liftToInjectiveNat a r hI = r := by
  let := _root_.OAI.Algebra.Homology.LiftToInjective.CochainComplex.mono_extendMap_nat a
  apply (ComplexShape.embeddingUpNat.extendFunctor C).map_injective
  rw [Functor.map_comp]
  dsimp only [_root_.OAI.Algebra.Homology.LiftToInjective.CochainComplex.liftToInjectiveNat]
  rw [Functor.map_preimage]
  exact _root_.OAI.Algebra.Homology.LiftToInjective.CochainComplex.comp_liftToInjective
    (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap r ComplexShape.embeddingUpNat)
    (_root_.OAI.Algebra.Homology.LiftToInjective.CochainComplex.injective_extend_nat I hI)

lemma liftToInjectiveNat_quasiIso [QuasiIso r] : QuasiIso (_root_.OAI.Algebra.Homology.LiftToInjective.CochainComplex.liftToInjectiveNat a r hI) := by
  have : QuasiIso (a ≫ _root_.OAI.Algebra.Homology.LiftToInjective.CochainComplex.liftToInjectiveNat a r hI) := by
    rw [comp_liftToInjectiveNat]
    infer_instance
  exact quasiIso_of_comp_left a _

end CochainComplex

section
namespace TopCat
open _root_.TopCat

variable (X : TopCat.{0}) (U : Opens X) (A : AddCommGrpCat.{0})

@[reassoc (attr := simp)]
lemma restrictedAmbientAugmentation_comp_comparison :
    restrictedAmbientConstantAugmentation X U A ≫
      restrictedAmbientToOpenResolution X U A = (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).ι :=
  _root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveTo.CochainComplex.comp_liftToInjectiveNat _ _ _

lemma restrictedAmbientToOpenResolution_quasiIso :
    QuasiIso (restrictedAmbientToOpenResolution X U A) := by
  let : QuasiIso (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).ι :=
    (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).quasiIso
  exact _root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveTo.CochainComplex.liftToInjectiveNat_quasiIso _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Strict normalization: the independently resolved restriction extends
the restriction map of constant sheaves. -/
@[reassoc]
lemma ambientAugmentation_comp_openResolution :
    (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).ι ≫ ambientToOpenInjectiveResolution X U A =
      (CochainComplex.single₀ _).map (_root_.OAI.AlgebraicTopology.Support.SheafCohomology.TopCat.Sheaf.constantRestriction U.inclusion' A) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (pushforward AddCommGrpCat U.inclusion') (.up ℕ) 0).inv.app _ ≫
        ((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).map
          (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).ι := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).ι.f 0 ≫
        ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app _ ≫
          (pushforward AddCommGrpCat U.inclusion').map
            ((restrictedAmbientToOpenResolution X U A).f 0)) =
      _root_.OAI.AlgebraicTopology.Support.SheafCohomology.TopCat.Sheaf.constantRestriction U.inclusion' A ≫
        (pushforward AddCommGrpCat U.inclusion').map
          ((_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).ι.f 0)
    have hnat := (_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).naturality
      ((_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).ι.f 0)
    dsimp only [Functor.id_map] at hnat
    rw [← Category.assoc, hnat]
    change ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app 𝓒[X; A] ≫ _) ≫ _ = _
    rw [← _root_.OAI.AlgebraicTopology.Sheaf.OpenRestriction.TopCat.constantRestriction_pushforward_constantToOpen]
    dsimp only [_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.openRestrictionPushforward, Functor.comp_map]
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← Functor.map_comp]
    have h := HomologicalComplex.congr_hom
      (restrictedAmbientAugmentation_comp_comparison X U A) 0
    change (_root_.OAI.AlgebraicTopology.Sheaf.OpenRestriction.TopCat.constantOpenSheafRestrictionIso X U A).hom ≫
        (U.isOpenEmbedding.sheafPullback AddCommGrpCat).map
          ((_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution X A).ι.f 0) ≫
        (restrictedAmbientToOpenResolution X U A).f 0 =
      (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).ι.f 0 at h
    dsimp only [_root_.OAI.AlgebraicTopology.Sheaf.OpenRestriction.TopCat.constantOpenSheafRestrictionIso] at h
    exact congrArg (fun f => _root_.OAI.AlgebraicTopology.Support.SheafCohomology.TopCat.Sheaf.constantRestriction U.inclusion' A ≫
      (pushforward AddCommGrpCat U.inclusion').map f) h
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 _ (n + 1) (by omega)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- The comparison remains a quasi-isomorphism after global sections, because on the open
subspace both resolutions are termwise flasque. -/
theorem globalRestrictedAmbientToOpenResolution_quasiIso :
    QuasiIso (globalRestrictedAmbientToOpenResolution X U A) := by
  change QuasiIso
    (((_root_.OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor (TopCat.of U)).mapHomologicalComplex
      (.up ℕ)).map (restrictedAmbientToOpenResolution X U A))
  let : QuasiIso (restrictedAmbientToOpenResolution X U A) :=
    restrictedAmbientToOpenResolution_quasiIso X U A
  apply _root_.OAI.AlgebraicTopology.Sheaf.FlasqueExtendNat.TopCat.globalSectionsNat_map_quasiIso
  · exact restrictedAmbientConstantResolution_isFlasque X U A
  · exact fun n => @_root_.OAI.AlgebraicTopology.Sheaf.InjectiveFlasque.TopCat.injective_isFlasque _ _ ((_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution (TopCat.of U) A).injective n)

end TopCat
end

end

end OAI.AlgebraicTopology.Sheaf.OpenInjectiveTo
