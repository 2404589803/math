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

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainResolution

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicTopology.Singular.SheafCochainRestriction

open _root_.AlgebraicTopology

/-!
# Restriction of singular cochains through direct image

For an open embedding `j : U → X`, restriction of singular cochains from `X` to `U` is a map of
cochain complexes of sheaves `C^•_X → j_* C^•_U`, natural with respect to sheafification.
-/

noncomputable section

open _root_.CategoryTheory Filter _root_.TopologicalSpace

universe u

section
section

variable (R : Type u) [CommRing R] {U X : TopCat.{u}} (j : U ⟶ X)

def preimageOpenToOpen (V : Opens X) :
    (Opens.toTopCat U).obj ((Opens.map j).obj V) ⟶ (Opens.toTopCat X).obj V :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨j x.1, x.2⟩,
      Continuous.subtype_mk (j.hom.continuous.comp continuous_subtype_val) _⟩

noncomputable def preimageOpenChainMap (V : Opens X) :
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.openSingularChainComplexFunctor R U).obj ((Opens.map j).obj V) ⟶
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.openSingularChainComplexFunctor R X).obj V :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).map (preimageOpenToOpen j V)

lemma preimageOpenChainMap_naturality {V W : Opens X} (i : V ⟶ W) :
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.openSingularChainComplexFunctor R U).map ((Opens.map j).map i) ≫
        preimageOpenChainMap R j W =
      preimageOpenChainMap R j V ≫ (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.openSingularChainComplexFunctor R X).map i := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)
  change F.map ((Opens.toTopCat U).map ((Opens.map j).map i)) ≫
      F.map (preimageOpenToOpen j W) =
    F.map (preimageOpenToOpen j V) ≫ F.map ((Opens.toTopCat X).map i)
  rw [← F.map_comp, ← F.map_comp]
  congr 1

noncomputable def singularRestrictionToRawPushforward (n : ℕ) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n ⟶
      (Opens.map j).op ⋙ _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R U n where
  app V := AddCommGrpCat.ofHom
    ((preimageOpenChainMap R j V.unop).f n).hom.dualMap.toAddMonoidHom
  naturality {V W} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change _root_.OAI.AlgebraicTopology.Singular.SheafCochain.OpenCochains R X V n at φ
    apply LinearMap.ext
    intro c
    change φ
        (((((_root_.OAI.AlgebraicTopology.Singular.SheafCochain.openSingularChainComplexFunctor R X).map i.unop).f n).hom)
          (((preimageOpenChainMap R j W.unop).f n).hom c)) =
      φ
        ((((preimageOpenChainMap R j V.unop).f n).hom)
          ((((_root_.OAI.AlgebraicTopology.Singular.SheafCochain.openSingularChainComplexFunctor R U).map
            ((Opens.map j).map i.unop)).f n).hom c))
    exact congrArg φ (ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f n) (preimageOpenChainMap_naturality R j i.unop)).symm c)

noncomputable def singularRestrictionPresheaf (n : ℕ) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R U n)).obj :=
  singularRestrictionToRawPushforward R j n ≫
    Functor.whiskerLeft (Opens.map j).op
      (toSheafify (Opens.grothendieckTopology U) (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R U n))

noncomputable def singularRestrictionSheaf (n : ℕ) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R X n ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat j).obj
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R U n) :=
  ⟨sheafifyLift (Opens.grothendieckTopology X)
    (singularRestrictionPresheaf R j n)
    ((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R U n)).property⟩

lemma toSheafify_comp_singularRestrictionSheaf (n : ℕ) :
    toSheafify (Opens.grothendieckTopology X)
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n) ≫
      (singularRestrictionSheaf R j n).hom =
        singularRestrictionPresheaf R j n :=
  toSheafify_sheafifyLift (J := Opens.grothendieckTopology X)
    (singularRestrictionPresheaf R j n)
    (((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R U n)).property)

lemma singularRestrictionToRawPushforward_coboundary (n : ℕ) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R X n ≫ singularRestrictionToRawPushforward R j (n + 1) =
      singularRestrictionToRawPushforward R j n ≫
        Functor.whiskerLeft (Opens.map j).op (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R U n) := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change _root_.OAI.AlgebraicTopology.Singular.SheafCochain.OpenCochains R X V n at φ
  apply LinearMap.ext
  intro c
  exact congrArg φ (ConcreteCategory.congr_hom
    ((preimageOpenChainMap R j V.unop).comm (n + 1) n) c)

set_option backward.isDefEq.respectTransparency false in
lemma singularRestrictionPresheaf_coboundary (n : ℕ) :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R X n ≫ singularRestrictionPresheaf R j (n + 1) =
      singularRestrictionPresheaf R j n ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
          (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafCoboundary R U n)).hom := by
  change _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R X n ≫
        singularRestrictionToRawPushforward R j (n + 1) ≫
          Functor.whiskerLeft (Opens.map j).op
            (toSheafify (Opens.grothendieckTopology U)
              (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R U (n + 1))) =
    singularRestrictionToRawPushforward R j n ≫
      Functor.whiskerLeft (Opens.map j).op
        (toSheafify (Opens.grothendieckTopology U)
          (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R U n)) ≫
      Functor.whiskerLeft (Opens.map j).op
        ((_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafCoboundary R U n).hom)
  calc
    _ = (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R X n ≫
          singularRestrictionToRawPushforward R j (n + 1)) ≫
        Functor.whiskerLeft (Opens.map j).op
          (toSheafify (Opens.grothendieckTopology U)
            (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R U (n + 1))) := (Category.assoc _ _ _).symm
    _ = (singularRestrictionToRawPushforward R j n ≫
          Functor.whiskerLeft (Opens.map j).op
            (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R U n)) ≫
        Functor.whiskerLeft (Opens.map j).op
          (toSheafify (Opens.grothendieckTopology U)
            (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R U (n + 1))) := by
      rw [singularRestrictionToRawPushforward_coboundary]
    _ = singularRestrictionToRawPushforward R j n ≫
        Functor.whiskerLeft (Opens.map j).op
          (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R U n ≫
            toSheafify (Opens.grothendieckTopology U)
              (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R U (n + 1))) := by
      rw [Category.assoc, Functor.whiskerLeft_comp]
    _ = singularRestrictionToRawPushforward R j n ≫
        Functor.whiskerLeft (Opens.map j).op
          (toSheafify (Opens.grothendieckTopology U)
            (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R U n) ≫
              (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafCoboundary R U n).hom) := by
      rw [toSheafify_naturality]
      rfl
    _ = _ := by
      rw [Functor.whiskerLeft_comp]

noncomputable def singularRestrictionSheafComplex :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R X ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R U) where
  f n := singularRestrictionSheaf R j n
  comm' i k hik := by
    obtain rfl := hik
    rw [_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex_d, Functor.mapHomologicalComplex_obj_d,
      _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex_d]
    apply Sheaf.hom_ext
    let η := _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R X i ≫
      singularRestrictionPresheaf R j (i + 1)
    apply (sheafifyLift_unique (J := Opens.grothendieckTopology X) η
      (((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R U (i + 1))).property) _ ?_).trans
    · apply (sheafifyLift_unique (J := Opens.grothendieckTopology X) η
        (((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
          (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R U (i + 1))).property) _ ?_).symm
      unfold η
      change toSheafify (Opens.grothendieckTopology X)
          (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X i) ≫
          (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafCoboundary R X i).hom ≫
          (singularRestrictionSheaf R j (i + 1)).hom = _
      calc
        _ = (toSheafify (Opens.grothendieckTopology X)
              (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X i) ≫
              (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafCoboundary R X i).hom) ≫
            (singularRestrictionSheaf R j (i + 1)).hom :=
          (Category.assoc _ _ _).symm
        _ = (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R X i ≫
              toSheafify (Opens.grothendieckTopology X)
                (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X (i + 1))) ≫
            (singularRestrictionSheaf R j (i + 1)).hom := by
          rw [toSheafify_naturality]
          rfl
        _ = _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R X i ≫
            (toSheafify (Opens.grothendieckTopology X)
              (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X (i + 1)) ≫
              (singularRestrictionSheaf R j (i + 1)).hom) :=
          Category.assoc _ _ _
        _ = _ := by rw [toSheafify_comp_singularRestrictionSheaf]
    · unfold η
      change toSheafify (Opens.grothendieckTopology X)
          (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X i) ≫
          (singularRestrictionSheaf R j i).hom ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
            (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafCoboundary R U i)).hom = _
      calc
        _ = (toSheafify (Opens.grothendieckTopology X)
              (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X i) ≫
              (singularRestrictionSheaf R j i).hom) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
              (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafCoboundary R U i)).hom :=
          (Category.assoc _ _ _).symm
        _ = singularRestrictionPresheaf R j i ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
              (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafCoboundary R U i)).hom := by
          rw [toSheafify_comp_singularRestrictionSheaf]
        _ = _ := (singularRestrictionPresheaf_coboundary R j i).symm

end
end

end

end OAI.AlgebraicTopology.Singular.SheafCochainRestriction
