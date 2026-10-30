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

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainRestriction
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain

namespace OAI.AlgebraicTopology.Singular.GlobalRestriction

/-!
# Global singular restriction

This file identifies the top-open comparison with the chosen sheafification unit and proves
that global singular restriction commutes strictly with that unit. This is the naturality square
needed to compare a support cone built from singular-cochain sheaves with the corresponding raw
singular-cochain cone.
-/

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace

section
section

variable (R : Type) [CommRing R] {U X : TopCat.{0}} (j : U ⟶ X)

/-- Restriction of the raw singular-cochain presheaf complexes. -/
def singularRawRestrictionComplex :
    _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex R X ⟶
      ((Functor.whiskeringLeft _ _ _).obj (Opens.map j).op).mapHomologicalComplex
        (ComplexShape.up ℕ) |>.obj (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex R U) where
  f n := _root_.OAI.AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionToRawPushforward R j n
  comm' i k hik := by
    obtain rfl := hik
    rw [_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex_d, Functor.mapHomologicalComplex_obj_d,
      _root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex_d]
    exact (_root_.OAI.AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionToRawPushforward_coboundary R j i).symm

/-- Raw singular cochains on the inverse image of the top open. -/
def globalRawPushforwardSingularCochainComplex : CochainComplex AddCommGrpCat ℕ :=
  ((((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op (⊤ : Opens X))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    ((((Functor.whiskeringLeft _ _ _).obj (Opens.map j).op).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex R U)))

/-- Global sections of the pushforward singular-cochain sheaf complex. -/
def globalPushforwardSingularCochainSheafComplex : CochainComplex AddCommGrpCat ℕ :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
      (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R U)))

/-- Restriction of raw global singular cochains to the inverse image of the top open. -/
def globalRawSingularRestriction :
    _root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R X ⟶
      globalRawPushforwardSingularCochainComplex R j :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularRawRestrictionComplex R j)

/-- Restriction on the global-section complexes of singular-cochain sheaves. -/
def globalSingularSheafRestriction :
    _root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R X ⟶
      globalPushforwardSingularCochainSheafComplex R j :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (_root_.OAI.AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionSheafComplex R j))

/-- The sheafification unit evaluated after restriction to the inverse image of the top open. -/
def globalRawPushforwardToSingularSheaf :
    globalRawPushforwardSingularCochainComplex R j ⟶
      globalPushforwardSingularCochainSheafComplex R j :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      ((((Functor.whiskeringLeft _ _ _).obj (Opens.map j).op).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafificationUnit R U))

/-- The double-plus presentation of the comparison is the chosen sheafification unit in each
degree. -/
lemma topOpenToGlobalSingularCochainSheafComplex_f (n : ℕ) :
    (_root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R X).f n =
      (toSheafify (Opens.grothendieckTopology X)
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n)).app (.op ⊤) := by
  change ((_root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainToPlusPlusPresheafComplex R X).f n ≫
      (_root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainPlusPlusPresheafComplexIsoSheafComplex R X).hom.f n).app
        (.op ⊤) = _
  rw [_root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainToPlusPlusPresheafComplex_f]
  change ((Opens.grothendieckTopology X).toSheafify
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n) ≫
    (plusPlusIsoSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R X n)).hom).app (.op ⊤) = _
  rw [toSheafify_plusPlusIsoSheafify_hom]

/-- Global restriction commutes strictly with sheafification. -/
lemma globalSingularSheafRestriction_naturality :
    _root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R X ≫
        globalSingularSheafRestriction R j =
      globalRawSingularRestriction R j ≫
        globalRawPushforwardToSingularSheaf R j := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    topOpenToGlobalSingularCochainSheafComplex_f]
  exact congrArg (fun f ↦ f.app (.op ⊤))
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochainRestriction.toSheafify_comp_singularRestrictionSheaf R j n)

end
end

end

end OAI.AlgebraicTopology.Singular.GlobalRestriction
