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

import HodgeConjecture.Mathlib.CategoryTheory.Sites.SheafCohomology.Pair
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sets.Closeds

namespace OAI.AlgebraicTopology.Support.Cohomology

open _root_.TopCat

/-!
# Sheaf cohomology with support in a closed set

For a closed subset `Z` of a topological space `X`, `H^n_Z(X; F)` is the cohomology of the pair
`(X, X \ Z)` with coefficients in the abelian sheaf `F`, that is `Ext (ℤ[X, X \ Z]) F n`.
Forgetting the support is the map `H^n_Z(X; F) → H^n(X; F)` of the long exact sequence of the
pair.
-/

noncomputable section

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace

namespace TopCat
open _root_.TopCat
namespace Sheaf
open _root_.TopCat
open _root_.TopCat.Sheaf

universe w u

variable (X : TopCat.{u})

instance {U V : Opens X} (f : U ⟶ V) : Mono f := ⟨fun _ _ _ => Subsingleton.elim _ _⟩

variable [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- `H^n_Z(X; F)`, the sheaf cohomology of `X` with support in the closed set `Z` and coefficients
in `F`: the cohomology of the pair `(X, X \ Z)`. -/
abbrev supportH (Z : Closeds X)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) : Type w :=
  _root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n (homOfLE (le_top : Z.compl ≤ ⊤))

@[inherit_doc supportH]
scoped notation:max "H_[" Z "]^" n:max "(" X "; " F ")" => _root_.OAI.AlgebraicTopology.Support.Cohomology.TopCat.Sheaf.supportH X Z F n

omit [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- `ℤ[U] = 0` for the empty open `U`: every sheaf has only the zero section on `U`. -/
lemma isZero_freeAbelianSheaf_of_eq_bot (U : Opens X) (hU : U = ⊥) :
    IsZero ((_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology X)).obj U) := by
  subst hU
  rw [IsZero.iff_id_eq_zero]
  apply (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafHomAddEquiv ⊥ _).injective
  have : Subsingleton
      (((_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology X)).obj ⊥).obj.obj
        (op ⊥)) :=
    AddCommGrpCat.subsingleton_of_isZero (IsZero.of_iso (isZero_zero _)
      (HasZeroObject.zeroIsoIsTerminal (CategoryTheory.Sheaf.isTerminalOfBotCover
        ((_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology X)).obj ⊥)
        ⊥ (fun _ h => h.elim))).symm)
  exact Subsingleton.elim _ _

/-- For `W = ⊥`, the map `ℤ[V] ⟶ ℤ[V, W]` is an isomorphism. -/
instance {W V : Opens X} (f : W ⟶ V) [Fact (W = ⊥)] :
    IsIso (cokernel.π ((_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology X)).map f)) := by
  have hf : (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology X)).map f = 0 :=
    (isZero_freeAbelianSheaf_of_eq_bot X W Fact.out).eq_of_src _ _
  have : cokernel.π ((_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology X)).map f) =
      cokernel.π (0 : _ ⟶ _) ≫ (cokernelIsoOfEq hf).inv := by
    rw [← π_comp_cokernelIsoOfEq_hom hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this]
  infer_instance

/-- Forgetting the support `X` itself loses nothing. -/
lemma relH.forget_injective_of_eq_bot
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) {W V : Opens X}
    (f : W ⟶ V) (hW : W = ⊥) (n : ℕ) :
    Function.Injective (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.forget F f n) :=
  haveI : Fact (W = ⊥) := ⟨hW⟩
  (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Abelian.Ext.precompAddEquiv (asIso (cokernel.π
    ((_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology X)).map f))) F n).injective

variable {X} (Z : Closeds X)
  (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- `H^n_Z(X; F) → H^n(X; F)`, forgetting the support. -/
def supportH.forget (n : ℕ) : H_[Z]^n(X; F) →+ F.H n :=
  (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.H'.addEquivTerminal isTerminalTop F n).toAddMonoidHom.comp
    (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.forget F _ n)

/-- The map on cohomology with support induced by a morphism of sheaves. -/
def supportH.map {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (g : F ⟶ G) (n : ℕ) : H_[Z]^n(X; F) →+ H_[Z]^n(X; G) :=
  _root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.map _ g n

end Sheaf
end TopCat

end

end OAI.AlgebraicTopology.Support.Cohomology
