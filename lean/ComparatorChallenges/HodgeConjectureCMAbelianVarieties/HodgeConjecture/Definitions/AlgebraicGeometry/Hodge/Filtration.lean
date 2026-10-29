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

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Lemmas.Algebra.FieldToComplex
import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicDeRham
import HodgeConjecture.Lemmas.LinearAlgebra.HodgeStructure
import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend
import HodgeConjecture.Mathlib.Algebra.Homology.StupidTruncation
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.CategoryTheory.Localization.SmallShiftedHom
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Data.Int.Cast.Lemmas

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicGeometry.Hodge.Filtration

open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# The Hodge filtration

This file defines constant-sheaf cohomology and holomorphic de Rham hypercohomology on the
analytic complex-point space of a smooth complex scheme. Constant-sheaf cohomology is Mathlib's
sheaf cohomology. Hypercohomology is expressed with Mathlib's small shifted morphisms in the
localization at quasi-isomorphisms; for the constant sheaf complex it agrees with sheaf
cohomology. This avoids exposing a noncanonical choice of derived category in the public types.

The stupid truncation of the holomorphic de Rham complex in form degrees at least `p` maps into
the full complex. Its image on hypercohomology is the Hodge filtration `F^p`. A rational Hodge
class is then a rational class whose de Rham image belongs to `F^p`.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace
open scoped TensorProduct

section
namespace ComplexPoint

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

/- Sheaves on a space are sheaves on its site of opens; the category instance is looked up under
that spelling by Mathlib's sheaf cohomology. -/
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf

def siteSheafHom {Y : TopCat} {F G : TopCat.Sheaf AddCommGrpCat Y} (f : F ⟶ G) :
    (show CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat from F) ⟶
      (show CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat from G) :=
  f

lemma siteSheafHom_comp {Y : TopCat} {F G H : TopCat.Sheaf AddCommGrpCat Y}
    (f : F ⟶ G) (g : G ⟶ H) :
    siteSheafHom (f ≫ g) = siteSheafHom f ≫ siteSheafHom g := by
  rfl

lemma siteSheafHom_id {Y : TopCat} {F : TopCat.Sheaf AddCommGrpCat Y} :
    siteSheafHom (𝟙 F) =
      𝟙 (show CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat from F) := by
  rfl

/-- Let `X` be a scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This is the category of
sheaves of abelian groups on `X(ℂ)`. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))

local instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticHasDerivedCategory :
    HasDerivedCategory (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)

/-- Let `K` be a field with a specified embedding into `ℂ`, and let `X` be a scheme over `ℂ`. This
morphism of constant sheaves on the analytic space `X(ℂ)` sends a locally constant `K`-valued
function to the same function with values in `ℂ`. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheaf :
    𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K) ⟶ 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℂ) :=
  (_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).map
    (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom)

/-- Let `K` be a field and `X` a scheme over `ℂ`. This integer-indexed complex on the analytic space
`X(ℂ)` has the constant sheaf `K` in degree zero, zero sheaves in all other degrees, and zero
differentials. -/
@[implicit_reducible]
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt :
    CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  ((CochainComplex.single₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).obj
    𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K)).extend ComplexShape.embeddingUpNat

instance : (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt K X).IsStrictlyGE 0 := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt
  infer_instance

/-- Let `K` be a field with a specified embedding into `ℂ`, and let `X` be a scheme over `ℂ`. This
map of integer-indexed complexes applies `K → ℂ` to the constant sheaves in degree zero. Both
complexes are zero in every other degree. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt K X ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).map
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheaf K X)) ComplexShape.embeddingUpNat

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ`, this map `K[0] → Ω^•` sends locally constant `K`-valued functions to
holomorphic zero-forms via the embedding. Here `Ω^•` is the complex of sheaves of holomorphic
differential forms with exterior derivative. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom] :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt K X ⟶ Ω•(X) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt K X ≫
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X

/-- Let `X` be a scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This integer-indexed
complex has the constant integer sheaf in degree zero and zero sheaves in all other degrees,
with zero differentials. -/
@[implicit_reducible]
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt :
    CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  ((CochainComplex.single₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).obj
    𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℤ)).extend ComplexShape.embeddingUpNat

/-- Let `K` be a field, `X` a scheme over `ℂ`, and `q ∈ K`. This endomorphism of the constant sheaf
`K` on the analytic space `X(ℂ)` multiplies each locally constant function by `q`. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf (q : K) :
    𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K) ⟶ 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K) :=
  (_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).map
    (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft q))

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_one : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X 1 = 𝟙 _ := by
  have h : AddCommGrpCat.ofHom (AddMonoidHom.id K) = 𝟙 (AddCommGrpCat.of K) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft 1)) =
    𝟙 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K)
  rw [_root_.OAI.Algebra.Ring.Basic.AddMonoidHom.mulLeft_one, h]
  exact (_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).map_id (AddCommGrpCat.of K)

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_add (a b : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X (a + b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X a + _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X b := by
  have h : AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a + AddMonoidHom.mulLeft b) =
      AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a) +
        AddCommGrpCat.ofHom (AddMonoidHom.mulLeft b) :=
    AddCommGrpCat.hom_ext rfl
  change (_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (a + b))) = _
  rw [_root_.OAI.Algebra.Ring.Basic.AddMonoidHom.mulLeft_add, h, Functor.map_add]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_mul (a b : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X (a * b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X b ≫ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X a := by
  have h : AddCommGrpCat.ofHom
      ((AddMonoidHom.mulLeft a).comp (AddMonoidHom.mulLeft b)) =
      AddCommGrpCat.ofHom (AddMonoidHom.mulLeft b) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a) :=
    AddCommGrpCat.hom_ext rfl
  change (_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (a * b))) = _
  rw [_root_.OAI.Algebra.Ring.Basic.AddMonoidHom.mulLeft_mul, h, Functor.map_comp]
  rfl

/-- Multiplying by `q` in `K` before including into `ℂ` agrees with including first and then
multiplying by `algebraMap K ℂ q`. -/
lemma ofHom_algebraMap_comp_complexScalarSMul (q : K) :
    AddCommGrpCat.ofHom ↑(algebraMap K ℂ) ≫
        AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ (algebraMap K ℂ q)) =
      AddCommGrpCat.ofHom (AddMonoidHom.mulLeft q) ≫
        AddCommGrpCat.ofHom ↑(algebraMap K ℂ) := by
  ext r
  simp [map_mul]

/-- The constant-presheaf map induced by the inclusion `K → ℂ`, followed by scalar multiplication
by `algebraMap K ℂ q` on the constant complex presheaf, is the constant-presheaf map induced by the
composite additive map. -/
lemma const_map_algebraMap_comp_complexScalarPresheaf (q : K) : (Functor.const (Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))ᵒᵖ).map (AddCommGrpCat.ofHom ↑(algebraMap K ℂ)) ≫
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X ((algebraMap K ℂ) q) =
  (Functor.const (Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))ᵒᵖ).map
    (AddCommGrpCat.ofHom (algebraMap K ℂ : K →+ ℂ) ≫ AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ ((algebraMap K ℂ) q))) := rfl

/-- The inclusion of `K`-valued constants into complex constants commutes with scalar
multiplication. -/
lemma fieldToComplexConstantSheaf_scalar (q : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheaf K X ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X (algebraMap K ℂ q) =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X q ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheaf K X := by
  change siteSheafHom
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheaf K X ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X (algebraMap K ℂ q)) =
    siteSheafHom
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X q ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheaf K X)
  rw [siteSheafHom_comp, siteSheafHom_comp]
  simp only [siteSheafHom,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheaf,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf,
    constantSheaf, _root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.const,
    _root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor]
  let sheafify := presheafToSheaf
    (Opens.grothendieckTopology (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
    AddCommGrpCat
  let constantPresheaf :
      AddCommGrpCat ⥤
        (Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))ᵒᵖ ⥤
          AddCommGrpCat :=
    Functor.const (Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))ᵒᵖ
  change sheafify.map
      (constantPresheaf.map (AddCommGrpCat.ofHom ↑(algebraMap K ℂ))) ≫
      sheafify.map
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X
          (algebraMap K ℂ q)) =
    sheafify.map (constantPresheaf.map (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft q))) ≫
      sheafify.map
        (constantPresheaf.map (AddCommGrpCat.ofHom ↑(algebraMap K ℂ)))
  rw [← sheafify.map_comp,
    const_map_algebraMap_comp_complexScalarPresheaf,
    ← sheafify.map_comp, ← constantPresheaf.map_comp,
    ofHom_algebraMap_comp_complexScalarSMul]

/-- Let `K` be a field, `X` a scheme over `ℂ`, and `q ∈ K`. This endomorphism of the integer-indexed
complex `K[0]` on the analytic space `X(ℂ)` multiplies its degree-zero constant sheaf by `q`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex (q : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt K X ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt K X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).map
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X q)) ComplexShape.embeddingUpNat

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex_one : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X 1 = 𝟙 _ := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_one, (CochainComplex.single₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).map_id,
    HomologicalComplex.extendMap_id]

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex_add (a b : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X (a + b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X a + _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X b := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_add, Functor.map_add, HomologicalComplex.extendMap_add]

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex_mul (a b : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X (a * b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X b ≫ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X a := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_mul, Functor.map_comp, HomologicalComplex.extendMap_comp]

/-- The integer-indexed inclusion of `K`-valued constants into complex constants commutes with
scalar multiplication. -/
lemma fieldToComplexConstantSheafComplexInt_scalar (q : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt K X ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X (algebraMap K ℂ q) =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X q ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt K X := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex,
    ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex, ← Functor.map_comp, fieldToComplexConstantSheaf_scalar]

/-- The `K`-coefficient to de Rham comparison of complexes commutes with `K`-scalar
multiplication. -/
lemma fieldToHolomorphicDeRhamComplexInt_scalar
    [IsIntegral X.left] [Smooth X.hom] (q : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt K X ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q) =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X q ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt K X := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt
  rw [Category.assoc, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt_scalar, ← Category.assoc,
    fieldToComplexConstantSheafComplexInt_scalar, Category.assoc]

/-- Let `X` be a scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This is the class of maps
between integer-indexed complexes of sheaves of abelian groups that induce isomorphisms on every
cohomology sheaf. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms :=
  HomologicalComplex.quasiIso (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤᵘᵖ

noncomputable instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticHasSmallLocalizedShiftedHom
    (K L : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) :
    Localization.HasSmallLocalizedShiftedHom.{1}
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) ℤ K L := by
  intro a b
  exact Localization.hasSmallLocalizedHom_of_isLocalization
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q

/-- Let `X` be a scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For an integer-indexed
complex `F` of sheaves of abelian groups, its degree-`n` hypercohomology is `ℍ^n(X(ℂ); F) =
Hom_D(ℤ[0], F[n])`. Here `D` is the derived category, obtained by inverting maps inducing
isomorphisms on all cohomology sheaves, and `ℤ` is the constant integer sheaf. -/
@[implicit_reducible]
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology
    (K : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ) : Type 1 :=
  Localization.SmallShiftedHom.{1} (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X) K n

/-- `ℍ^n(X; 𝒦)` is the hypercohomology in integer degree `n` of a complex `𝒦` of sheaves on the
analytic space `X(ℂ)`. The symbol `ℍ` follows page 51 of
[P. Deligne, *The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf). -/
scoped notation:max "ℍ^" n:max "(" X "; " 𝒦 ")" => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X 𝒦 n

/-- `Ext`-groups of analytic sheaves are computed in `Type 1`. The instance is stated on the site
category, which is how Mathlib's sheaf cohomology looks it up. -/
instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticHasExt :
    HasExt.{1} (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat.{0}) :=
  fun _ _ _ _ ↦ Localization.hasSmallLocalizedHom_of_isLocalization
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q

/-- `H^n(X; K)` is the sheaf cohomology of the analytic space `X(ℂ)` with coefficients in the
constant sheaf `K`, in degree `n`, as defined in Mathlib.

The literature writes `H^n(X; K)` for the variety `X.left` alone; here the variety is presented by
its structure morphism `X`. -/
scoped notation3:max "H^" n:max "(" X "; " K ")" =>
  Sheaf.H ((_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).obj (AddCommGrpCat.of K)) n

/-- Let `X` be a scheme over `ℂ`, and give `X(ℂ)` its analytic topology. Degree-`n` cohomology with
coefficients in the constant complex sheaf is `H^n(X(ℂ); ℂ) = ℍ^n(X(ℂ); ℂ[0])`. It is the group
of morphisms `ℤ[0] → ℂ[n]` in the derived category of sheaves of abelian groups. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology (n : ℤ) : Type 1 :=
  ℍ^n(X; _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X)

noncomputable instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddCommGroup
    (K : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    AddCommGroup ℍ^n(X; K) :=
  fast_instance% (Localization.SmallShiftedHom.equiv
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).addCommGroup

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_zero
    (K : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    (Localization.SmallShiftedHom.equiv
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (0 : ℍ^n(X; K)) = 0 := by
  rw [Equiv.zero_def, Equiv.apply_symm_apply]

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_add
    (K : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    (α β : ℍ^n(X; K)) :
    (Localization.SmallShiftedHom.equiv
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q) (α + β) =
      (Localization.SmallShiftedHom.equiv
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q) α +
      (Localization.SmallShiftedHom.equiv
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q) β := by
  simp [Equiv.add_def]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. Holomorphic
de Rham cohomology `H_dR^n(X)` is the degree-`n` hypercohomology of the sheaf complex `𝒪 → Ω¹ →
Ω² → ⋯`, whose differential is exterior differentiation. The complex is zero in negative
degrees. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.DeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) : Type 1 :=
  ℍ^n(X; Ω•(X))

@[inherit_doc _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.DeRhamHypercohomology]
scoped notation:max "H_dR^" n:max "(" X ")" => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.DeRhamHypercohomology X n

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The
inclusion of locally constant complex functions into holomorphic zero-forms gives this
equivalence `H^n(X(ℂ); ℂ) ≃ ℍ^n(X(ℂ); Ω^•)`. The holomorphic Poincaré lemma makes the inclusion
`ℂ[0] → Ω^•` a quasi-isomorphism. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology X n ≃ H_dR^n(X) :=
  Localization.SmallShiftedHom.postcompEquiv
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X)
    (by
      change QuasiIso (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X)
      infer_instance)
/-- Let `X` be a scheme over `ℂ`, and give `X(ℂ)` its analytic topology. A map of sheaf complexes `f
: K → L` induces this additive map `ℍ^n(X(ℂ); K) → ℍ^n(X(ℂ); L)`. In the derived category it
sends `α : ℤ[0] → K[n]` to its composite with `f[n]`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap
    {K L : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ) :
    ℍ^n(X; K) →+ ℍ^n(X; L) where
  toFun α := α.comp
      (Localization.SmallShiftedHom.mk₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) 0 rfl f)
      (zero_add n)
  map_zero' := by
    apply (Localization.SmallShiftedHom.equiv
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_zero, ShiftedHom.zero_comp]

  map_add' α β := by
    apply (Localization.SmallShiftedHom.equiv
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_add, ShiftedHom.add_comp]

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smallShiftedHomMkZero_comp
    {K L M : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) :
    Localization.SmallShiftedHom.mk₀
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl (f ≫ g) =
      (Localization.SmallShiftedHom.mk₀
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl f).comp
        (Localization.SmallShiftedHom.mk₀
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl g)
          (zero_add (0 : ℤ)) := by
  let e : Localization.SmallShiftedHom
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) K M (0 : ℤ) ≃
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) (0 : ℤ) :=
    Localization.SmallShiftedHom.equiv
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  rw [Localization.SmallShiftedHom.equiv_comp]
  simp [e, Functor.map_comp]

/-- Postcomposition on hypercohomology respects composition of complex maps. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply
    {K L M : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) (n : ℤ)
    (α : ℍ^n(X; K)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (f ≫ g) n α =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X g n
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f n α) := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap
  dsimp
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smallShiftedHomMkZero_comp X]
  let β : Localization.SmallShiftedHom
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) K L (0 : ℤ) :=
    Localization.SmallShiftedHom.mk₀
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl f
  let γ : Localization.SmallShiftedHom
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) L M (0 : ℤ) :=
    Localization.SmallShiftedHom.mk₀
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl g
  simpa only using
    (Localization.SmallShiftedHom.comp_assoc
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) α β γ
      (zero_add n) (zero_add (0 : ℤ)) (zero_add n)).symm

/-- Postcomposition on hypercohomology is additive in the map of complexes. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_add_apply
    {C D : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (f g : C ⟶ D) (n : ℤ)
    (α : ℍ^n(X; C)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (f + g) n α =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f n α + _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X g n α := by
  apply (Localization.SmallShiftedHom.equiv
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_add]
  simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Functor.map_add]

/-- The constant sheaf complex is the constant sheaf placed in degree zero. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt K X ≅
      (CochainComplex.singleFunctor (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K) 0 0 rfl

/-- The integer constant sheaf complex is the source object of Mathlib's sheaf cohomology placed
in degree zero. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X ≅
      (CochainComplex.singleFunctor (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj
        ((constantSheaf (Opens.grothendieckTopology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
          AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℤ) 0 0 rfl ≪≫
    (CochainComplex.singleFunctor (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).mapIso
      ((_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).mapIso
        (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso).symm

local instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat.{0}) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticHasDerivedCategory X

/-- The source comparison, as a small shifted morphism from the source object of Mathlib's sheaf
cohomology to the integer constant sheaf complex. -/
def constantIntegerComparison :=
  Localization.SmallShiftedHom.mk₀Inv (W := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)

/-- The target comparison, as a small shifted morphism from the constant sheaf complex to the
constant sheaf in degree zero. -/
def constantFieldComparison :=
  Localization.SmallShiftedHom.mk₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle K X).hom

/-- Precomposition with the source comparison commutes with postcomposition by a map of
complexes. -/
lemma constantIntegerComparison_comp_comp_mk₀
    {L M : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (n : ℤ)
    (β : Localization.SmallShiftedHom (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X) L n) (h : L ⟶ M) :
    ((constantIntegerComparison X).comp β (add_zero n)).comp
      (Localization.SmallShiftedHom.mk₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl h) (zero_add n) =
    (constantIntegerComparison X).comp
      (β.comp (Localization.SmallShiftedHom.mk₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl h)
        (zero_add n)) (add_zero n) :=
  Localization.SmallShiftedHom.comp_assoc (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) _ β _
    (add_zero n) (zero_add n) (by simp)

/-- Hypercohomology of the constant sheaf complex is Mathlib's sheaf cohomology of the constant
sheaf. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology (n : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt K X) n ≃+ H^n(X; K) where
  toEquiv :=
    (Localization.SmallShiftedHom.precompEquiv.{1} (W := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance) (a := (n : ℤ))).symm.trans
    (Localization.SmallShiftedHom.postcompEquiv.{1} (W := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle K X).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance) (a := (n : ℤ)))
  map_add' α β := by
    apply Abelian.Ext.ext
    rw [Abelian.Ext.add_hom]
    show Localization.SmallShiftedHom.equiv (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((constantIntegerComparison X).comp (α + β) _).comp (constantFieldComparison K X) _) =
      Localization.SmallShiftedHom.equiv (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((constantIntegerComparison X).comp α _).comp (constantFieldComparison K X) _) +
      Localization.SmallShiftedHom.equiv (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((constantIntegerComparison X).comp β _).comp (constantFieldComparison K X) _)
    simp only [Localization.SmallShiftedHom.equiv_comp, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_add,
      ShiftedHom.add_comp, ShiftedHom.comp_add]
    rfl

omit [Algebra K ℂ] in
/-- The comparison with Mathlib's sheaf cohomology is natural in maps of constant sheaves. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology_map {L : Type} [Field L]
    (f : 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K) ⟶ 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); L)) (n : ℕ)
    (α : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt K X) n) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology L X n
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (HomologicalComplex.extendMap
        ((CochainComplex.single₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).map f)
          ComplexShape.embeddingUpNat) n α) =
    Sheaf.H.map f n (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology K X n α) := by
  show ((constantIntegerComparison X).comp (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (HomologicalComplex.extendMap
        ((CochainComplex.single₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).map f)
          ComplexShape.embeddingUpNat) n α) (add_zero _)).comp
      (constantFieldComparison L X) (zero_add _) =
    (((constantIntegerComparison X).comp α (add_zero _)).comp (constantFieldComparison K X)
      (zero_add _)).comp
      (Localization.SmallShiftedHom.mk₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        ((CochainComplex.singleFunctor (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).map f)) (zero_add _)
  refine (constantIntegerComparison_comp_comp_mk₀ X _ _ _).trans (Eq.trans ?_
    ((congrArg (fun γ => γ.comp (Localization.SmallShiftedHom.mk₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X)
      (0 : ℤ) rfl ((CochainComplex.singleFunctor (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).map f))
      (zero_add _)) (constantIntegerComparison_comp_comp_mk₀ X _ α _)).trans
        (constantIntegerComparison_comp_comp_mk₀ X _ _ _)).symm)
  congr 1
  change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ n (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ n α) =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ n (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ n α)
  rw [← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, ← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply]
  exact congrArg (fun g => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X g n α)
    (_root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.extendSingleIso_hom_naturality ComplexShape.embeddingUpNat f 0 0 rfl)

omit [Algebra K ℂ] in
/-- The inverse comparison is natural in maps of constant sheaves. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology_symm_map {L : Type} [Field L]
    (f : 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K) ⟶ 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); L)) (n : ℕ) (β : H^n(X; K)) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology L X n).symm (Sheaf.H.map f n β) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (HomologicalComplex.extendMap
        ((CochainComplex.single₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).map f)
          ComplexShape.embeddingUpNat) n
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology K X n).symm β) := by
  apply (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology L X n).injective
  rw [AddEquiv.apply_symm_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology_map,
    AddEquiv.apply_symm_apply]

/-- Let `X` be a scheme over `ℂ`, and give `X(ℂ)` its analytic topology. Let a semiring `R` act on a
sheaf complex `C` through endomorphisms `s(r)` with `s(a+b) = s(a)+s(b)`, `s(1) = id`, and
`s(ab) = s(a) ∘ s(b)`. If the specified scalar action on `ℍ^n(X(ℂ); C)` is induced by these
maps, this construction supplies its `R`-module structure. -/
noncomputable abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyModule {R : Type*} [Semiring R]
    {C : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (s : R → (C ⟶ C)) (n : ℤ)
    [SMul R ℍ^n(X; C)]
    (smul_eq : ∀ (r : R) (α : ℍ^n(X; C)),
      r • α = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (s r) n α)
    (s_add : ∀ a b : R, s (a + b) = s a + s b)
    (s_one : s 1 = 𝟙 C)
    (s_mul : ∀ a b : R, s (a * b) = s b ≫ s a) :
    Module R ℍ^n(X; C) :=
  Module.ofMinimalAxioms
    (fun r α β => by
      rw [smul_eq, smul_eq, smul_eq]
      exact (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (s r) n).map_add α β)
    (fun a b α => by
      rw [smul_eq, smul_eq, smul_eq, s_add]
      exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_add_apply X (s a) (s b) n α)
    (fun a b α => by
      rw [smul_eq, smul_eq, smul_eq, s_mul]
      exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X (s b) (s a) n α)
    (fun α => by
      rw [smul_eq, s_one]
      let e : ℍ^n(X; C) ≃
          ShiftedHom
            (DerivedCategory.Q.obj (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
            (DerivedCategory.Q.obj C) n :=
        Localization.SmallShiftedHom.equiv
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
      apply e.injective
      simp [e, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap])

/-- The `K`-action on constant-sheaf cohomology, induced by scalar multiplication on the
coefficient sheaf. -/
noncomputable instance (n : ℕ) :
    SMul K (H^n(X; K)) :=
  ⟨fun q α ↦ Sheaf.H.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X q) n α⟩

omit [Algebra K ℂ] in
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq (n : ℕ) (q : K) (α : H^n(X; K)) :
    q • α = Sheaf.H.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X q) n α := rfl

omit [Algebra K ℂ] in
lemma fieldScalarSheafCohomologyMap_comp_apply (a b : K) (n : ℕ) (α : H^n(X; K)) :
    Sheaf.H.map
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X b ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X a) n α =
      Sheaf.H.map
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X a) n
        (Sheaf.H.map
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X b) n α) := by
  change Sheaf.H.map
      (siteSheafHom
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X b ≫
          _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X a)) n α =
    Sheaf.H.map
      (siteSheafHom
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X a)) n
      (Sheaf.H.map
        (siteSheafHom
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X b)) n α)
  rw [siteSheafHom_comp, Sheaf.H.map_comp_apply]

omit [Algebra K ℂ] in
lemma fieldScalarSheafCohomologyMap_id_apply (n : ℕ) (α : H^n(X; K)) :
    Sheaf.H.map (𝟙 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K)) n α = α := by
  change Sheaf.H.map
    (siteSheafHom (𝟙 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K))) n α = α
  rw [siteSheafHom_id, Sheaf.H.map_id_apply]

/-- For a scheme `X` over `ℂ` and a field `K`, constant-sheaf cohomology `H^n(X(ℂ); K)` is a `K`-vector space, with scalars acting on coefficient functions. -/
noncomputable instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyModule (n : ℕ) :
    Module K (H^n(X; K)) :=
  Module.ofMinimalAxioms
    (fun r α β => by
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq]
      exact map_add _ α β)
    (fun a b α => by
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_add]
      exact Sheaf.H.map_add_apply _ _ α)
    (fun a b α => by
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_mul]
      exact fieldScalarSheafCohomologyMap_comp_apply K X a b n α)
    (fun α => by
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_one]
      exact fieldScalarSheafCohomologyMap_id_apply K X n α)

omit [Algebra K ℂ] in
/-- The comparison with hypercohomology carries scalar multiplication to the action of the
scalar complex. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology_symm_smul (n : ℕ) (q : K) (α : H^n(X; K)) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology K X n).symm (q • α) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X q) n
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology K X n).symm α) := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.field_smul_eq, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology_symm_map]
  rfl

/-- The complex action on holomorphic de Rham hypercohomology, induced by scalar multiplication
on the holomorphic de Rham complex. -/
noncomputable instance
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    SMul ℂ H_dR^n(X) :=
  ⟨fun c α ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X c) n α⟩

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRham_complex_smul_eq [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : H_dR^n(X)) :
    c • α = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X c) n α :=
  rfl

/-- Holomorphic de Rham hypercohomology is canonically a complex vector space. -/
noncomputable instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamHypercohomologyComplexModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module ℂ H_dR^n(X) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyModule X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X) n
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRham_complex_smul_eq X n) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_add X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_one X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_mul X)

/-- De Rham hypercohomology as a vector space over `K`, by restriction of complex scalars. -/
noncomputable instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamHypercohomologyModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module K H_dR^n(X) :=
  Module.restrictScalars K ℂ H_dR^n(X)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRham_field_smul_eq [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (q : K) (α : H_dR^n(X)) :
    q • α = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q)) n α :=
  rfl

/-- Restriction of complex scalars gives the scalar tower on de Rham hypercohomology. -/
noncomputable instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamHypercohomologyIsScalarTower
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    IsScalarTower K ℂ H_dR^n(X) :=
  IsScalarTower.restrictScalars K ℂ H_dR^n(X)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ`, this additive map `H^n(X(ℂ); K) → H_dR^n(X)` is induced by including
locally constant `K`-valued functions as holomorphic zero-forms. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    H^n(X; K) →+ H_dR^n(X) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt K X) n).comp
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology K X n).symm.toAddMonoidHom

/-- The `K`-coefficient to de Rham comparison is compatible with `K`-scalar multiplication. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomology_smul
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (q : K) (α : H^n(X; K)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomology K X n (q • α) =
      q • _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomology K X n α := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRham_field_smul_eq]
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomology
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology_symm_smul, ← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply,
    ← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, fieldToHolomorphicDeRhamComplexInt_scalar]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ`, the inclusion `K[0] → Ω^•` induces this `K`-linear map from constant-sheaf
cohomology `H^n(X(ℂ); K)` to holomorphic de Rham cohomology `H_dR^n(X)`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    H^n(X; K) →ₗ[K] H_dR^n(X) where
  toFun := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomology K X n
  map_add' := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomology K X n).map_add
  map_smul' := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomology_smul K X n

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For an
integer `p`, the complex `F^p Ω^•` has the sheaf of holomorphic `q`-forms in degrees `q ≥ p` and
zero in degrees `q < p`. Its remaining differentials are exterior derivatives; this is the
truncation by form degree. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamComplex [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  Ω•(X).stupidTrunc (ComplexShape.embeddingUpIntGE p)

@[inherit_doc _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamComplex]
scoped notation:max "F^" p:max " Ω•" "(" X ")" => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamComplex X p

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For an
integer `p`, this map `F^p Ω^• → Ω^•` is the identity on holomorphic forms in degrees at least
`p` and the zero map below `p`, where the source is zero. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    F^p Ω•(X) ⟶ Ω•(X) :=
  _root_.OAI.Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion Ω•(X) (ComplexShape.embeddingUpIntGE p)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For an
integer `p` and a scalar `c ∈ ℂ`, this endomorphism multiplies forms by `c` in the complex `F^p
Ω^•` of holomorphic forms in degrees at least `p`, which is zero in lower degrees. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamComplexScalar [IsIntegral X.left] [Smooth X.hom]
    (p : ℤ) (c : ℂ) :
    F^p Ω•(X) ⟶ F^p Ω•(X) :=
  HomologicalComplex.stupidTruncMap
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X c)
    (ComplexShape.embeddingUpIntGE p)

/-- Complex scalar multiplication on the filtered complex commutes with inclusion into the full
de Rham complex. -/
lemma hodgeFilteredDeRhamComplexScalar_comp_inclusion
    [IsIntegral X.left] [Smooth X.hom] (p : ℤ) (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamComplexScalar X p c ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X c :=
  _root_.OAI.Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion
    (ComplexShape.embeddingUpIntGE p)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X c)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For
integers `p` and `n`, this is `ℍ^n(X(ℂ); F^p Ω^•)`, the hypercohomology of the holomorphic de
Rham complex with terms below form degree `p` replaced by zero. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.FilteredDeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Type 1 :=
  ℍ^n(X; F^p Ω•(X))

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For
integers `p` and `n`, inclusion of holomorphic forms of degree at least `p` into the full de
Rham complex induces this map `ℍ^n(X(ℂ); F^p Ω^•) → H_dR^n(X)`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.filteredToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.FilteredDeRhamHypercohomology X p n →+ H_dR^n(X) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p) n

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The `p`-th
Hodge filtration in degree `n` is the additive subgroup `F^p H_dR^n(X)` given by the image of
`ℍ^n(X(ℂ); F^p Ω^•) → ℍ^n(X(ℂ); Ω^•)`. The source complex keeps holomorphic forms of degree at
least `p` and is zero in lower degrees. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    AddSubgroup H_dR^n(X) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.filteredToDeRhamCohomology X p n).range

/-- The Hodge filtration is stable under arbitrary complex scalar multiplication. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration_complex_smul_mem [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) (c : ℂ) {α : H_dR^n(X)}
    (hα : α ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p n) :
    c • α ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p n := by
  rcases hα with ⟨β, rfl⟩
  refine ⟨_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamComplexScalar X p c) n β, ?_⟩
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRham_complex_smul_eq]
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.filteredToDeRhamCohomology
  rw [← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, ← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamComplexScalar_comp_inclusion]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The complex
subspace `F^p H_dR^n(X)` is the image on degree-`n` hypercohomology of the inclusion of
holomorphic forms of degrees at least `p` into the full de Rham complex. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Submodule ℂ H_dR^n(X) where
  carrier := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p n
  zero_mem' := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p n).zero_mem
  add_mem' := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p n).add_mem
  smul_mem' := fun c _ h => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration_complex_smul_mem X p n c h

@[inherit_doc _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule]
scoped notation:max "F^" p:max " H_dR^" n:max "(" X ")" =>
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X p n

/-! ### Complex conjugation and the `(p,p)` part

Conjugation is not `ℂ`-linear, so it acts on the constant sheaf `ℂ` rather than on the holomorphic
de Rham complex, and is transported across the constant-to-de Rham comparison. The `(p,q)` piece
is then *defined* as `F^p ⊓ conj F^q`, which needs no Hodge decomposition theorem. -/

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This
additive equivalence `H^n(X(ℂ); ℂ) ≃ H_dR^n(X)` is induced by the inclusion of the constant
complex sheaf into the holomorphic de Rham complex. The inclusion is a quasi-isomorphism by the
holomorphic Poincaré lemma. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology X n ≃+ H_dR^n(X) :=
  { _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamEquiv X n with
    map_add' := fun α β ↦ by
      change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) n (α + β) =
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) n α +
          _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) n β
      exact map_add _ α β }

lemma complexConstantCohomologyDeRhamAddEquiv_apply [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (α : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology X n) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n α =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) n α :=
  rfl

/-- The comparison equivalence carries the constant-sheaf scalar action to the de Rham one. -/
lemma complexConstantCohomologyDeRhamAddEquiv_scalar [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (β : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology X n) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c) n β) =
      c • _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n β := by
  rw [complexConstantCohomologyDeRhamAddEquiv_apply,
    complexConstantCohomologyDeRhamAddEquiv_apply,
    ← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, ← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt_scalar,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRham_complex_smul_eq]

/-- The inverse comparison carries the de Rham scalar action back to the constant-sheaf one. -/
lemma complexConstantCohomologyDeRhamAddEquiv_symm_scalar [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : H_dR^n(X)) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n).symm (c • α) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c) n
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n).symm α) := by
  apply (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n).injective
  rw [AddEquiv.apply_symm_apply, complexConstantCohomologyDeRhamAddEquiv_scalar,
    AddEquiv.apply_symm_apply]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This
additive endomorphism of `H_dR^n(X)` is complex conjugation transported through `H^n(X(ℂ); ℂ) ≃
H_dR^n(X)`. On constant-sheaf cohomology, conjugation is induced by conjugating the locally
constant coefficient functions. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H_dR^n(X) →+ H_dR^n(X) :=
  ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n).toAddMonoidHom).comp
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheafComplexInt X) n).comp
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n).symm.toAddMonoidHom)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj_apply [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (α : H_dR^n(X)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj X n α =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheafComplexInt X) n
          ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n).symm α)) :=
  rfl

/-- Conjugation on de Rham hypercohomology is conjugate-linear. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj_smul [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (c : ℂ) (α : H_dR^n(X)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj X n (c • α) = (starRingEnd ℂ) c • _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj X n α := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj_apply,
    complexConstantCohomologyDeRhamAddEquiv_symm_scalar,
    ← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt_comp_conj,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, complexConstantCohomologyDeRhamAddEquiv_scalar]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. Conjugation
of constant complex coefficients, transported through `H^n(X(ℂ); ℂ) ≃ H_dR^n(X)`, gives this
conjugate-linear endomorphism of de Rham cohomology. It sends `c α` to `conj(c) conj(α)`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConjSemilinear [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H_dR^n(X) →ₛₗ[starRingEnd ℂ] H_dR^n(X) where
  toFun := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj X n
  map_add' := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj X n).map_add
  map_smul' := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj_smul X n

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The
conjugate Hodge filtration in degree `n` consists of classes whose complex conjugates lie in
`F^p H_dR^n(X)`. Here `F^p` is the image of the hypercohomology of holomorphic forms of degree
at least `p`, and conjugation is transported from constant complex coefficients. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjHodgeFiltrationComplexSubmodule [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Submodule ℂ H_dR^n(X) :=
  (F^p H_dR^n(X)).comap (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConjSemilinear X n)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This
complex subspace of `H_dR^n(X)` is `F^p ∩ conjugate(F^q)`, where `F^r` is the image of the
hypercohomology of holomorphic forms in degrees at least `r`. Conjugation comes from constant
complex coefficients. When `X` is projective and `p + q = n`, this is the Hodge component of
type `(p,q)`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgePiece [IsIntegral X.left] [Smooth X.hom] (p q n : ℤ) :
    Submodule ℂ H_dR^n(X) :=
  F^p H_dR^n(X) ⊓ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjHodgeFiltrationComplexSubmodule X q n

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ` and a natural number `p`, these are the classes in `H^{2p}(X(ℂ); K)` whose
de Rham images belong to `F^p ∩ conjugate(F^p)`. The filtration `F^p` is the image of the
hypercohomology of holomorphic forms of degrees at least `p`. Conjugation is induced by
conjugating constant complex coefficients; for projective `X`, the intersection is the Hodge
component of type `(p,p)`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeClasses [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    Submodule K (H^(2 * p)(X; K)) :=
  ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgePiece X p p (2 * p : ℕ)).restrictScalars K).comap
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear K X (2 * p))

/-- `Hdg^p(f; K)` is the space of Hodge classes of codimension `p` with coefficients in `K`.

The literature writes `Hdg^p(X.left)` for the variety `X.left` alone; here the variety is
presented by its structure morphism `f`, and the coefficient field is named. -/
scoped notation:max "Hdg^" p:max "(" f "; " K ")" => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hodgeClasses K f p

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Hodge.Filtration
