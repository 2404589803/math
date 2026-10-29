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

import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.HolomorphicDeRham

import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicPoincare
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Topology.Sheaves.Sheafify
import HodgeConjecture.Mathlib.Topology.Sheaves.StalkExact
import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.AnalyticDifferentialForms
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Topology.Sheaves.Abelian

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicGeometry.Hodge.HolomorphicDeRhamAdd

open _root_.AlgebraicGeometry

/-!
# The holomorphic de Rham complex

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.HolomorphicDeRham`.
-/

/-! ### Constructions used only in proofs -/

noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold
section
namespace ComplexPoint
open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point
variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Multiplication by a complex scalar on the presheaf of holomorphic de Rham forms. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p where
  app U := AddCommGrpCat.ofHom
    ((c • LinearMap.id : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p →ₗ[ℂ] _).toAddMonoidHom)
  naturality {U V} i := by
    ext x
    dsimp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf] at x ⊢
    change c • _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i p x =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i p (c • x)
    exact (LinearMap.map_smul _ c x).symm

/-- Scalar multiplication commutes with the exterior derivative. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_d
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p c ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d (p + 1) c :=
  NatTrans.ext <| funext fun U => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x =>
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d U p).map_smul c x

/-- Multiplication by a complex scalar as an endomorphism of the sheafified de Rham complex. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex [SmoothOfRelativeDimension d X.hom]
    (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d :=
  CochainComplex.ofHom
    (fun p =>
      let J := Opens.grothendieckTopology
        (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
      (presheafToSheaf J AddCommGrpCat).map
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p c))
    (fun p => by
      let J := Opens.grothendieckTopology
        (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
      unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex
      simp only [CochainComplex.of_d]
      change (presheafToSheaf J AddCommGrpCat).map
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p c) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p) =
        (presheafToSheaf J AddCommGrpCat).map
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d (p + 1) c)
      rw [← Functor.map_comp, ← Functor.map_comp,
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_d])

/-- Multiplication by a complex scalar on the integer-indexed holomorphic de Rham complex. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom]
    (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt X ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt X :=
  HomologicalComplex.extendMap
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) c) ComplexShape.embeddingUpNat

end ComplexPoint
end
end

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

section
namespace ComplexPoint

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Scalar multiplication on the constant complex presheaf. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf (c : ℂ) :
    𝓒ᵖ(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶ 𝓒ᵖ(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℂ) where
  app _ := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)
  naturality {U V} i := by
    ext x
    rfl

/-- Scalar multiplication on the constant complex sheaf. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf (c : ℂ) :
    𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶ 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℂ) :=
  let J := Opens.grothendieckTopology
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
  (presheafToSheaf J AddCommGrpCat).map
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X c)

/-- Scalar multiplication on the constant complex-valued complex concentrated in degree zero. -/
@[implicit_reducible]
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex (c : ℂ) :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))).obj
        𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))).obj
        𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℂ) :=
  (CochainComplex.single₀ _).map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X c)

/-- Scalar multiplication on the integer-indexed constant complex-valued complex. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X c)
    ComplexShape.embeddingUpNat

end ComplexPoint
end

end

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

section
namespace ComplexPoint

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_apply
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (c : ℂ)
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p c).app U x = c • x := rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_zero
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p 0 = 0 := by
  dsimp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_one
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p 1 = 𝟙 _ := by
  dsimp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_add
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (a b : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p (a + b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p a +
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p b := by
  dsimp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf]
  simp [add_smul]
  rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_mul
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (a b : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p (a * b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p b ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p a := by
  dsimp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf]
  simp [mul_smul]
  rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_zero
    [SmoothOfRelativeDimension d X.hom] :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d 0 = 0 := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat).map
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p 0) = 0
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_zero, Functor.map_zero]

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_one
    [SmoothOfRelativeDimension d X.hom] :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d 1 = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat).map
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p 1) = 𝟙 _
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_one]
  exact (presheafToSheaf
    (Opens.grothendieckTopology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
    AddCommGrpCat).map_id _

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_add
    [SmoothOfRelativeDimension d X.hom] (a b : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d (a + b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d a +
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d b := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat).map
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p (a + b)) = _
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_add, Functor.map_add]
  rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_mul
    [SmoothOfRelativeDimension d X.hom] (a b : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d (a * b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d b ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d a := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat).map
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p (a * b)) = _
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_mul, Functor.map_comp]
  rfl

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the constant
complex presheaf. This is the presheaf-level source of conjugate-linearity. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf_comp_conj (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X c ≫ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf X =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf X ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X (starRingEnd ℂ c) := by
  ext U : 2
  exact AddMonoidHom.ext (map_mul (starRingEnd ℂ) c)

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the constant
complex sheaf. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf_comp_conj (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X c ≫ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheaf X =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheaf X ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X (starRingEnd ℂ c) := by
  let J := Opens.grothendieckTopology
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
  change (presheafToSheaf J AddCommGrpCat).map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X c) ≫
      (presheafToSheaf J AddCommGrpCat).map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf X) =
    (presheafToSheaf J AddCommGrpCat).map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf X) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X (starRingEnd ℂ c))
  rw [← Functor.map_comp, ← Functor.map_comp, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf_comp_conj]

/-- The inclusion of constant zero-forms commutes with complex scalar multiplication. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero_scalar
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X d ≫
      (let J := Opens.grothendieckTopology
        (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
      (presheafToSheaf J AddCommGrpCat).map
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d 0 c)) =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X c ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X d := by
  let J := Opens.grothendieckTopology
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
  change (presheafToSheaf J AddCommGrpCat).map
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d 0 c) =
    (presheafToSheaf J AddCommGrpCat).map
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X c) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  let f := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d U
  change (c • LinearMap.id).toAddMonoidHom.comp f.toAddMonoidHom =
    f.toAddMonoidHom.comp (DistribSMul.toAddMonoidHom ℂ c)
  ext x
  exact (f.map_smul c x).symm

/-- The constant-to-de Rham comparison commutes with complex scalar multiplication. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex_scalar
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X d ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d c =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X c ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X d := by
  apply HomologicalComplex.hom_ext
  intro p
  rcases p with _ | p
  · exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero_scalar X d c
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℂ) (p + 1)
      (Nat.succ_ne_zero p)).eq_of_src

/-- Conjugation intertwines the two scalar multiplications in degree zero. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex_comp_conj (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X c ≫ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexComplex X =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexComplex X ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X (starRingEnd ℂ c) := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexComplex
  rw [← Functor.map_comp, ← Functor.map_comp, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf_comp_conj]

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the
integer-indexed constant complex. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt_comp_conj (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c ≫ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheafComplexInt X =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheafComplexInt X ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X (starRingEnd ℂ c) := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheafComplexInt
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex_comp_conj]

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_zero
    [IsIntegral X.left] [Smooth X.hom] :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X 0 = 0 := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_zero, HomologicalComplex.extendMap_zero]
  rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_one
    [IsIntegral X.left] [Smooth X.hom] :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X 1 = 𝟙 _ := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_one]
  exact HomologicalComplex.extendMap_id _ _

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_add
    [IsIntegral X.left] [Smooth X.hom] (a b : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X (a + b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X a +
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X b := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_add, HomologicalComplex.extendMap_add]
  rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_mul
    [IsIntegral X.left] [Smooth X.hom] (a b : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X (a * b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X b ≫
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X a := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_mul, HomologicalComplex.extendMap_comp]
  rfl

/-- The integer-indexed constant-to-de Rham comparison commutes with complex scalar
multiplication. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt_scalar
    [IsIntegral X.left] [Smooth X.hom] (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X c =
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c ≫
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X := by
  change HomologicalComplex.extendMap
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) c) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X c) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex_scalar]

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Hodge.HolomorphicDeRhamAdd
