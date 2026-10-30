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

import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicGeometry.Hodge.FiltrationId

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# The Hodge filtration

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration`.
-/

/-! ### Constructions used only in proofs -/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace
open scoped TensorProduct

section
namespace ComplexPoint

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

attribute [local instance] _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticHasDerivedCategory

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

/-- A rational number as a morphism from the integer to the rational constant sheaf. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf (q : K) :
    𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℤ) ⟶ 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); K) :=
  (_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).map
    (AddCommGrpCat.ofHom (zmultiplesAddHom K q))

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf_zero :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X 0 = 0 := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf
  rw [map_zero (zmultiplesAddHom K)]
  have h : AddCommGrpCat.ofHom (0 : ℤ →+ K) = 0 := AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf_add (a b : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X (a + b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X a +
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X b := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf
  rw [map_add (zmultiplesAddHom K)]
  have h : AddCommGrpCat.ofHom
      (zmultiplesAddHom K a + zmultiplesAddHom K b) =
      AddCommGrpCat.ofHom (zmultiplesAddHom K a) +
        AddCommGrpCat.ofHom (zmultiplesAddHom K b) :=
    AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_add]
  rfl

/-- The source object of Mathlib's sheaf cohomology mapped to the constant integer sheaf. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.uliftIntegerToIntegerConstantSheaf :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℤ) :=
  (_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)).map
    (AddCommGrpCat.ofHom (AddEquiv.ulift (α := ℤ)).toAddMonoidHom)

/-- The constant rational class `q` in degree-zero rational cohomology. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass (q : K) : H^0(X; K) :=
  Abelian.Ext.mk₀ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.uliftIntegerToIntegerConstantSheaf X ≫ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X q)

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass_zero :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass K X 0 = 0 := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf_zero]
  exact (congrArg Abelian.Ext.mk₀
    (Limits.comp_zero (f := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.uliftIntegerToIntegerConstantSheaf X))).trans
    (Abelian.Ext.mk₀_zero _ _)

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass_add (a b : K) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass K X (a + b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass K X a + _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass K X b := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf_add]
  exact (congrArg Abelian.Ext.mk₀ (Preadditive.comp_add _ _ _ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.uliftIntegerToIntegerConstantSheaf X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X a) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X b))).trans
    (Abelian.Ext.mk₀_add _ _)

end ComplexPoint
end

end

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace
open scoped TensorProduct

section
namespace ComplexPoint

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

attribute [local instance] _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticHasDerivedCategory

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_zero : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X 0 = 0 := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf
  rw [_root_.OAI.Algebra.Ring.Basic.AddMonoidHom.mulLeft_zero]
  have h : AddCommGrpCat.ofHom (0 : K →+ K) = 0 := AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex_zero : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X 0 = 0 := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_zero, Functor.map_zero, HomologicalComplex.extendMap_zero]

/-- Postcomposition by the zero map of complexes is the zero map on hypercohomology. -/
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_zero
    {K L : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (0 : K ⟶ L) n = 0 := by
  refine AddMonoidHom.ext fun α ↦ ?_
  apply (Localization.SmallShiftedHom.equiv
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap
  simp [Localization.SmallShiftedHom.equiv_comp,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_zero]

/-- Postcomposition by the identity map of complexes is the identity on hypercohomology. -/
@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_id
    {K : CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (𝟙 K) n = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun α ↦ ?_
  let eK : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n :=
    Localization.SmallShiftedHom.equiv
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
  change α.comp
      (Localization.SmallShiftedHom.mk₀
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) 0 rfl (𝟙 K))
      (zero_add n) = α
  apply eK.injective
  simp [eK]

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConjSemilinear_apply [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.DeRhamHypercohomology X n) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConjSemilinear X n α = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.deRhamConj X n α := rfl

/-! #### Real coefficient fields

The hypothesis `hK` below says conjugation fixes the image of `K` in `ℂ`, equivalently that
`K → ℂ` lands in `ℝ`. It holds for `ℚ` and fails for `ℚ(i) ⊆ ℂ`. -/

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Hodge.FiltrationId
