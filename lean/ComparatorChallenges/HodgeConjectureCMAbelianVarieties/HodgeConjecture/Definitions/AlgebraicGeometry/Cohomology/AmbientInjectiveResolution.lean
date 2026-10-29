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

import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenInjectiveResolution
import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

namespace OAI.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution

open _root_.AlgebraicGeometry

/-!
# The chosen injective resolution of the constant rational sheaf

`ℚ → I^•` is a chosen injective resolution of the constant rational sheaf on the analytic space
`X(ℂ)`, indexed by integers. It is K-injective.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

section
namespace ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- Let `X` be a scheme over `ℂ`. This is the complex `I^•` of sheaves of abelian groups in a chosen
injective resolution `ℚ → I^•` on the analytic space `X(ℂ)`. It is indexed by integers and is
zero in negative degrees. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex :
    CochainComplex (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  -- An injective resolution `ℚ_{X(ℂ)} → I^•`.
  (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (AddCommGrpCat.of ℚ)).cocomplex.extend
      ComplexShape.embeddingUpNat

/-- Let `X` be a scheme over `ℂ`. This is the augmentation `ℚ[0] → I^•` of the chosen injective
resolution of the constant rational sheaf on the analytic space `X(ℂ)`, with both complexes
indexed by integers. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X :=
  HomologicalComplex.extendMap
    (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution
      (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (AddCommGrpCat.of ℚ)).ι
    ComplexShape.embeddingUpNat

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation_quasiIso :
    QuasiIso (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X) := by
  let I := _root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (AddCommGrpCat.of ℚ)
  let : QuasiIso I.ι := I.quasiIso
  exact (HomologicalComplex.quasiIso_extendMap_iff I.ι _).mpr inferInstance

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex_injective (q : ℤ) :
    Injective ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).X q) :=
  _root_.OAI.Algebra.Homology.LiftToInjective.CochainComplex.injective_extend_nat _
    (_root_.OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution
      (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (AddCommGrpCat.of ℚ)).injective q

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex_isStrictlyGE :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).IsStrictlyGE 0 := by
  dsimp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex]
  infer_instance

local instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalConeForgetSheafDerivedCategory :
    HasDerivedCategory (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex_isKInjective :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

/-- The augmentation `ℚ[0] → I^•`, with the source the constant sheaf placed in degree zero. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation :
    (CochainComplex.singleFunctor (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℚ) ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation_quasiIso :
    QuasiIso (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X) := by
  dsimp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation]
  infer_instance


end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
