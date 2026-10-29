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

import HodgeConjecture.Lemmas.AlgebraicTopology.Support.CohomologyFlasqueModel
import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel
import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.CohomologySheaf

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

namespace OAI.AlgebraicGeometry.Cohomology.WithSupport

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# Cohomology of the analytic space with support in a closed set

`H^n_Z(X(ℂ); K)` is the sheaf cohomology of `X(ℂ)` with support in the closed set `Z` and
coefficients in the constant sheaf `K`. Forgetting the support lands in `H^n(X(ℂ); K)`. With
rational coefficients the group is computed by the sections supported in `Z` of the chosen
injective resolution of `ℚ`, or of the sheafified singular cochains.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace

section
namespace ComplexPoint

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (K : Type) [Field K] (X : Over (Spec ↧ℂ))

set_option quotPrecheck false in
/-- `H_[Z]^n(X; K)` is the sheaf cohomology of the analytic space `X(ℂ)` with support in the closed
set `Z ⊆ X(ℂ)` and coefficients in the constant sheaf `K`, in degree `n`. -/
scoped notation:max "H_[" Z "]^" n:max "(" X "; " K ")" =>
  _root_.OAI.AlgebraicTopology.Support.Cohomology.TopCat.Sheaf.supportH
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) Z
    ((_root_.OAI.AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor
      (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))).obj
      (AddCommGrpCat.of K)) n

variable (Z : Closeds (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))

/-- `H^n_Z(X(ℂ); K) → H^n(X(ℂ); K)`, forgetting the support. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.forgetSupport (n : ℕ) : H_[Z]^n(X; K) →+ H^n(X; K) :=
  (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.H'.addEquivTerminal isTerminalTop _ n).toAddMonoidHom.comp
    (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.forget _ (homOfLE (le_top : Z.compl ≤ ⊤)) n)

/-- Forgetting the support `X(ℂ)` itself is injective. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.forgetSupport_injective_of_eq_top (hZ : Z = ⊤) (n : ℕ) :
    Function.Injective (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.forgetSupport K X Z n) :=
  (_root_.OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.H'.addEquivTerminal isTerminalTop _ n).injective.comp
    (_root_.OAI.AlgebraicTopology.Support.Cohomology.TopCat.Sheaf.relH.forget_injective_of_eq_bot (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) _ _
      (by rw [hZ]; ext; simp) n)

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
/-- `H^n_Z(X(ℂ); ℚ) ≃ H^n(Γ_Z(X(ℂ), I))` for the chosen injective resolution `ℚ → I`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology (n : ℕ) :
    H_[Z]^n(X; ℚ) ≃+
      (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X Z)).homology n :=
  @_root_.OAI.AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) Z.compl ⊤
    Z.compl (top_inf_eq _) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticHasExt X) _ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex_isKInjective X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation_quasiIso X) n

section Singular

open _root_.OAI.AlgebraicTopology.Singular

variable [IsIntegral X.left] [Smooth X.hom]

/-- The augmentation `ℚ[0] → C^•` of the sheafified rational singular cochains on `X(ℂ)`, indexed
by integers. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation :
    (CochainComplex.singleFunctor (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℚ) ⟶
      _root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫
    HomologicalComplex.extendMap
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex ℚ (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
      ComplexShape.embeddingUpNat

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation_mono : Mono (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation X) := by
  dsimp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation]
  exact @mono_comp _ _ _ _ _ _ inferInstance _
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochainResolution.constantsToSingularCochainComplexInt_mono ℚ (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation_quasiIso : QuasiIso (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation X) := by
  dsimp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation]
  have : QuasiIso (HomologicalComplex.extendMap
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex ℚ (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr
      (_root_.OAI.AlgebraicTopology.Singular.SheafCochainResolution.constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X))
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' := this)

variable [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom]

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
/-- `H^n_Z(X(ℂ); ℚ) ≃ H^n(Γ_Z(X(ℂ), C^•))` for the sheafified rational singular cochains `C^•`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedSingularHomology (n : ℕ) :
    H_[Z]^n(X; ℚ) ≃+
      (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation ↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
        (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) Z.compl)).homology n :=
  letI : ∀ V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace V := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  @_root_.OAI.AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
    𝓒(↧(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℚ) (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
    (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex_isStrictlyGE _) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation_mono X) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation_quasiIso X)
    Z.compl ⊤ Z.compl (top_inf_eq _)
    (fun n => _root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex_isFlasque (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) n)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticHasExt X) n

end Singular

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cohomology.WithSupport
