/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel

namespace OAI.AlgebraicGeometry.Cohomology.SupportedSingularHomology

open _root_.AlgebraicGeometry

/-!
# Supported singular models on smooth projective complex varieties

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel`.
-/

/-! ### Constructions used only in proofs -/

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace
open _root_.OAI.AlgebraicTopology.Singular

section
namespace ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `Y = X(ℂ)` its analytic topology. This
cochain map sends the sheafified rational singular cochain complex on `Y` to the chosen
injective resolution of the constant rational sheaf. It extends the identity on constant
cochains and uses local contractibility of `Y`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSingularToAmbientInjective :
    _root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X :=
  _root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X)

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSingularToAmbientInjective_quasiIso :
    QuasiIso (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSingularToAmbientInjective X) :=
  _root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex_quasiIso _ _

variable [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `Y = X(ℂ)` its analytic topology. Assume
also that `X` is projective, and let `U,V ⊆ Y` be open. The comparison from sheafified rational
singular cochains `C` to a constant-sheaf injective resolution `I` induces this isomorphism
`H^n(Γ_{Y \ U}(V,C)) ≅ H^n(Γ_{Y \ U}(V,I))` for every integer `n`. In each complex, sections
over `V` are required to vanish on `V ∩ U`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso
    (U V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℤ) :
    ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj
        (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) U))).homology n ≅
    ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj
        (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside
          (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) U).mapHomologicalComplex ℤᵘᵖ).obj
            (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)))).homology n :=
  letI : ∀ W : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace W :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  _root_.OAI.AlgebraicTopology.Support.SingularFlasqueOn.Singular.supportedSingularInjectiveHomologyIso (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X) U V n

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cohomology.SupportedSingularHomology
