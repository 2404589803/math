/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SingularFlasqueModel
import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact

namespace OAI.AlgebraicGeometry.Cohomology.SupportedSingularModel

open _root_.AlgebraicGeometry

/-!
# Supported singular models on smooth projective complex varieties

The generic supported singular/injective comparison is specialized using the analytic
contractible neighborhoods and hereditary paracompactness of smooth projective analytifications.
Only the geometric scheme hypotheses remain. The target is the ambient injective complex used by
the derived rational support comparison.
-/

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace
open _root_.OAI.AlgebraicTopology.Singular

section
namespace ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom]

/-- Let `X` be a smooth integral complex scheme and `U ⊆ X(ℂ)` an analytic open. Write `C^•` for the
sheafified rational singular cochains and `ℚ → I^•` for the chosen injective resolution. This
map `Γ_{X(ℂ) \ U}(C^•) → Γ_{X(ℂ) \ U}(I^•)` restricts the augmentation-preserving resolution
comparison to subsheaves of sections vanishing on `U`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective
    (U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) :
    -- `Γ_{X(ℂ) \ U}` of the singular-cochain model, mapping to `Γ_{X(ℂ) \ U}(I^•)`.
    _root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) U ⟶
      ((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside
        -- `X(ℂ)`.
        (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) U).mapHomologicalComplex ℤᵘᵖ).obj
          -- The injective resolution `I^•` of `ℚ` on `X(ℂ)`.
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X) :=
  _root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedSingularToInjectiveComplex (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X) U

variable [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- The supported comparison is a sheaf quasi-isomorphism under
the usual smooth projective geometry hypotheses alone. -/
instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective_quasiIso
    (U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) :
    QuasiIso (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective X U) := by
  let : ∀ V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace V :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  exact _root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedSingularToInjectiveComplex_quasiIso
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X) U

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cohomology.SupportedSingularModel
