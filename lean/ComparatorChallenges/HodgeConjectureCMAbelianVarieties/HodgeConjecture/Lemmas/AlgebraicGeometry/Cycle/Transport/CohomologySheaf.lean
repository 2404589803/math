/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.CohomologySheaf

namespace OAI.AlgebraicGeometry.Cycle.TransportCohomologySection

open _root_.AlgebraicGeometry

/-!
# Cohomology-sheaf concentration for smooth closed supports

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.CohomologySheaf`.
-/

/-! ### Constructions used only in proofs -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace Opposite

section
namespace ComplexPoint

open _root_.OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- Let `X` be a smooth integral projective scheme over `ℂ`, `Y = X(ℂ)` with its analytic topology,
`S ⊆ Y` closed, and `V ⊆ Y` open. For an injective resolution `I` of the constant rational
sheaf, this additive equivalence identifies `H^n(Γ_S(V,I))` with relative singular cohomology
`H^n(V,V \ S;ℚ)`. Here `Γ_S(V,I^q)` consists of sections over `V` that vanish off `S`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv (S : Closeds (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
    (V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ) :
    ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S))).homology (n : ℤ) ≃+
        _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
          (V : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (S : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))) n :=
  letI : ∀ W : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace W := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)).symm.addCommGroupIsoToAddEquiv
    |>.trans (_root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) S S.isClosed V n)

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.TransportCohomologySection
