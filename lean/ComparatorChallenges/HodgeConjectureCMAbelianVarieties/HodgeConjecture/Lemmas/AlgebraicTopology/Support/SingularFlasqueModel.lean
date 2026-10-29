/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularFlasqueModel

namespace OAI.AlgebraicTopology.Support.SingularFlasqueOn

/-!
# Constructions used only in proofs

These were built to prove the results about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularFlasqueModel`.
The statement of the conjecture never inspects them: every path from the statement to one
of them runs through a proof, so proof irrelevance makes their bodies immaterial.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex

section
namespace Singular

variable (X : TopCat.{0})

variable (hX : ∀ (x : X) (V : Opens X), x ∈ V →
  ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)

variable [T2Space X] [∀ V : Opens X, ParacompactSpace V]

/-- The comparison is a quasi-isomorphism on sections on every open set.
This stronger conclusion is essential for applying local normal-slice calculations. -/
theorem supportedSingularToInjectiveComplex_onOpen_quasiIso (U V : Opens X) :
    QuasiIso (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
      (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedSingularToInjectiveComplex X hX U)) :=
  _root_.OAI.AlgebraicTopology.Support.FlasqueComparison.TopCat.Sheaf.supportedSections_map_quasiIso_of_flasque X U V
    (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex X hX) 0 0 (fun _ => inferInstance) (fun _ => inferInstance)

/-- Let `X` be Hausdorff, with every open subset paracompact, and with a basis of contractible open
neighborhoods. Let `C` be the sheafified rational singular cochain complex and `I` an injective
resolution of the constant rational sheaf. For opens `U,V ⊆ X`, the augmentation-preserving
comparison `C → I` induces this isomorphism `H^n(Γ_{X \ U}(V,C)) ≅ H^n(Γ_{X \ U}(V,I))`. Here
supported sections on `V` are sections vanishing on `V ∩ U`, and `n` is any integer. -/
def supportedSingularInjectiveHomologyIso (U V : Opens X) (n : ℤ) :
    ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U))).homology n ≅
    ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (((_root_.OAI.AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
        (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalConstantInjectiveComplex X)))).homology n :=
  let f := ((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
    (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedSingularToInjectiveComplex X hX U)
  letI : QuasiIso f := supportedSingularToInjectiveComplex_onOpen_quasiIso X hX U V
  asIso (HomologicalComplex.homologyMap f n)

end Singular
end

end

end OAI.AlgebraicTopology.Support.SingularFlasqueOn
