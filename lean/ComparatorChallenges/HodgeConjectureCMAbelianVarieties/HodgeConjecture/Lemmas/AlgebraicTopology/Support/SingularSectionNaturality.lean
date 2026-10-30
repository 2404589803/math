/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SectionRestrictionConeNaturality
import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularSectionCohomology
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainOpenConeNaturality
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf

namespace OAI.AlgebraicTopology.Support.SingularSectionNaturality

/-! # Naturality of supported singular-section relative cohomology -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

section
namespace Singular

open _root_.TopCat.Sheaf

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
  (U : Opens X) {V W : Opens X} (a : W ⟶ V)

/-- Let `X` be Hausdorff with every open subset paracompact, and let `U,V ⊆ X` be open. Write `C^•`
for sheafified rational singular cochains. This identifies `H^n(Γ(V, Γ_{X \ U}(C^•)))` with
`H^{n-1}(Cone(C^•(V) → C^•(V ∩ U)))`, using the inclusion of the kernel of restriction and
extension to integer degrees. -/
def supportedSingularSectionConeHomologyIso (V : Opens X) (n : ℤ) :
    ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U))).homology n ≅
        (_root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openSingularSheafRestrictionCone ℚ X (Opens.infLELeft V U)).homology (n - 1) :=
  _root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex X)
    (fun _ => inferInstance) n ≪≫
  HomologicalComplex.homologyMapIso (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ X) (Opens.infLELeft V U)) (n - 1)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supported kernel-to-singular-cone comparison respects open restriction. -/
@[reassoc]
lemma supportedSingularSectionConeHomologyIso_naturality (n : ℤ) :
    HomologicalComplex.homologyMap
      (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U) a) n ≫
      (supportedSingularSectionConeHomologyIso X U W n).hom =
    (supportedSingularSectionConeHomologyIso X U V n).hom ≫
      HomologicalComplex.homologyMap
        (_root_.OAI.AlgebraicTopology.Singular.CochainOpenConeNaturality.openSingularSheafRestrictionConeMap ℚ X (Opens.infLELeft V U) (Opens.infLELeft W U)
          a (homOfLE (inf_le_inf_right U (leOfHom a)))) (n - 1) := by
  dsimp only [supportedSingularSectionConeHomologyIso, Iso.trans_hom]
  change HomologicalComplex.homologyMap
      (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionConeNaturality.TopCat.Sheaf.supportRestrictionSectionsComplexMap X U (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex X) a).τ₁ n ≫
      ((_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U W (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex X)
        (fun _ => inferInstance) n).hom ≫ _) = _
  rw [_root_.OAI.AlgebraicTopology.Support.SectionRestrictionConeNaturality.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone_naturality_assoc X U
    (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex X) a]
  simp only [Category.assoc]
  congr 1
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ (n - 1)
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp]
  exact congrArg H.map (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionConeNaturality.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso_naturality X
    (_root_.OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ X) (Opens.infLELeft V U) (Opens.infLELeft W U)
    a (homOfLE (inf_le_inf_right U (leOfHom a))))

/-- Restriction naturality of the whole supported-section-to-relative equivalence. -/
lemma supportedRationalSingularSectionCohomologyEquivRelative_naturality
    (n : ℕ)
    (z : ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U))).homology (n : ℤ)) :
    _root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative X U W n
      (HomologicalComplex.homologyMap
        (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U) a)
          (n : ℤ) z) =
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n
      (_root_.OAI.AlgebraicTopology.Singular.CochainOpenConeNaturality.openInclusionPairMap X (Opens.infLELeft V U) (Opens.infLELeft W U)
        a (homOfLE (inf_le_inf_right U (leOfHom a))))
      (_root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative X U V n z) := by
  change _root_.OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openSingularSheafRestrictionConeCohomologyEquivRelative X (Opens.infLELeft W U) n
      ((supportedSingularSectionConeHomologyIso X U W (n : ℤ)).hom
        (HomologicalComplex.homologyMap
          (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U) a)
            (n : ℤ) z)) = _
  have h := congrArg (fun f => f z)
    (supportedSingularSectionConeHomologyIso_naturality X U a (n : ℤ))
  change (supportedSingularSectionConeHomologyIso X U W (n : ℤ)).hom
      (HomologicalComplex.homologyMap
        (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U) a)
          (n : ℤ) z) =
    HomologicalComplex.homologyMap
      (_root_.OAI.AlgebraicTopology.Singular.CochainOpenConeNaturality.openSingularSheafRestrictionConeMap ℚ X (Opens.infLELeft V U) (Opens.infLELeft W U)
        a (homOfLE (inf_le_inf_right U (leOfHom a)))) ((n : ℤ) - 1)
      ((supportedSingularSectionConeHomologyIso X U V (n : ℤ)).hom z) at h
  rw [h]
  exact _root_.OAI.AlgebraicTopology.Singular.CochainOpenConeNaturality.openSingularSheafRestrictionConeCohomologyEquivRelative_naturality X
    (Opens.infLELeft V U) (Opens.infLELeft W U) a
    (homOfLE (inf_le_inf_right U (leOfHom a))) n _

/-- The final support-complement comparison preserves ambient-open restrictions. -/
lemma supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality
    (S : Set X) (hS : IsClosed S) {V W : Opens X} (a : W ⟶ V) (n : ℕ)
    (z : ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ)) :
    _root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS W n
      (HomologicalComplex.homologyMap
        (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
          (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) a) (n : ℤ) z) =
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n
      (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap
        (W := (W : Set X)) (V := (V : Set X)) (leOfHom a) S)
      (_root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n z) := by
  change _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n (_root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.openIntersectionPairIsoSupportComplement X S hS W).inv
      (_root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative X _ W n _) =
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n _
      (_root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n (_root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.openIntersectionPairIsoSupportComplement X S hS V).inv
        (_root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative X _ V n z))
  rw [supportedRationalSingularSectionCohomologyEquivRelative_naturality,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp,
    ← _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp]
  congr 2

end Singular
end

end

end OAI.AlgebraicTopology.Support.SingularSectionNaturality
