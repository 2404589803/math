/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SingularSectionNaturality
import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.CohomologySection

namespace OAI.AlgebraicTopology.Support.SingularCohomologySheafComparison

open scoped OAI.AlgebraicTopology.Support.RelativeCohomologySheaf.Singular

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# The supported singular cohomology sheaf and local relative cohomology

The restriction-natural local comparison is an isomorphism of presheaves, and exact
sheafification with its counit identifies the sheafification with the cohomology sheaf of
the kernel-defined supported singular complex. The local class and unit equations fix this
identification, including the positive short-exact-sequence lift normalization.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

universe u

namespace TopCat
open _root_.TopCat
namespace Sheaf
open _root_.TopCat
open _root_.TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The canonical evaluation/homology comparison respects open restriction. -/
@[reassoc]
lemma sectionCohomologyPresheafOnOpenIso_inv_naturality
    (n : ℤ) {V W : Opens X} (a : W ⟶ V) :
    (_root_.OAI.AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheaf X K n).map a.op ≫
      (_root_.OAI.AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso X K n W).inv =
    (_root_.OAI.AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso X K n V).inv ≫
      homologyMap (_root_.OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ K a) n := by
  let P : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
    ((forget AddCommGrpCat.{u} X).mapHomologicalComplex ℤᵘᵖ).obj K
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) := P.sc n
  change ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map a.op).app S.homology ≫
      (S.mapHomologyIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W))).inv =
    (S.mapHomologyIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))).inv ≫
      ShortComplex.homologyMap
        (S.mapNatTrans ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map a.op))
  rw [NatTrans.app_homology]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Sheaf
end TopCat

section
namespace Singular

open _root_.OAI.AlgebraicTopology.Support.SingularCohomologySheafComparison.TopCat.Sheaf

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
  (S : Set X) (hS : IsClosed S) (n : ℕ)

/-- Let `X` be a Hausdorff topological space whose every open subset is paracompact. Let `S ⊆ X` be
closed and `n` a natural number. This presheaf isomorphism identifies `V ↦ H^n(Γ(V, Γ_S(C^•)))`
with `V ↦ H^n(V, V \ S; ℚ)`. Here `C^•` is the sheafified rational singular cochain complex, and
`Γ_S` takes the subsheaves of sections vanishing off `S`. -/
def supportedSingularCohomologyPresheafIsoRelative :
    -- `V ↦ H^n_S(V; ℚ)` is the presheaf `V ↦ H^n(V, V \ S; ℚ)`.
    _root_.OAI.AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheaf X
      -- `Γ_S` of the singular-cochain sheaf complex.
      (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) ≅
        _root_.OAI.AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyPresheaf X S n :=
  NatIso.ofComponents (fun V =>
    (_root_.OAI.AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso X
      (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) V.unop).symm ≪≫
      (_root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V.unop n).toAddCommGrpIso) (by
    intro V W a
    apply ConcreteCategory.hom_ext
    intro z
    let K := _root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩
    change _root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS W.unop n
        ((_root_.OAI.AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso X K (n : ℤ) W.unop).inv
          ((_root_.OAI.AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheaf X K (n : ℤ)).map a z)) =
      _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n
        (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap
          (W := (W.unop : Set X)) (V := (V.unop : Set X)) (leOfHom a.unop) S)
        (_root_.OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V.unop n
          ((_root_.OAI.AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso X K (n : ℤ) V.unop).inv z))
    have h := ConcreteCategory.congr_hom
      (_root_.OAI.AlgebraicTopology.Support.SingularCohomologySheafComparison.TopCat.Sheaf.sectionCohomologyPresheafOnOpenIso_inv_naturality X K (n : ℤ) a.unop) z
    simp only [ConcreteCategory.comp_apply, Quiver.Hom.op_unop] at h
    rw [h]
    exact _root_.OAI.AlgebraicTopology.Support.SingularSectionNaturality.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality
      X S hS a.unop n _)

/-- Let `X` be a Hausdorff topological space whose every open subset is paracompact. Let `S ⊆ X` be
closed and `C^•` the sheafified rational singular cochain complex. The degree-`n` cohomology
sheaf of its subsheaves of sections supported in `S` is identified with the sheafification of `V
↦ H^n(V, V \ S; ℚ)`, rational relative singular cohomology. -/
def supportedSingularCohomologySheafIsoRelative :
    -- The `n`-th cohomology sheaf of `Γ_S(C^•_sing)`.
    (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X
      -- The open `X \ S`.
      ⟨Sᶜ, hS.isOpen_compl⟩).homology (n : ℤ) ≅
      𝓗_[S]^n(X; ℚ) :=
  (_root_.OAI.AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafSheafificationIso X
    (_root_.OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ)).symm ≪≫
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso
    (supportedSingularCohomologyPresheafIsoRelative X S hS n)

end Singular
end

end

end OAI.AlgebraicTopology.Support.SingularCohomologySheafComparison
