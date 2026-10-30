/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.OpenTransport
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenRestrictedVanishing

namespace OAI.AlgebraicGeometry.Stratification.LocalSupportVanishing

open _root_.AlgebraicGeometry

/-!
# Local support vanishing on canonical singular-filtration layers

Every point of a smooth layer has a fixed-dimensional affine source neighborhood, of
dimension strictly less than that of the original cycle component. Deleting the image of
the discarded source complement makes that neighborhood closed in a smaller ambient open,
and normal neighborhoods there transport to the original projective ambient space and its
fixed supported injective resolution. The local lower vanishing follows from those maps
and the dimension bounds.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace

section
namespace ComplexPoint

open _root_.OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p) (k : ℕ)

include hx in
/-- Every point in the `k`th layer has cofinal ambient neighborhoods
whose relative cohomology below degree `2(p+1)` vanishes. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayer_exists_relativeCohomology_vanishing
    (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k)
    (hyNext : y ∉ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1))
    (V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), W ≤ V ∧
      W ≤ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl ∧
      y ∈ W ∧ ∀ n : ℕ, n < 2 * (p + 1) →
        IsZero (ModuleCat.of ℚ (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
          (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
            (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))) n)) := by
  obtain ⟨z, rfl⟩ := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_layer X x k).ge ⟨hy, hyNext⟩
  let O := _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k
  let OX := _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver X x k
  let Y := _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOver X x k
  let i : Y ⟶ OX := _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLiftOver X x k
  obtain ⟨A, hA, hzA, m, hm, hcodim, hdim⟩ :=
    _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum_exists_smooth_relativeDimension
      X x hx k z.underlying
  let : SmoothOfRelativeDimension m (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A).hom := hdim
  let zA := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.asOpenPoint Y A z hzA
  let f := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X O)
  have hS : f ⁻¹'
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) =
        Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i) :=
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularStratumClosedLift_complexPoints_range X x k).symm
  have he : f (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion Y A ≫ i) zA) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOverι X x k) z := by
    apply Over.OverMorphism.ext
    change (zA.left ≫ (A.ι ≫ _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k)) ≫ O.ι =
      z.left ≫ _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k
    rw [Category.assoc, Category.assoc, _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift_ι,
      ← Category.assoc]
    exact congrArg (fun g => g ≫ _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.liftToOpen_fac Y A z hzA)
  let V' := V ⊓ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl
  have hzV' : f (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion Y A ≫ i) zA) ∈ V' := by
    rw [he]
    exact ⟨hyV, hyNext⟩
  have : SmoothOfRelativeDimension (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) OX.hom := by
    change SmoothOfRelativeDimension (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) O.ι X.hom
  obtain ⟨W, hWV', hzW, hW⟩ := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_smoothClosedSourceOpenImageNeighborhood
    OX Y i m (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) f (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpenEmbedding_map_open X O)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
    hS A zA V' hzV'
  exact ⟨W, hWV'.trans inf_le_left, hWV'.trans inf_le_right, he ▸ hzW,
    fun n hn ↦ hW n (by omega)⟩

include hx in
/-- The original ambient supported injective complex has cofinally vanishing section
cohomology below `2(p+1)` at every point outside the next closed support. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1))
    (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hyNext : y ∉ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1))
    (V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), W ≤ V ∧ y ∈ W ∧
      IsZero ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) W).mapHomologicalComplex
        ℤᵘᵖ).obj (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) V).map_isZero
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k
    · obtain ⟨W, hWV, _, hyW, hW⟩ :=
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayer_exists_relativeCohomology_vanishing X x hx k
          y hy hyNext V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
          (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
            (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k) W q
      let : Subsingleton ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
          (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) W).mapHomologicalComplex ℤᵘᵖ).obj
            (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
              (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k))).homology (q : ℤ)) :=
        e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact _root_.OAI.AlgebraicTopology.Support.SectionRestrictionIs.TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k).compl W
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

include hx in
/-- The open-layer section complex needed by finite support localization has zero cohomology
below `2(p+1)`. The resolution remains the one on the original projective ambient variety. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayerSectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl).mapHomologicalComplex
        ℤᵘᵖ).obj (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  apply _root_.OAI.AlgebraicTopology.Sheaf.OpenRestrictedVanishing.TopCat.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) _ _ 0 n
  · exact fun j ↦ _root_.OAI.AlgebraicTopology.Support.FlasqueSections.TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k).compl
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).X j)
  · exact fun j hj y hy V hyV ↦
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
        X x hx k j (hj.trans_lt hn) y hy V hyV

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Stratification.LocalSupportVanishing
