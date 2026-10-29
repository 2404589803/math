/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

namespace OAI.AlgebraicTopology.LocalHomology.NormalProjectionTop

/-!
# Normal projections and the local support coclass

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.NormalProjectionCoclass`.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology

section
namespace Singular

variable {M : Type} [TopologicalSpace M]

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
  (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)

omit [NormedSpace ℝ E] in
theorem neighborhoodSupportInclusion_comp_chartNormalProjection
    {W V : Set M} (hWV : W ⊆ V) (hV : V ⊆ e.source) :
    _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap hWV S ≫ _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e S hS V hV =
      _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e S hS W (hWV.trans hV) := rfl

omit [NormedSpace ℝ E] in
/-- The chart coclass is compatible with neighborhood inclusion. -/
theorem chartNormalProjectionCoclass_restrict {W V : Set M} (hWV : W ⊆ V) (hV : V ⊆ e.source) :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * c) (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap hWV S)
      (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E c e S hS V hV) =
        _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E c e S hS W (hWV.trans hV) := by
  unfold _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp,
    neighborhoodSupportInclusion_comp_chartNormalProjection]

/-- On a zero-tangent fiber, the product radial compression has exactly the usual
normal radial compression, including its scale. -/
theorem univBall_zero_tangent_normal (a : E) (r : ℝ) (hr : 0 < r) (v : Fin c → ℂ) :
    (OpenPartialHomeomorph.univBall (a, (0 : Fin c → ℂ)) r (0, v)).2 =
      OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) r v := by
  rw [OpenPartialHomeomorph.univBall, dite_eq_left hr, OpenPartialHomeomorph.univBall, dite_eq_left hr]
  change (r • ((Real.sqrt (1 + ‖((0 : E), v)‖ ^ 2))⁻¹ • ((0 : E), v)) + (a, 0)).2 =
    r • ((Real.sqrt (1 + ‖v‖ ^ 2))⁻¹ • v) + 0
  simp

variable (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)

/-- The normal fiber, local pair homeomorphism, and normal projection compose to the standard
radial point-complement map, scale included. -/
theorem normalFiber_comp_chartNormalProjection :
    _root_.OAI.AlgebraicTopology.LocalHomology.NormalSlicePurity.Singular.normalSliceSection E c ≫ (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportPairIso E c e x hx S hS h0).hom ≫
      _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e S hS (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx)
        (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood_subset_source E c e x hx) =
      _root_.OAI.AlgebraicTopology.LocalHomology.CenteredComplexOrientation.Singular.centeredComplexEmbeddingPair c
        (OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportRadius E c e x hx))
        (_root_.OAI.AlgebraicTopology.LocalHomology.CenteredComplexOrientation.Singular.continuous_complexUnivBall c _ _) (_root_.OAI.AlgebraicTopology.LocalHomology.CenteredComplexOrientation.Singular.injective_complexUnivBall c _ _) 0 := by
  have hp (v : Fin c → ℂ) :
      (e (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportHomeomorph E c e x hx (0, v))).2 =
        OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportRadius E c e x hx) v := by
    rw [_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportHomeomorph_coordinates]
    have he : e x = ((e x).1, (0 : Fin c → ℂ)) := Prod.ext rfl h0
    rw [he]
    exact univBall_zero_tangent_normal E c _ _ (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportRadius_pos E c e x hx) v
  apply MorphismProperty.Arrow.Hom.ext
  · ext v
    apply Subtype.ext
    change (e (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportHomeomorph E c e x hx (0, v.1))).2 =
      OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportRadius E c e x hx) (v.1 + 0) -
        OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportRadius E c e x hx) 0
    simpa only [add_zero, OpenPartialHomeomorph.univBall_apply_zero, sub_zero] using hp v.1
  · ext v
    change Fin c → ℂ at v
    change (e (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportHomeomorph E c e x hx (0, v))).2 =
      OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportRadius E c e x hx) (v + 0) -
        OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportRadius E c e x hx) 0
    simpa only [add_zero, OpenPartialHomeomorph.univBall_apply_zero, sub_zero] using hp v

/-- The flattened-support normal class is the image of the fixed class on this normal
fiber. -/
theorem flattenedSupportNormalClass_eq_normalFiber :
    _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNormalClass E c e x hx S hS h0 =
      _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap ℚ (2 * c)
        (_root_.OAI.AlgebraicTopology.LocalHomology.NormalSlicePurity.Singular.normalSliceSection E c ≫ (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportPairIso E c e x hx S hS h0).hom)
        (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ c) := by aesop

/-- Normal projection sends the local normal class to the exactly normalized standard
class. -/
theorem chartNormalProjection_normalClass :
    _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap ℚ (2 * c)
      (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e S hS (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx)
        (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood_subset_source E c e x hx))
      (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNormalClass E c e x hx S hS h0) = _root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ c := by
  rw [flattenedSupportNormalClass_eq_normalFiber, ← LinearMap.comp_apply,
    ← _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap_comp, Category.assoc, normalFiber_comp_chartNormalProjection]
  exact _root_.OAI.AlgebraicTopology.LocalHomology.CenteredComplexOrientation.Singular.centeredComplexUnivBall_preserves_standardComplexLocalClass c _ _
    (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportRadius_pos E c e x hx) 0

/-- The chart-projection coclass has precisely the required normalization. -/
theorem chartNormalProjectionCoclass_apply_normalClass :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology ℚ
        (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx) S) (2 * c)
        (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E c e S hS (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx)
          (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood_subset_source E c e x hx))
      (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNormalClass E c e x hx S hS h0) = 1 := by
  simp [_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass, _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    _root_.OAI.AlgebraicGeometry.Cycle.LocalPurityOf.AlgebraicTopology.Singular.relativeCohomologyEquivDualHomology_normalizedRelativeCoclass,
    chartNormalProjection_normalClass, _root_.OAI.AlgebraicGeometry.Cycle.LocalPurityOf.AlgebraicTopology.Singular.normalizedDual_apply_self]

/-- Generation follows from the pair isomorphism and contraction. -/
theorem span_flattenedSupportNormalClass_eq_top :
    Submodule.span ℚ {_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNormalClass E c e x hx S hS h0} = ⊤ := by
  let eH := (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportRelativeHomologyIso E c e x hx S hS h0 (2 * c)).symm.toLinearEquiv
  have h := congrArg (Submodule.map eH.toLinearMap) (_root_.OAI.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator.Singular.span_standardComplexLocalClass_eq_top_for_chart c)
  rwa [Submodule.map_span, Set.image_singleton, Submodule.map_top, LinearEquiv.range] at h

include h0 in
/-- In top normal degree the normal projection is injective, by the pair computation and its
exact normalization. -/
theorem chartNormalProjection_relativeHomologyMap_injective :
    Function.Injective (_root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap ℚ (2 * c)
      (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e S hS (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx)
        (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood_subset_source E c e x hx))) := by
  intro v w hvw
  have hg := (Submodule.span_singleton_eq_top_iff ℚ
    (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNormalClass E c e x hx S hS h0)).mp
    (span_flattenedSupportNormalClass_eq_top E c e S hS x hx h0)
  obtain ⟨r, rfl⟩ := hg v
  obtain ⟨s, rfl⟩ := hg w
  rw [map_smul, map_smul, chartNormalProjection_normalClass] at hvw
  rw [smul_left_injective ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator.Singular.standardComplexLocalClass_ne_zero_for_chart c) hvw]

/-- A local supported coclass equals the normal-projection coclass precisely when
it evaluates to one on the normal class. -/
theorem chartNormalProjectionCoclass_unique
    (α : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
      (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx) S) (2 * c))
    (hα : _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology ℚ
        (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx) S) (2 * c) α
      (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNormalClass E c e x hx S hS h0) = 1) :
    α = _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E c e S hS (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx)
      (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood_subset_source E c e x hx) := by
  have hne : _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNormalClass E c e x hx S hS h0 ≠ 0 := by
    intro hz
    have h := chartNormalProjectionCoclass_apply_normalClass E c e S hS x hx h0
    rw [hz, map_zero] at h
    exact zero_ne_one h
  exact (_root_.OAI.AlgebraicGeometry.Cycle.LocalPurityOf.AlgebraicTopology.Singular.normalizedRelativeCoclass_unique hne
      (span_flattenedSupportNormalClass_eq_top E c e S hS x hx h0) α hα).trans
    (_root_.OAI.AlgebraicGeometry.Cycle.LocalPurityOf.AlgebraicTopology.Singular.normalizedRelativeCoclass_unique hne
      (span_flattenedSupportNormalClass_eq_top E c e S hS x hx h0) _
      (chartNormalProjectionCoclass_apply_normalClass E c e S hS x hx h0)).symm

end Singular
end

end

end OAI.AlgebraicTopology.LocalHomology.NormalProjectionTop
