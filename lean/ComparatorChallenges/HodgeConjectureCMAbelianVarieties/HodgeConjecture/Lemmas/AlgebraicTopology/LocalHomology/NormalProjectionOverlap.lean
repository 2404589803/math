/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionCoclass
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition

namespace OAI.AlgebraicTopology.LocalHomology.NormalProjectionOverlap

/-!
# Normal fibers and ambient overlap compatibility

Normal fibers factor both normal projections through maps of point-complement
pairs. Complex orientation invariance of the normal transition therefore gives agreement
of the ambient supported coclasses, not just an abstract transverse comparison.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology

section
namespace Singular

section Transverse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (c : ℕ) (t : OpenPartialHomeomorph (E × (Fin c → ℂ)) (E × (Fin c → ℂ)))
  (a : E) (ha : (a, 0) ∈ t.source)
  (hp : ∀ p ∈ t.source, (t p).2 = 0 ↔ p.2 = 0)
  (ht : AnalyticAt ℂ t (a, 0)) (hti : AnalyticAt ℂ t.symm (t (a, 0)))

include ha hp ht hti in
/-- Exact normal orientation invariance can be obtained inside any prescribed open
normal neighborhood. This permits the transverse pair map to land in a chosen
common ambient neighborhood. -/
theorem exists_open_normalTransition_localClass_invariance_within
    (U : Set (Fin c → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    (hUt : U ⊆ _root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionDomain c t a) :
    ∃ (V : Set (Fin c → ℂ)) (hV : V ⊆ U)
      (hne : ∀ v, v ∈ V → v ≠ 0 → _root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap c t a v ≠ 0),
      IsOpen V ∧ 0 ∈ V ∧
      ∀ z : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.Singular.RelativePairExcision.neighborhoodPointComplementPair V 0) (2 * c),
        _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap ℚ (2 * c) (_root_.OAI.AlgebraicTopology.Singular.RelativePairExcision.neighborhoodPointComplementPairMap V 0) z =
          _root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ c →
        _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap ℚ (2 * c)
          (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClassDifferentiableInvariance.Singular.complexNeighborhoodPuncturedPairMapOf c V (_root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap c t a)
            ((_root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap_continuousOn c t a).mono (hV.trans hUt))
            hne) z = _root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ c := by
  let L := _root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionDerivativeEquiv t a ha hp ht hti
  let A := _root_.OAI.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance.Singular.complexMatrixOfContinuousLinearMap c L.toContinuousLinearMap
  have hA := _root_.OAI.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance.Singular.complexMatrixOfContinuousLinearMap_det_ne_zero c L.toContinuousLinearMap L.injective
  have hAL : (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) =
      L.toContinuousLinearMap :=
    ContinuousLinearMap.ext (_root_.OAI.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance.Singular.complexMatrixOfContinuousLinearMap_mulVec c L.toContinuousLinearMap)
  apply _root_.OAI.AlgebraicTopology.LocalHomology.ComplexClassDifferentiableInvariance.Singular.exists_open_complexDifferentiable_localClass_invariance c A hA U hU h0U
    (_root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap c t a) ((_root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap_continuousOn c t a).mono hUt)
    (_root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap_zero c t a ha hp)
  rw [hAL]
  exact _root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransition_hasFDerivAt t a ha hp ht hti

end Transverse

section Fiber

variable {M E : Type} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (c : ℕ) (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
  (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
  (a : E) (W : Set M) (V : Set (Fin c → ℂ))
  (hV : ∀ v ∈ V, (a, v) ∈ e.target ∧ e.symm (a, v) ∈ W)

/-- Let `e` be a chart on a topological space `M` with values in `E × ℂ^c`, identifying a subset `S`
with the locus where the second coordinate is zero. Fix `a ∈ E`, `W ⊆ M`, and `V ⊆ ℂ^c` such
that `(a,v)` lies in the chart target and `e⁻¹(a,v) ∈ W` for every `v ∈ V`. This map of pairs
`(V,V \ {0}) → (W,W \ S)` sends `v` to `e⁻¹(a,v)`. -/
def chartNormalFiberPair :
    _root_.OAI.AlgebraicTopology.Singular.RelativePairExcision.neighborhoodPointComplementPair V 0 ⟶ _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair W S :=
  have hc : Continuous (fun v : V => e.symm (a, v.1)) :=
    e.symm.continuousOn.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun v => (hV v.1 v.2).1)
  have hn (v : {v : V | v.1 ≠ 0}) : e.symm (a, v.1.1) ∉ S := by
    intro hs
    have hz := (hS _ (e.map_target (hV v.1.1 v.1.2).1)).mp hs
    rw [e.right_inv (hV v.1.1 v.1.2).1] at hz
    exact v.2 hz
  TopPair.ofHom
    (TopCat.ofHom ⟨fun v => ⟨e.symm (a, v.1), (hV v.1 v.2).2⟩, hc.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun v => ⟨⟨e.symm (a, v.1.1), (hV v.1.1 v.1.2).2⟩, hn v⟩,
      (hc.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _⟩) (by ext v; rfl)

omit [NormedSpace ℝ E] in
/-- In the chart used to define the fiber, normal projection is inclusion. -/
theorem chartNormalFiber_comp_projection (hW : W ⊆ e.source) :
    chartNormalFiberPair c e S hS a W V hV ≫ _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e S hS W hW =
      _root_.OAI.AlgebraicTopology.Singular.RelativePairExcision.neighborhoodPointComplementPairMap V 0 := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext v
    apply Subtype.ext
    exact congrArg Prod.snd (e.right_inv (hV v.1.1 v.1.2).1)
  · ext v
    exact congrArg Prod.snd (e.right_inv (hV v.1 v.2).1)

omit [NormedSpace ℝ E] in
/-- In a second chart, normal projection of the same fiber is the normal transition map. -/
theorem chartNormalFiber_comp_other_projection
    (e' : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (hS' : ∀ y ∈ e'.source, y ∈ S ↔ (e' y).2 = 0) (hW' : W ⊆ e'.source)
    (hf : ContinuousOn (_root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap c (e.symm.trans e') a) V)
    (hne : ∀ v, v ∈ V → v ≠ 0 → _root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap c (e.symm.trans e') a v ≠ 0) :
    chartNormalFiberPair c e S hS a W V hV ≫ _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e' S hS' W hW' =
      _root_.OAI.AlgebraicTopology.LocalHomology.ComplexClassDifferentiableInvariance.Singular.complexNeighborhoodPuncturedPairMapOf c V (_root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap c (e.symm.trans e') a)
        hf hne := rfl

end Fiber

section Overlap

variable {M E : Type} [TopologicalSpace M] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E]
  (c : ℕ) (e e' : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
  (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
  (hS' : ∀ y ∈ e'.source, y ∈ S ↔ (e' y).2 = 0)
  (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)

include hS hS' in
omit [NormedSpace ℝ E] [NormedSpace ℂ E] in
/-- Flattening the same support proves the zero-plane criterion for the transition. -/
theorem supportChartTransition_preserves_plane (v : E × (Fin c → ℂ))
    (hv : v ∈ (e.symm.trans e').source) :
    (e.symm.trans e' v).2 = 0 ↔ v.2 = 0 := by
  have h1 := hS (e.symm v) (e.map_target hv.1)
  rw [e.right_inv hv.1] at h1
  exact (hS' (e.symm v) hv.2).symm.trans h1

include h0 in
/-- On a modeled ambient neighborhood contained in both chart sources, the
normal-projection coclasses agree. The proof factors both projections through the same
normal fiber and uses the complex normal-transition orientation theorem. -/
theorem chartNormalProjectionCoclass_eq_on_flattenedNeighborhood
    (hW' : (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx : Set M) ⊆ e'.source)
    (ht : AnalyticAt ℂ (e.symm.trans e') (e x))
    (hti : AnalyticAt ℂ (e.symm.trans e').symm ((e.symm.trans e') (e x))) :
    _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E c e S hS (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx)
      (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood_subset_source E c e x hx) =
    _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E c e' S hS' (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx) hW' := by
  let W := _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c e x hx
  let a := (e x).1
  let t := e.symm.trans e'
  have hex : e x = (a, (0 : Fin c → ℂ)) := Prod.ext rfl h0
  have h0t : (a, 0) ∈ t.source := by
    rw [← hex]
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rw [e.left_inv hx]
    exact hW' (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.mem_flattenedSupportNeighborhood E c e x hx)
  have hp := supportChartTransition_preserves_plane c e e' S hS hS'
  have hta : AnalyticAt ℂ t (a, 0) := hex ▸ ht
  have htia : AnalyticAt ℂ t.symm (t (a, 0)) := hex ▸ hti
  let U : Set (Fin c → ℂ) := {v | (a, v) ∈ e.target ∧ e.symm (a, v) ∈ W}
  have hU : IsOpen U :=
    (e.isOpen_inter_preimage_symm W.isOpen).preimage (continuous_const.prodMk continuous_id)
  have h0U : 0 ∈ U := by
    change (a, 0) ∈ e.target ∧ e.symm (a, 0) ∈ W
    rw [← hex, e.left_inv hx]
    exact ⟨e.map_source hx, _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.mem_flattenedSupportNeighborhood E c e x hx⟩
  have hUt : U ⊆ _root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionDomain c t a := fun _ hv => ⟨hv.1, hW' hv.2⟩
  obtain ⟨V, hV, hne, hVo, h0V, hclass⟩ :=
    exists_open_normalTransition_localClass_invariance_within c t a h0t hp hta htia U hU h0U hUt
  have hfiber : ∀ v ∈ V, (a, v) ∈ e.target ∧ e.symm (a, v) ∈ W := fun _ hv => hV hv
  let F := chartNormalFiberPair c e S hS a W V hfiber
  obtain ⟨z, hz⟩ := (_root_.OAI.AlgebraicTopology.Singular.RelativePairExcision.neighborhoodPointComplement_relativeHomologyMap_bijective
    V 0 hVo h0V (2 * c)).2 (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ c)
  have hFz : _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap ℚ (2 * c) F z =
      _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNormalClass E c e x hx S hS h0 := by
    apply _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionTop.Singular.chartNormalProjection_relativeHomologyMap_injective E c e S hS x hx h0
    rw [_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionTop.Singular.chartNormalProjection_normalClass, ← LinearMap.comp_apply, ← _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap_comp]
    change _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap ℚ (2 * c)
      (chartNormalFiberPair c e S hS a W V hfiber ≫ _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e S hS W _) z = _
    rw [chartNormalFiber_comp_projection]
    exact hz
  have hvalue : _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology ℚ
      (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set M) S) (2 * c)
      (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E c e' S hS' W hW')
      (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNormalClass E c e x hx S hS h0) = 1 := by
    rw [← hFz, _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass,
      _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyEquivDualHomology_relativeCohomologyMap,
      _root_.OAI.AlgebraicGeometry.Cycle.LocalPurityOf.AlgebraicTopology.Singular.relativeCohomologyEquivDualHomology_normalizedRelativeCoclass,
      ← LinearMap.comp_apply (_root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap ℚ (2 * c)
      (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e' S hS' W hW')), ← _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap_comp]
    change _root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedDual (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ c)
        (_root_.OAI.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator.Singular.standardComplexLocalClass_ne_zero_for_chart c)
      (_root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeHomologyMap ℚ (2 * c)
        (chartNormalFiberPair c e S hS a W V hfiber ≫ _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E c e' S hS' W hW') z) = 1
    rw [chartNormalFiber_comp_other_projection c e S hS a W V hfiber e' hS' hW'
      ((_root_.OAI.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition.Singular.normalTransitionMap_continuousOn c t a).mono (hV.trans hUt))
      hne, hclass z hz, _root_.OAI.AlgebraicGeometry.Cycle.LocalPurityOf.AlgebraicTopology.Singular.normalizedDual_apply_self]
  exact (_root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionTop.Singular.chartNormalProjectionCoclass_unique E c e S hS x hx h0 _ hvalue).symm

include hx h0 in
/-- Ambient overlap agreement on a sufficiently small common open neighborhood. The local class
is the one built by the normal pair model, and the proof checks its exact transition
normalization. -/
theorem exists_open_chartNormalProjectionCoclass_eq (hx' : x ∈ e'.source)
    (ht : AnalyticAt ℂ (e.symm.trans e') (e x))
    (hti : AnalyticAt ℂ (e.symm.trans e').symm ((e.symm.trans e') (e x))) :
    ∃ (W : TopologicalSpace.Opens M) (hW : (W : Set M) ⊆ e.source)
      (hW' : (W : Set M) ⊆ e'.source), x ∈ W ∧
      _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E c e S hS W hW =
        _root_.OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E c e' S hS' W hW' := by
  let er := e.restrOpen e'.source e'.open_source
  have hxr : x ∈ er.source := ⟨hx, hx'⟩
  have hSr : ∀ y ∈ er.source, y ∈ S ↔ (er y).2 = 0 := fun y hy => hS y hy.1
  let W := _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood E c er x hxr
  have hWr := _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood_subset_source E c er x hxr
  have hW : (W : Set M) ⊆ e.source := fun _ hy => (hWr hy).1
  have hW' : (W : Set M) ⊆ e'.source := fun _ hy => (hWr hy).2
  exact ⟨W, hW, hW', _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.mem_flattenedSupportNeighborhood E c er x hxr,
    chartNormalProjectionCoclass_eq_on_flattenedNeighborhood c er e' S hSr hS' x hxr h0 hW' ht hti⟩

end Overlap

end Singular
end

end

end OAI.AlgebraicTopology.LocalHomology.NormalProjectionOverlap
