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

import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.AnalyticDifferentialForms
import HodgeConjecture.Lemmas.Analysis.Calculus.DifferentialForm.HolomorphicPoincare
import HodgeConjecture.Mathlib.Analysis.NormedSpace.WedgeCovectors

import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI.AlgebraicGeometry.Hodge.HolomorphicPoincare

open _root_.AlgebraicGeometry

/-!
# The holomorphic Poincaré operator on a complex-point space

This file applies the holomorphic Poincaré lemma of
`HodgeConjecture.Lemmas.Analysis.Calculus.DifferentialForm.HolomorphicPoincare` to fixed-chart
evaluations of raw holomorphic forms on the analytic complex-point space of a complex scheme.
-/

noncomputable section

open _root_.ContinuousAlternatingMap _root_.MeasureTheory
open scoped ContDiff Interval

section
namespace ComplexPoint

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- For the analytic charted-space instance, `chartAt` is the algebraically constructed local
chart. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartAt_eq_localChart [SmoothOfRelativeDimension d X.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    chartAt (Fin d → ℂ) z = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z := rfl

/-- The change of coordinates from the chart at `z'` to the chart at `z`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition [SmoothOfRelativeDimension d X.hom]
    (z z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) : (Fin d → ℂ) → (Fin d → ℂ) :=
  fun y ↦ (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z)
    ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y)

/-- A fixed-chart transition is complex analytic wherever the two charts overlap. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (z z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) {y : Fin d → ℂ}
    (hy : y ∈ ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z').symm.trans
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z)).source) :
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z') y := by
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_transition X d z' z hy

/-- Expressions of a section in two overlapping fixed charts are related by the chart
transition. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z' f y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y) := by
  simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection, Function.comp_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition]
  rw [(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).left_inv hy]

/-- The coordinate derivatives of a section obey the chain rule under a fixed-chart
transition. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z')
    (hyz : (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z' f y =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z f
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y)).comp
          (fderiv ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z') y) := by
  have htransLocal : y ∈ ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z').symm.trans
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z)).source := by
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · change y ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z').target
      simpa only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
        ModelWithCorners.range_eq_univ, Set.inter_univ,
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartAt_eq_localChart X d] using hy.1
    · change (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z').symm y ∈
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).source
      simpa only [extChartAt_coe_symm, extChartAt_source,
        modelWithCornersSelf_coe_symm, Function.comp_id,
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartAt_eq_localChart X d] using hyz
  have hT : DifferentiableAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z') y :=
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_fixedChartTransition X d z z' htransLocal).differentiableAt
  have hTy : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z := by
    let ez := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
    let ez' := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z'
    refine ⟨ez.map_source hyz, ?_⟩
    change ez.symm (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y) ∈
      ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _)
    rw [show _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y = ez (ez'.symm y) from rfl,
      ez.left_inv hyz]
    exact hy.2
  have hf : DifferentiableAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y) :=
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffWithinAt X d U z f hTy).contDiffAt
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z).mem_nhds hTy)).differentiableAt (by simp)
  have heq : Filter.EventuallyEq (nhds y)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z' f)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f ∘ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z') := by
    filter_upwards [((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z').symm.trans
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z)).open_source.mem_nhds htransLocal] with w hw
    apply _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_fixedChartTransition X d U z z' f
    rw [OpenPartialHomeomorph.trans_source] at hw
    have hw2 := hw.2
    change (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z').symm w ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).source at hw2
    simpa only [extChartAt_coe_symm, extChartAt_source,
      modelWithCornersSelf_coe_symm, Function.comp_id,
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartAt_eq_localChart X d] using hw2
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential,
    fderivWithin_of_isOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z') hy,
    fderivWithin_of_isOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z) hTy,
    heq.fderiv_eq]
  exact fderiv_fun_comp y hf hT

/-- Evaluation of a differential form is covariant under a holomorphic fixed-chart
transition. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z')
    (hyz : (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z' p θ y =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y)).compContinuousLinearMap
          (fderiv ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z') y) := by
  have hTy : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z := by
    refine ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).map_source hyz, ?_⟩
    change (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y) ∈
        ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _)
    rw [show _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y =
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z)
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y) from rfl,
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).left_inv hyz]
    exact hy.2
  induction θ using _root_.OAI.Algebra.DeRham.Basic.mk_induction with
  | mk a₀ v =>
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U z' p a₀ v hy, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U z p a₀ v hTy]
      simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation]
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_fixedChartTransition X d U z z' a₀ hyz]
      have hd :
          (fun j ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z' (v j) y) =
          (fun j ↦ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (v j)
            (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y)).comp
              (fderiv ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z') y)) := by
        funext j
        exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_fixedChartTransition X d U z z' (v j) hy hyz
      rw [hd, _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_compContinuousLinearMap, _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.smul_compContinuousLinearMap]
  | zero =>
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_zero]
      exact ContinuousAlternatingMap.ext fun v ↦ by
        simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  | add a b ha hb =>
      simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_add, Pi.add_apply, ha, hb, _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.add_compContinuousLinearMap]
  | smul c a ha =>
      simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_smul, Pi.smul_apply, ha, _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.smul_compContinuousLinearMap]

/-- Vanishing throughout one fixed chart detects an analytic relation, provided
the open set lies in the source of that chart. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_of_chartEvaluation_eq_zero
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) :
      Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) ⊆
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p)
    (hθ : Set.EqOn (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ) 0
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    θ ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p := by
  apply (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X d U p _).2
  intro z' y hy
  have hyU := hy.2
  have hyz :
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source :=
    hsource hyU
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_fixedChartTransition X d U z z' p θ ⟨hy.1, hyU⟩ hyz]
  have hTy : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z := by
    let ez := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
    let ez' := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z'
    refine ⟨ez.map_source hyz, ?_⟩
    change ez.symm (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y) ∈
      ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _)
    rw [show _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.fixedChartTransition X d z z' y = ez (ez'.symm y) from rfl,
      ez.left_inv hyz]
    exact hyU
  rw [hθ hTy]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.contMDiffAt_chartFunction [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z))
    {q : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X} (hq : q ∈ Opposite.unop U) :
    ContMDiffAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (fun x ↦ a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) x)) q := by
  have hqsource := hsource hq
  have hcoord :
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q ∈
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z := by
    refine ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).map_source hqsource, ?_⟩
    change (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q) ∈
        ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _)
    rw [(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).left_inv hqsource]
    exact hq
  exact (ha _ hcoord).contDiffAt.contMDiffAt.comp q
    (contMDiffAt_extChartAt' (by
      rwa [← extChartAt_source (modelWithCornersSelf ℂ (Fin d → ℂ))]))

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.contMDiff_chartFunction [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    ContMDiff (modelWithCornersSelf ℂ (Fin d → ℂ)) (modelWithCornersSelf ℂ ℂ) ω
      (fun q : (Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) ↦
        a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q)) :=
  fun q ↦ (contMDiffAt_subtype_iff
    (I := modelWithCornersSelf ℂ (Fin d → ℂ))
    (I' := modelWithCornersSelf ℂ ℂ)
    (U := (Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
    (f := fun x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X ↦
      a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) x))
    (x := q)).mpr (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.contMDiffAt_chartFunction X d U z hsource a ha q.2)

/-- An analytic scalar function in one chart, regarded as a holomorphic section on the chart
source. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicSectionOfChart [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U :=
  (⟨fun q ↦ a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q),
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.contMDiff_chartFunction X d U z hsource a ha⟩ :
    C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)); ℂ⟯)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_holomorphicSectionOfChart [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z))
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicSectionOfChart X d U z hsource a ha) y = a y := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ hy]
  change a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z)
    ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) = a y
  rw [(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).right_inv hy.1]

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_holomorphicSectionOfChart
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z))
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicSectionOfChart X d U z hsource a ha) y =
      fderivWithin ℂ a (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y := by
  exact fderivWithin_congr'
    (fun w hw ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_holomorphicSectionOfChart X d U z hsource a ha hw) hy

/-- The `i`-th fixed-chart coordinate as a holomorphic section. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartCoordinateSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (i : Fin d) : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicSectionOfChart X d U z hsource
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).analyticOnNhd _)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_chartCoordinateSection
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (i : Fin d) {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartCoordinateSection X d U z hsource i) y =
      ContinuousLinearMap.proj i := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartCoordinateSection
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_holomorphicSectionOfChart X d U z hsource _ _ hy,
    fderivWithin_of_isOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z) hy]
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).hasFDerivAt.fderiv

/-- A finite differential form whose fixed-chart evaluation is a given analytic
alternating-form field. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formOfAnalyticField [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (p : ℕ) (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (hθ : AnalyticOnNhd ℂ θ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p :=
  ∑ I : Fin p → Fin d,
    _root_.OAI.Algebra.DeRham.Basic.mk ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicSectionOfChart X d U z hsource
        (_root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.coordinateCoefficient θ I)
        (_root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.analyticOnNhd_coordinateCoefficient θ hθ I))
      fun j ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartCoordinateSection X d U z hsource (I j)

/-- The finite realization of an analytic alternating-form field evaluates to that field in the
chosen chart. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_formOfAnalyticField
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hsource : ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (p : ℕ) (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (hθ : AnalyticOnNhd ℂ θ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    Set.EqOn (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formOfAnalyticField X d U z hsource p θ hθ)) θ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) := by
  intro y hy
  have hsum := map_sum (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationAt X d U z p y)
    (fun I : Fin p → Fin d => _root_.OAI.Algebra.DeRham.Basic.mk ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicSectionOfChart X d U z hsource
        (_root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.coordinateCoefficient θ I)
        (_root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.analyticOnNhd_coordinateCoefficient θ hθ I))
      fun j ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartCoordinateSection X d U z hsource (I j)) Finset.univ
  change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationAt X d U z p y
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formOfAnalyticField X d U z hsource p θ hθ) = _
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formOfAnalyticField, hsum]
  have hterm : ∀ I : Fin p → Fin d,
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationAt X d U z p y
        (_root_.OAI.Algebra.DeRham.Basic.mk ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicSectionOfChart X d U z hsource
            (_root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.coordinateCoefficient θ I)
            (_root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.analyticOnNhd_coordinateCoefficient θ hθ I))
          fun j ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartCoordinateSection X d U z hsource (I j)) =
      _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.coordinateCoefficient θ I y •
        _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) fun j ↦ ContinuousLinearMap.proj (I j) := by
    intro I
    change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p _ y = _
    rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U z p _ _ hy]
    simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation]
    rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_holomorphicSectionOfChart X d U z hsource _ _ hy]
    have hd : (fun j ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartCoordinateSection X d U z hsource (I j)) y) =
        fun j ↦ ContinuousLinearMap.proj (I j) := by
      funext j
      exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_chartCoordinateSection X d U z hsource _ hy
    rw [hd]
  simp_rw [hterm]
  exact (_root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.alternating_eq_sum_wedgeCovectors (θ y)).symm

/-- A holomorphic section is complex analytic in every fixed chart. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) :
    AnalyticOnNhd ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z).analyticOn_iff_analyticOnNhd.mp
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffOn X d U z f).analyticOn

/-- The coordinate differential of a holomorphic section is analytic. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartSectionDifferential
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) :
    AnalyticOnNhd ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z f)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) := by
  refine AnalyticOnNhd.congr (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartSection X d U z f).fderiv fun y hy ↦ ?_
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential,
    fderivWithin_of_isOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z) hy]

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartGeneratorEvaluation_apply
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a₀ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (w : Fin p → _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U)
    (v : Fin p → Fin d → ℂ) :
    AnalyticOnNhd ℂ
      (fun y ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation X d U z p a₀ w y v)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) := by
  let s := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z
  have hentry (i j : Fin p) : AnalyticOnNhd ℂ
      (fun y ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (w j) y (v i)) s :=
    (ContinuousLinearMap.apply ℂ ℂ (v i)).comp_analyticOnNhd
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartSectionDifferential X d U z (w j))
  have hprod (e : Equiv.Perm (Fin p)) : AnalyticOnNhd ℂ
      (fun y ↦ ∏ j : Fin p,
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (w (e j)) y (v j)) s :=
    Finset.univ.analyticOnNhd_fun_prod (fun j hj ↦ hentry j (e j))
  have hterm (e : Equiv.Perm (Fin p)) : AnalyticOnNhd ℂ
      (fun y ↦ (((e.sign : ℤ) : ℂ) * ∏ j : Fin p,
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (w (e j)) y (v j))) s := by
    convert (hprod e).const_smul (c := ((e.sign : ℤ) : ℂ)) using 1
  have hdet : AnalyticOnNhd ℂ
      (fun y ↦ ∑ e : Equiv.Perm (Fin p), (((e.sign : ℤ) : ℂ) * ∏ j : Fin p,
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (w (e j)) y (v j))) s :=
    Finset.univ.analyticOnNhd_fun_sum (fun e he ↦ hterm e)
  have hmul := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartSection X d U z a₀).mul hdet
  refine AnalyticOnNhd.congr (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z) hmul fun y _ ↦ ?_
  simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_apply_eq_det, Matrix.det_apply]
  apply congrArg (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z a₀ y * ·)
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  rfl

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartEvaluation_apply
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p)
    (v : Fin p → Fin d → ℂ) :
    AnalyticOnNhd ℂ (fun y ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ y v)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) := by
  induction θ using _root_.OAI.Algebra.DeRham.Basic.mk_induction with
  | mk a₀ w =>
      refine AnalyticOnNhd.congr (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z)
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartGeneratorEvaluation_apply X d U z p a₀ w v) fun y hy ↦ ?_
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U z p a₀ w hy]
  | zero =>
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_zero]
      exact analyticOnNhd_const
  | add a b ha hb =>
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_add]
      convert ha.add hb using 1
  | smul c a ha =>
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_smul]
      convert ha.const_smul (c := c) using 1

/-- A holomorphic form has an analytic fixed-chart evaluation. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartEvaluation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p) :
    AnalyticOnNhd ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) := by
  let s := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z
  let e (I : Fin p → Fin d) : Fin p → Fin d → ℂ := fun j ↦ Pi.single (I j) 1
  let W (I : Fin p → Fin d) :=
    _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) (fun j ↦ ContinuousLinearMap.proj (I j))
  let c : ℂ := ((Fintype.card (Fin p)).factorial : ℂ)⁻¹
  have hc (I : Fin p → Fin d) : AnalyticOnNhd ℂ
      (fun y ↦ c * _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ y (e I)) s := by
    convert (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartEvaluation_apply X d U z p θ (e I)).const_smul
      (c := c) using 1
  have hterm (I : Fin p → Fin d) : AnalyticOnNhd ℂ
      (fun y ↦ (c * _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ y (e I)) • W I) s :=
    (hc I).smul analyticOnNhd_const
  have hsum : AnalyticOnNhd ℂ
      (fun y ↦ ∑ I : Fin p → Fin d,
        (c * _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ y (e I)) • W I) s :=
    Finset.univ.analyticOnNhd_fun_sum (fun I hI ↦ hterm I)
  exact AnalyticOnNhd.congr (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z) hsum fun y _ ↦
    (_root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.alternating_eq_sum_wedgeCovectors (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ y)).symm

/-- Every open neighborhood contains a smaller neighborhood that is exactly a Euclidean ball in
the fixed chart at the chosen point. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_chartBall_le [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hxU : x ∈ Opposite.unop U) :
    ∃ (V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (_i : U ⟶ V)
      (r : ℝ),
      x ∈ Opposite.unop V ∧ 0 < r ∧
      ((Opposite.unop V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x).source ∧
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d V x =
        Metric.ball ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r := by
  let e := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d x
  have hxsource : x ∈ e.source := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d x
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' ((Opposite.unop U : Opens _) : Set _)) :=
    e.isOpen_inter_preimage_symm (Opposite.unop U).2
  have hximage : e x ∈ e.target ∩ e.symm ⁻¹' ((Opposite.unop U : Opens _) : Set _) := by
    refine ⟨e.map_source hxsource, ?_⟩
    rw [Set.mem_preimage, e.left_inv hxsource]
    exact hxU
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp (hopen.mem_nhds hximage)
  let Vo : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
    ⟨e.source ∩ e ⁻¹' Metric.ball (e x) r, e.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hxV : x ∈ Vo := ⟨hxsource, Metric.mem_ball_self hr⟩
  have hVU : Vo ≤ Opposite.unop U := by
    intro z hz
    have hzU : e.symm (e z) ∈ ((Opposite.unop U : Opens _) : Set _) := (hball hz.2).2
    rw [e.left_inv hz.1] at hzU
    exact hzU
  let V := Opposite.op Vo
  let i : U ⟶ V := (homOfLE hVU).op
  refine ⟨V, i, r, hxV, hr, ?_, ?_⟩
  · intro z hz
    simpa only [extChartAt_source, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartAt_eq_localChart X d] using hz.1
  · unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ, extChartAt_coe_symm, extChartAt_coe,
      Function.comp_id, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartAt_eq_localChart X d, modelWithCornersSelf_coe]
    dsimp only [V, Opposite.unop_op]
    change e.target ∩ e.symm ⁻¹' (Vo : Set _) = Metric.ball (e x) r
    ext y
    constructor
    · rintro ⟨hytarget, hysource, hyball⟩
      rw [Set.mem_preimage, e.right_inv hytarget] at hyball
      exact hyball
    · intro hy
      have hytarget : y ∈ e.target := (hball hy).1
      refine ⟨hytarget, e.map_target hytarget, ?_⟩
      rw [Set.mem_preimage, e.right_inv hytarget]
      exact hy

/-- Shrink a fixed chart ball to any smaller positive radius. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_smaller_chartBall [SmoothOfRelativeDimension d X.hom]
    (V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (r : ℝ)
    (hdom : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d V x =
      Metric.ball ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r)
    (ρ : NNReal) (hρ : 0 < ρ) (hρr : (ρ : ℝ) < r) :
    ∃ (W : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (_j : V ⟶ W),
      x ∈ Opposite.unop W ∧
      ((Opposite.unop W : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : Set _) ⊆
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x).source ∧
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d W x = Metric.ball
        ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) (ρ : ℝ) := by
  let e := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d x
  have hdom' : e.target ∩ e.symm ⁻¹' ((Opposite.unop V : Opens _) : Set _) =
      Metric.ball (e x) r := by
    unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain at hdom
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ, extChartAt_coe_symm, extChartAt_coe,
      Function.comp_id, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartAt_eq_localChart X d, modelWithCornersSelf_coe] at hdom
    exact hdom
  have hxsource : x ∈ e.source := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d x
  let Wo : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
    ⟨e.source ∩ e ⁻¹' Metric.ball (e x) (ρ : ℝ),
      e.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hxW : x ∈ Wo := ⟨hxsource, Metric.mem_ball_self (by exact_mod_cast hρ)⟩
  have hWV : Wo ≤ Opposite.unop V := by
    intro z hz
    have hezdom : e z ∈ e.target ∩ e.symm ⁻¹'
        ((Opposite.unop V : Opens _) : Set _) :=
      hdom'.symm ▸ Metric.ball_subset_ball hρr.le hz.2
    have hzV := hezdom.2
    rw [Set.mem_preimage, e.left_inv hz.1] at hzV
    exact hzV
  let W := Opposite.op Wo
  let j : V ⟶ W := (homOfLE hWV).op
  refine ⟨W, j, hxW, ?_, ?_⟩
  · intro z hz
    simpa only [extChartAt_source, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartAt_eq_localChart X d] using hz.1
  · unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ, extChartAt_coe_symm, extChartAt_coe,
      Function.comp_id, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartAt_eq_localChart X d, modelWithCornersSelf_coe]
    dsimp only [W, Opposite.unop_op]
    change e.target ∩ e.symm ⁻¹' (Wo : Set _) = Metric.ball (e x) (ρ : ℝ)
    ext y
    constructor
    · rintro ⟨hytarget, hysource, hyball⟩
      rw [Set.mem_preimage, e.right_inv hytarget] at hyball
      exact hyball
    · intro hy
      have hyr : y ∈ Metric.ball (e x) r := Metric.ball_subset_ball hρr.le hy
      have hytarget : y ∈ e.target := (hdom'.symm ▸ hyr).1
      refine ⟨hytarget, e.map_target hytarget, ?_⟩
      rw [Set.mem_preimage, e.right_inv hytarget]
      exact hy

/-- Every closed holomorphic form of positive degree is locally exact. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_local_holomorphicForm_primitive [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hxU : x ∈ Opposite.unop U) (p : ℕ)
    (form : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U (p + 1))
    (hclosed : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d U (p + 1) form = 0) :
    ∃ (W : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (k : U ⟶ W)
      (θ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d W p),
      x ∈ Opposite.unop W ∧
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d W p θ =
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d k (p + 1) form := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U (p + 1)) form
  have hrel : _root_.OAI.Algebra.DeRham.Basic.differential ℂ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (p + 1) a ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U (p + 2) := by
    change Submodule.Quotient.mk (_root_.OAI.Algebra.DeRham.Basic.differential ℂ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (p + 1) a) = 0 at hclosed
    rwa [Submodule.Quotient.mk_eq_zero] at hclosed
  obtain ⟨V, i, r, hxV, hr, hsourceV, hdomV⟩ :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_chartBall_le X d U x hxU
  let aV := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i (p + 1) a
  let η := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d V x (p + 1) aV
  have hη : AnalyticOnNhd ℂ η (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    rw [← hdomV]
    exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartEvaluation X d V x (p + 1) aV
  have hrelV : _root_.OAI.Algebra.DeRham.Basic.differential ℂ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d V) (p + 1) aV ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d V (p + 2) := by
    have h := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_mem_chartEvaluationKernel X d i (p + 2) hrel
    rwa [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_differential] at h
  have hclosedη : Set.EqOn (extDeriv η) 0 (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    intro y hy
    have hyV : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d V x := hdomV.symm ▸ hy
    have hchart : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d V x (p + 2)
        (_root_.OAI.Algebra.DeRham.Basic.differential ℂ
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d V) (p + 1) aV) y = 0 := by
      exact (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X d V (p + 2) _).1 hrelV x y hyV
    rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_differential X d V x (p + 1) aV hyV] at hchart
    have hwithin : extDerivWithin η (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d V x) y =
        extDeriv η y := by
      rw [extDerivWithin, extDeriv,
        fderivWithin_of_isOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d V x) hyV]
    rwa [hwithin] at hchart
  obtain ⟨ρ, hρ, hρr, θfield, hθfield, hprim⟩ :=
    _root_.OAI.Analysis.DifferentialForms.HolomorphicPoincare.DifferentialForm.exists_analyticOnNhd_primitive_on_smaller_centered_ball p hr η hη hclosedη
  obtain ⟨W, j, hxW, hsourceW, hdomW⟩ :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_smaller_chartBall X d V x r hdomV ρ hρ hρr
  have hθW : AnalyticOnNhd ℂ θfield (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d W x) := by
    rw [hdomW]
    exact hθfield
  let b := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formOfAnalyticField X d W x hsourceW p θfield hθW
  let θ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d W p := Submodule.Quotient.mk b
  refine ⟨W, i ≫ j, θ, hxW, ?_⟩
  apply (Submodule.Quotient.eq (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d W (p + 1))).2
  apply _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_of_chartEvaluation_eq_zero
    X d W x (p + 1) hsourceW
  intro y hy
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_sub, Pi.sub_apply,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_differential X d W x p b hy,
    extDerivWithin_congr'
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_formOfAnalyticField X d W x hsourceW p θfield hθW) hy]
  have hwithin : extDerivWithin θfield (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d W x) y =
      extDeriv θfield y := by
    rw [extDerivWithin, extDeriv,
      fderivWithin_of_isOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d W x) hy]
  rw [hwithin]
  have hyball : y ∈ Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) (ρ : ℝ) := hdomW ▸ hy
  rw [hprim hyball, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_comp, LinearMap.comp_apply,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_formRestriction X d j x (p + 1) aV hy]
  simp [η]

/-- In degree zero, the Kähler representative of a scalar evaluates to the constant alternating
map with that scalar value. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_ofConstant [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (c : ℂ) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U x) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U x 0
        (_root_.OAI.Algebra.DeRham.Basic.ofConstant ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) c) y =
      ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin d → ℂ) (Fin 0) c := by
  rw [_root_.OAI.Algebra.DeRham.Basic.ofConstant_apply, _root_.OAI.Algebra.DeRham.Basic.ofFunction_apply,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U x 0 _ _ hy]
  simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U x _ hy]
  change c • _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) Fin.elim0 = _
  ext v
  simp

/-- A closed holomorphic zero-form is locally the image of a complex constant. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_local_holomorphicForm_eq_constant [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hxU : x ∈ Opposite.unop U)
    (form : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U 0)
    (hclosed : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d U 0 form = 0) :
    ∃ (V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (i : U ⟶ V) (c : ℂ),
      x ∈ Opposite.unop V ∧
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i 0 form =
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d V c := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U 0) form
  have hrel : _root_.OAI.Algebra.DeRham.Basic.differential ℂ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) 0 a ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U 1 := by
    change Submodule.Quotient.mk (_root_.OAI.Algebra.DeRham.Basic.differential ℂ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) 0 a) = 0 at hclosed
    rwa [Submodule.Quotient.mk_eq_zero] at hclosed
  obtain ⟨V, i, r, hxV, hr, hsourceV, hdomV⟩ :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_chartBall_le X d U x hxU
  let aV := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i 0 a
  let η := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d V x 0 aV
  have hη : AnalyticOnNhd ℂ η (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    rw [← hdomV]
    exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticOnNhd_chartEvaluation X d V x 0 aV
  have hrelV : _root_.OAI.Algebra.DeRham.Basic.differential ℂ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d V) 0 aV ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d V 1 := by
    have h := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_mem_chartEvaluationKernel X d i 1 hrel
    rwa [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_differential] at h
  have hclosedη : Set.EqOn (extDeriv η) 0 (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    intro y hy
    have hyV : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d V x := hdomV.symm ▸ hy
    have hchart : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d V x 1
        (_root_.OAI.Algebra.DeRham.Basic.differential ℂ
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d V) 0 aV) y = 0 := by
      exact (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X d V 1 _).1 hrelV x y hyV
    rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_differential X d V x 0 aV hyV] at hchart
    have hwithin : extDerivWithin η (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d V x) y =
        extDeriv η y := by
      rw [extDerivWithin, extDeriv,
        fderivWithin_of_isOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d V x) hyV]
    rwa [hwithin] at hchart
  have hconst :=
    _root_.OAI.Analysis.DifferentialForms.HolomorphicPoincare.DifferentialForm.zeroForm_eq_at_center_of_closedOn_ball hr η hη hclosedη
  let center := (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x
  let c := _root_.OAI.Analysis.DifferentialForms.Poincare.DifferentialForm.zeroFormCoeff η center
  refine ⟨V, i, c, hxV, ?_⟩
  apply (Submodule.Quotient.eq (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d V 0)).2
  apply _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_of_chartEvaluation_eq_zero
    X d V x 0 hsourceV
  intro y hy
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_sub, Pi.sub_apply]
  have hyball' : y ∈ Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r := hdomV ▸ hy
  have hyball : y ∈ Metric.ball center r := by simpa only [center] using hyball'
  rw [show _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d V x 0 aV y = η center from hconst hyball]
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_ofConstant X d V x c hy]
  have hrepr := congrFun (_root_.OAI.Analysis.DifferentialForms.Poincare.DifferentialForm.zeroForm_eq_constOfIsEmpty η) center
  rw [hrepr]
  exact sub_self _

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Hodge.HolomorphicPoincare
