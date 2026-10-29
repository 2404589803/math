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

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Homotopy.Contractible

import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Complex

namespace OAI.AlgebraicGeometry.ComplexPoint.Manifold

open _root_.AlgebraicGeometry

/-!
# The topological manifold of complex points

If a complex scheme is smooth of relative dimension `d`, its analytic complex-point
space is locally homeomorphic to `ℂ^d`. This file turns the chosen algebraic étale coordinates into
a `ChartedSpace (Fin d → ℂ)` structure and proves that its transition maps are
holomorphic. So the complex points form a complex-analytic manifold of complex dimension `d`, in
particular a topological manifold of real dimension `2 * d`; both structures are instances.

The charts are not extra input. At a complex point we choose the affine étale coordinates supplied
by relative-dimensional smoothness, take a local inverse for that local homeomorphism, and
extend that chart from the corresponding analytic open subset to the ambient space.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff

section
section

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- The analytic open subset on which the chosen coordinates at `z` are defined. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhood [SmoothOfRelativeDimension d X.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
  {w : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X //
    w ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z).neighborhood)}

/-- The point `z` regarded as a point of its chosen coordinate neighborhood. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.pointInCoordinateNeighborhood [SmoothOfRelativeDimension d X.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhood X d z :=
  ⟨z, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localEtaleCoordinates X d z⟩

/-- A local coordinate homeomorphism on the chosen analytic open neighborhood. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhoodChart [SmoothOfRelativeDimension d X.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    OpenPartialHomeomorph (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhood X d z) (Fin d → ℂ) :=
  let D := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z
  D.ambientProjectionChart (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.pointInCoordinateNeighborhood X d z)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.pointInCoordinateNeighborhood_mem_chart_source
    [SmoothOfRelativeDimension d X.hom] (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.pointInCoordinateNeighborhood X d z ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhoodChart X d z).source :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z).mem_ambientProjectionChart_source
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.pointInCoordinateNeighborhood X d z)

/-- The chosen local chart at a complex point, extended from its analytic open neighborhood to the
whole complex-point space. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart [SmoothOfRelativeDimension d X.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    OpenPartialHomeomorph (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (Fin d → ℂ) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhoodChart X d z).lift_openEmbedding
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.isOpen_overOpen (X := X)
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z).neighborhood)).isOpenEmbedding_subtypeVal

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source [SmoothOfRelativeDimension d X.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) : z ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).source := by
  exact ⟨_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.pointInCoordinateNeighborhood X d z,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.pointInCoordinateNeighborhood_mem_chart_source X d z, rfl⟩

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_coordinateNeighborhood_of_mem_localChart_source
    [SmoothOfRelativeDimension d X.hom]
    (z w : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hw : w ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).source) :
    w ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z).neighborhood) := by
  obtain ⟨w', _, rfl⟩ := hw
  exact w'.2

@[simp]
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_target [SmoothOfRelativeDimension d X.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).target =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhoodChart X d z).target := rfl

@[simp]
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_symm_apply [SmoothOfRelativeDimension d X.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (w : Fin d → ℂ) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w =
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhoodChart X d z).symm w).1 := rfl

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_apply_of_mem [SmoothOfRelativeDimension d X.hom]
    (z w : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hw : w ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).source) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z w =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z).ambientAnalyticCoordinates
        ⟨w, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_coordinateNeighborhood_of_mem_localChart_source X d z w hw⟩ := by
  obtain ⟨w', hw', rfl⟩ := hw
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart, OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z).ambientProjectionChart_apply_of_mem
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.pointInCoordinateNeighborhood X d z) w' hw'

/-- The canonical charted-space structure obtained from algebraic smooth coordinates. -/
instance [SmoothOfRelativeDimension d X.hom] :
    ChartedSpace (Fin d → ℂ) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) where
  atlas := Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d)
  chartAt := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d
  mem_chart_source := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d
  chart_mem_atlas z := ⟨z, rfl⟩

/-- Evaluation of a regular section near an inverse-chart point is complex analytic. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_evaluate
    [SmoothOfRelativeDimension d X.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) {w : Fin d → ℂ}
    (hw : w ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).target)
    (V : X.left.Opens) (s : Γ(X.left, V))
    (hV : (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen V) :
    AnalyticAt ℂ
      (fun v ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate V s ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v)) w := by
  let D := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z
  let p := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.pointInCoordinateNeighborhood X d z
  have hwD : w ∈ (D.ambientProjectionChart p).target := by
    simpa only [D, p, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhoodChart, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_target] using hw
  have hVD : ((D.ambientProjectionChart p).symm w).1 ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen V := by
    simpa only [D, p, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhoodChart, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_symm_apply] using hV
  simpa only [D, p, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.coordinateNeighborhoodChart, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_symm_apply] using
    D.analyticAt_ambientProjectionChart_symm_evaluate p hwD V s hVD

/-- On the source of a chart, each coordinate is evaluation of its defining regular section. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_apply_component_eq_evaluate
    [SmoothOfRelativeDimension d X.hom]
    (z q : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hq : q ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).source)
    (i : Fin d) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z q i =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z).ambientCoordinateOpen
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z).ambientCoordinateSection i) q := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_apply_of_mem X d z q hq]
  exact (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z).ambientAnalyticCoordinates_apply_eq_evaluate _ i

/-- Each component of a transition between the chosen algebraic charts is complex analytic. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_transition_component
    [SmoothOfRelativeDimension d X.hom]
    (z z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) {w : Fin d → ℂ}
    (hw : w ∈ ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm.trans
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z')).source) (i : Fin d) :
    AnalyticAt ℂ
      (fun v ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z'
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v) i) w := by
  have hwtarget : w ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).target := hw.1
  have hsource : (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z').source := hw.2
  let D' := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X d z'
  have hV : (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen D'.ambientCoordinateOpen := by
    have hmem := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_coordinateNeighborhood_of_mem_localChart_source
      X d z' ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w) hsource
    simpa only [D', _root_.OAI.AlgebraicGeometry.ComplexPoint.SmoothCoordinates.LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have hi := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_evaluate X d z hwtarget
    D'.ambientCoordinateOpen (D'.ambientCoordinateSection i) hV
  apply hi.congr
  have hcontinuous : ContinuousAt (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w :=
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).continuousAt_symm hwtarget
  have heventually : (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm ⁻¹'
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z').source ∈ 𝓝 w :=
    hcontinuous ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z').open_source.mem_nhds hsource)
  filter_upwards [heventually] with v hv
  exact (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_apply_component_eq_evaluate X d z'
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v) hv i).symm

/-- A transition between the chosen algebraic charts is complex analytic. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_transition
    [SmoothOfRelativeDimension d X.hom]
    (z z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) {w : Fin d → ℂ}
    (hw : w ∈ ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm.trans
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z')).source) :
    AnalyticAt ℂ
      (fun v ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z' ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v)) w :=
  AnalyticAt.pi fun i ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_transition_component X d z z' hw i

/-- Transition maps in the chosen atlas are holomorphic on their domains. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.contDiffOn_localChart_transition
    [SmoothOfRelativeDimension d X.hom]
    (z z' : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    ContDiffOn ℂ ω ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm.trans
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z'))
        (((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm.trans
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z')).source) := by
  intro w hw
  exact (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_transition X d z z' hw).contDiffAt.contDiffWithinAt

/-- Smooth complex points form a holomorphic complex manifold of the specified dimension.

This is an instance. Through `IsManifold.of_le` it makes the complex points a `C^n` manifold for
every `n`, so no downstream file needs a local `IsManifold` instance. -/
instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isManifold_omega [SmoothOfRelativeDimension d X.hom] :
    IsManifold 𝓘(ℂ, Fin d → ℂ) ω (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    CompTriple.comp_eq, Function.id_comp, Function.comp_id, Set.preimage_id,
    Set.range_id, Set.inter_univ] using
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.contDiffOn_localChart_transition X d z z'

/-- Every analytic neighborhood of a smooth complex point contains an open contractible
neighborhood. The smaller neighborhood is the inverse image of a Euclidean ball in the chosen
algebraic coordinate chart. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le [IsIntegral X.left] [Smooth X.hom]
    (x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (U : TopologicalSpace.Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (hxU : x ∈ U) :
    ∃ (V : TopologicalSpace.Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)),
      x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  let e := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) x
  have hxsource : x ∈ e.source := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) x
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' (U : Set _)) :=
    e.isOpen_inter_preimage_symm U.2
  have hximage : e x ∈ e.target ∩ e.symm ⁻¹' (U : Set _) := by
    refine ⟨e.map_source hxsource, ?_⟩
    rwa [Set.mem_preimage, e.left_inv hxsource]
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp
    (hopen.mem_nhds hximage)
  let V : TopologicalSpace.Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
    ⟨e.source ∩ e ⁻¹' Metric.ball (e x) r,
      e.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hxV : x ∈ V := ⟨hxsource, Metric.mem_ball_self hr⟩
  have hVsource : (V : Set _) ⊆ e.source := Set.inter_subset_left
  have himage : e '' (V : Set _) = Metric.ball (e x) r := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.2
    · intro hy
      have hytarget : y ∈ e.target := (hball hy).1
      refine ⟨e.symm y, ⟨e.map_target hytarget, ?_⟩, e.right_inv hytarget⟩
      rwa [Set.mem_preimage, e.right_inv hytarget]
  have hVcontractible : ContractibleSpace V := by
    let : ContractibleSpace (Metric.ball (e x) r) := Metric.contractibleSpace_ball hr
    exact (e.homeomorphOfImageSubsetSource hVsource himage).contractibleSpace
  have hVU : V ≤ U := by
    intro z hz
    have hzU : e.symm (e z) ∈ (U : Set _) := (hball hz.2).2
    rwa [e.left_inv hz.1] at hzU
  exact ⟨V, hxV, hVcontractible, hVU⟩

/-- The analytic topology on the smooth complex-point space is locally path connected. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.locallyPathConnectedSpace [IsIntegral X.left] [Smooth X.hom] :
    LocallyPathConnectedSpace (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) := by
  refine ⟨fun x ↦ hasBasis_self.mpr fun S hS ↦ ?_⟩
  obtain ⟨U, hUS, hUopen, hxU⟩ := mem_nhds_iff.mp hS
  let Uo : TopologicalSpace.Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) := ⟨U, hUopen⟩
  obtain ⟨V, hxV, hVcontractible, hVU⟩ :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X x Uo hxU
  refine ⟨(V : Set _), V.2.mem_nhds hxV, ?_, ?_⟩
  · rw [isPathConnected_iff_pathConnectedSpace]
    infer_instance
  · exact fun z hz ↦ hUS (hVU hz)

end
end

end

end OAI.AlgebraicGeometry.ComplexPoint.Manifold
