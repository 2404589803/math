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

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import Mathlib.Geometry.Manifold.ContMDiff.Defs

namespace OAI.AlgebraicGeometry.ComplexPoint.AnalyticMap

open _root_.AlgebraicGeometry

/-!
# Analytic maps induced by morphisms of smooth complex schemes

A morphism of schemes over `Spec ℂ` induces a holomorphic map between the complex manifolds
constructed from algebraic étale coordinates.  In local charts, every target coordinate is a
regular function.  Its pullback is again regular, so analyticity follows from the chartwise
analyticity of regular-function evaluation.
-/

noncomputable section

open _root_.CategoryTheory Filter _root_.Topology _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

section
section

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
  (d e : ℕ)

/-- In algebraic coordinate charts, each component of a morphism of smooth complex schemes is
complex analytic. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_map_component
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) {w : Fin d → ℂ}
    (hw : w ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).target)
    (hmap : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w) ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f z)).source)
    (i : Fin e) :
    AnalyticAt ℂ
      (fun v ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f z)
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v)) i) w := by
  let D := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates Y e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f z)
  have htargetOpen : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w) ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen D.ambientCoordinateOpen := by
    have hmem := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_coordinateNeighborhood_of_mem_localChart_source
      Y e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f z)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w)) hmap
    simpa only [D, _root_.OAI.AlgebraicGeometry.ComplexPoint.SmoothCoordinates.LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have hsourceOpen : (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen (f.left ⁻¹ᵁ D.ambientCoordinateOpen) :=
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.mem_overOpen_map_iff f _ D.ambientCoordinateOpen).mp htargetOpen
  have ha := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_evaluate X d z hw
    (f.left ⁻¹ᵁ D.ambientCoordinateOpen)
    (f.left.app D.ambientCoordinateOpen (D.ambientCoordinateSection i)) hsourceOpen
  have hcontinuous : ContinuousAt
      (fun v ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v)) w :=
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.continuous_map f).continuousAt.comp
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).continuousAt_symm hw)
  have heventually :
      (fun v ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v)) ⁻¹'
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f z)).source ∈ 𝓝 w :=
    hcontinuous ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f z)).open_source.mem_nhds hmap)
  apply ha.congr
  filter_upwards [heventually] with v hv
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_apply_component_eq_evaluate Y e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f z)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v)) hv i]
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate_map f D.ambientCoordinateOpen
    (D.ambientCoordinateSection i) ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v) |>.symm

/-- In algebraic coordinate charts, the map induced by a morphism of smooth complex schemes is
complex analytic. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_map
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) {w : Fin d → ℂ}
    (hw : w ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).target)
    (hmap : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm w) ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f z)).source) :
    AnalyticAt ℂ
      (fun v ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y e (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f z)
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d z).symm v))) w :=
  AnalyticAt.pi fun i ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_map_component
    X Y f d e z hw hmap i

end
end

end

end OAI.AlgebraicGeometry.ComplexPoint.AnalyticMap
