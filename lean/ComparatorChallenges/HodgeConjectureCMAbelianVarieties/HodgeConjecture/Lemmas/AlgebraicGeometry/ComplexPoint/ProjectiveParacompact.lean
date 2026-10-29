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

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

namespace OAI.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact

open _root_.AlgebraicGeometry

/-!
# Paracompact open subsets of smooth projective analytifications

A smooth projective complex variety has a compact Hausdorff analytification and algebraic
coordinate charts modeled on a finite-dimensional complex vector space. Every open subset is
therefore paracompact. This supplies the hereditary-paracompactness input for the flasque
singular-cochain resolution.
-/

noncomputable section

open _root_.TopologicalSpace
open _root_.CategoryTheory

section
section

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (X : Over (Spec ↧ℂ))
  [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- Every open subset of a smooth projective complex analytification is paracompact. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace [IsIntegral X.left] [Smooth X.hom]
    (U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) : ParacompactSpace U :=
  _root_.OAI.Topology.Foundations.ChartedSpaceParacompact.TopologicalSpace.opens_paracompactSpace_of_compact_chartedSpace (H := Fin (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) U

end
end

end

end OAI.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact
