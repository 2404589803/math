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

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicGeometry.ComplexPoint.ProjectiveCompact

open _root_.AlgebraicGeometry

/-!
# Analytic compactness of a projective complex scheme

A projective presentation of a complex scheme is a closed immersion into scheme-theoretic
projective space. On complex points it therefore induces a closed topological embedding into the
complex points of projective space, which are analytically compact.

Consequently the analytic complex points of any projective complex scheme form a compact space.
-/

section

open _root_.CategoryTheory Opposite _root_.TopologicalSpace _root_.Topology

section

namespace ProjectiveSpace.Presentation

/-- The immersion of a projective presentation, bundled over the complex base. -/
noncomputable abbrev overImmersion {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : _root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) :
    Over.mk f ⟶
      Over.mk (_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ)) :=
  Over.homMk P.immersion P.immersion_toBase

/-- The continuous map on complex points induced by an explicit projective presentation. -/
noncomputable def analyticImmersion {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : _root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) :
    @ContinuousMap (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk f))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ))))
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.continuousMap (overImmersion P)

/-- The analytic map of an explicit projective presentation is a closed topological
embedding. -/
lemma analyticImmersion_isClosedEmbedding {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : _root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) :
    @IsClosedEmbedding (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk f))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ))))
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology (analyticImmersion P) := by
  let : IsClosedImmersion (overImmersion P).left := P.isClosedImmersion
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isClosedEmbedding_map_of_closedImmersion (overImmersion P)

/-- The analytic complex points of an explicit projective presentation form a compact space. -/
theorem complexPoint_compactSpace {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : _root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) :
    @CompactSpace (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk f)) _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology := by
  exact (analyticImmersion_isClosedEmbedding P).compactSpace

end ProjectiveSpace.Presentation

namespace IsProjective

/-- The analytic complex points of a projective complex scheme form a compact space. -/
noncomputable instance _root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective.complexPoint_compactSpace {X : Over (Spec ↧ℂ)}
    [h : _root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] : CompactSpace (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.ProjectiveCompact.ProjectiveSpace.Presentation.complexPoint_compactSpace
    (Classical.choice h.nonempty_presentation)

end IsProjective

end

end

end OAI.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
