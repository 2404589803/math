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

import HodgeConjecture.Lemmas.Algebra.Homology.MapExtendNaturality
import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.GlobalRestriction
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone

namespace OAI.AlgebraicGeometry.Cohomology.SupportSingularGlobal

/-!
# Global singular restriction and relative cohomology

This file identifies restriction on global raw singular cochains with the algebraic dual of
the singular-chain inclusion of a topological pair.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace

namespace AlgebraicTopology
open _root_.AlgebraicTopology
namespace Singular
open _root_.AlgebraicTopology
open _root_.OAI.AlgebraicTopology.Singular

universe u v

variable (R : Type) [CommRing R] (X : TopCat.{0})

/-- The raw global singular-cochain complex, extended by zero to integer degrees. -/
def globalRawSingularCochainComplexInt : CochainComplex AddCommGrpCat ℤ :=
  (_root_.OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R X).extend ComplexShape.embeddingUpNat

/-- The raw global singular-cochain pushforward from a subset, extended by zero to integer
degrees. -/
def globalRawPushforwardSingularCochainComplexInt (A : Set X) :
    CochainComplex AddCommGrpCat ℤ :=
  (_root_.OAI.AlgebraicTopology.Singular.GlobalRestriction.globalRawPushforwardSingularCochainComplex R
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X A)).extend ComplexShape.embeddingUpNat

/-- Raw global restriction, extended by zero to integer degrees. -/
def globalRawSingularRestrictionInt (A : Set X) :
    globalRawSingularCochainComplexInt R X ⟶
      globalRawPushforwardSingularCochainComplexInt R X A :=
  HomologicalComplex.extendMap
    (_root_.OAI.AlgebraicTopology.Singular.GlobalRestriction.globalRawSingularRestriction R (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X A))
      ComplexShape.embeddingUpNat

end Singular
end AlgebraicTopology

end

end OAI.AlgebraicGeometry.Cohomology.SupportSingularGlobal
