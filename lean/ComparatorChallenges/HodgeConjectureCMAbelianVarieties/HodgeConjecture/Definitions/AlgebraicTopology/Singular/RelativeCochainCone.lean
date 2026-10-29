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

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace OAI.AlgebraicTopology.Singular.RelativeCochainCone

/-!
# Relative singular cohomology as a cochain mapping cone

For a topological pair `A ⊆ X`, restriction of singular cochains is the algebraic dual of
the inclusion `C_*(A) ⟶ C_*(X)`.  This file proves, without a finite-dimensionality
hypothesis, that the cohomology in degree `n - 1` of its mapping cone is `H^n(X, A)`, the
degree-`n` cohomology of the dual relative cochain complex.

The proof dualizes the degreewise short exact sequence
`C_*(A) ⟶ C_*(X) ⟶ C_*(X, A)`, extends the resulting cochain complexes by zero to
integer degrees, and compares its rotated triangle with Mathlib's mapping-cone triangle.
-/

noncomputable section

open _root_.CategoryTheory Limits
open _root_.CategoryTheory.Pretriangulated

universe u

section
section

variable (R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This is
the sequence `C^*(X, A; R) → C^*(X; R) → C^*(A; R)` of nonnegative cochain complexes. The maps
include cochains vanishing on `A` and restrict cochains to `A`; their composite is zero. -/
def relativeDualCochainShortComplexNat (X : TopPair.{u}) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk
    (_root_.OAI.Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap (_root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeChainProjection R X))
    (_root_.OAI.Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor R).obj X).hom)
    (by
      ext n φ
      change Module.Dual R (((_root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeChainFunctor R).obj X).X n) at φ
      apply LinearMap.ext
      intro x
      change φ (((((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor R).obj X).hom ≫
        _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeChainProjection R X).f n).hom x) = 0
      rw [_root_.OAI.AlgebraicTopology.Singular.CohomologyTo.subspaceChainMap_relativeChainProjection]
      exact map_zero φ)

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This is
the sequence `C^*(X, A; R) → C^*(X; R) → C^*(A; R)`, with all complexes extended by zero to
negative integer degrees. Its maps are inclusion of cochains vanishing on `A` and restriction to
`A`. -/
def relativeDualCochainShortComplexInt (X : TopPair.{u}) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (relativeDualCochainShortComplexNat R X).map
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R))

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This
map `C^*(X; R) → C^*(A; R)` restricts singular cochains along the embedding of `A`. Both
complexes are indexed by integers and zero in negative degrees. -/
def relativeCochainRestrictionInt (X : TopPair.{u}) :
    ((_root_.OAI.Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (_root_.OAI.AlgebraicTopology.Singular.Cohomology.SingularChainComplex R X.fst)).extend
        ComplexShape.embeddingUpNat) ⟶
      ((_root_.OAI.Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor R).obj X).left).extend
        ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap
    (_root_.OAI.Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor R).obj X).hom)
    ComplexShape.embeddingUpNat

end
end

end

end OAI.AlgebraicTopology.Singular.RelativeCochainCone
