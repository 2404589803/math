/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

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

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffineSmallPrism

namespace OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Iterated affine subdivision on singular chains

This file packages finite iterates of geometric affine subdivision on full and cover-small
singular chains.  Every iterate is chain homotopic to the identity, and the small/full iterates
commute with the canonical inclusion.
-/

section

noncomputable section

open _root_.AlgebraicTopology _root_.CategoryTheory

section
section

/-- Finite iteration of affine subdivision on all integral singular chains. -/
noncomputable def affineSingularSubdivisionIterate (X : TopCat.{0}) :
    ℕ → ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ) ⟶
      (TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ))
  | 0 => 𝟙 _
  | m + 1 => affineSingularSubdivisionIterate X m ≫
      _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionChainMap X

@[simp]
theorem affineSingularSubdivisionIterate_zero (X : TopCat.{0}) :
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.affineSingularSubdivisionIterate X 0 = 𝟙 _ :=
  rfl

theorem affineSingularSubdivisionIterate_succ
    (X : TopCat.{0}) (m : ℕ) :
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.affineSingularSubdivisionIterate X (m + 1) =
      _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.affineSingularSubdivisionIterate X m ≫
        _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionChainMap X :=
  rfl

/-- Every finite affine-subdivision iterate is chain homotopic to the identity. -/
noncomputable def affineSingularSubdivisionIterateHomotopy
    (X : TopCat.{0}) : ∀ m : ℕ,
    Homotopy (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.affineSingularSubdivisionIterate X m)
      (𝟙 ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)))
  | 0 => Homotopy.refl _
  | m + 1 => by
      simpa [affineSingularSubdivisionIterate_succ] using
        (affineSingularSubdivisionIterateHomotopy X m).comp
          (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionHomotopy X)

section Small

variable {iota : Type} (X : TopCat) (U : iota → Set X)

/-- Finite iteration of affine subdivision on cover-small chains. -/
noncomputable def coverSmallAffineSubdivisionIterate :
    ℕ → (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U ⟶
      _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U)
  | 0 => 𝟙 _
  | m + 1 => coverSmallAffineSubdivisionIterate m ≫
      _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U

@[simp]
theorem coverSmallAffineSubdivisionIterate_zero :
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.coverSmallAffineSubdivisionIterate X U 0 = 𝟙 _ :=
  rfl

theorem coverSmallAffineSubdivisionIterate_succ (m : ℕ) :
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.coverSmallAffineSubdivisionIterate X U (m + 1) =
      _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.coverSmallAffineSubdivisionIterate X U m ≫
        _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U :=
  rfl

/-- Every cover-small affine-subdivision iterate is chain homotopic to the identity. -/
noncomputable def coverSmallAffineSubdivisionIterateHomotopy :
    ∀ m : ℕ, Homotopy (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.coverSmallAffineSubdivisionIterate X U m)
      (𝟙 (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U))
  | 0 => Homotopy.refl _
  | m + 1 => by
      simpa [coverSmallAffineSubdivisionIterate_succ] using
        (coverSmallAffineSubdivisionIterateHomotopy m).comp
          (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmallPrism.coverSmallAffineSubdivisionHomotopy X U)

/-- Small and full affine-subdivision iterates commute with the small-chain inclusion. -/
theorem coverSmallAffineSubdivisionIterate_comp_inclusion : ∀ m : ℕ,
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.coverSmallAffineSubdivisionIterate X U m ≫
        _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U =
      _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U ≫
        _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.affineSingularSubdivisionIterate X m
  | 0 => by
      change (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)) =
        SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
          (AddCommGrpCat.of ℤ) ≫ 𝟙 _
      simp
  | m + 1 => by
      let I := SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)
      have hm := coverSmallAffineSubdivisionIterate_comp_inclusion m
      change _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.coverSmallAffineSubdivisionIterate X U m ≫ I =
        I ≫ _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.affineSingularSubdivisionIterate X m at hm
      have hA := _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap_comp_inclusion X U
      change _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U ≫ I =
        I ≫ _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionChainMap X at hA
      rw [coverSmallAffineSubdivisionIterate_succ,
        affineSingularSubdivisionIterate_succ]
      change (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.coverSmallAffineSubdivisionIterate X U m ≫
          _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U) ≫ I =
        I ≫ (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration.affineSingularSubdivisionIterate X m ≫
          _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionChainMap X)
      rw [Category.assoc, hA, ← Category.assoc, hm, Category.assoc]

end Small

end
end

end
end

end OAI.AlgebraicTopology.Singular.SubdivisionAffineIteration
