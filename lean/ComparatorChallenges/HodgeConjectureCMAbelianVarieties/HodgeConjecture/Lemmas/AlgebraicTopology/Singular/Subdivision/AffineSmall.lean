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

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.Affine

import Mathlib.Algebra.Homology.HomologicalComplexLimits

namespace OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Affine subdivision on cover-small singular chains

Affine barycentric subdivision of a simplex only precomposes that simplex.  Consequently a
simplex which factors through one member of a cover subdivides entirely inside the same member.
This file packages that range-preservation statement as an endomorphism of the cover-small chain
complex and proves compatibility with its inclusion into all singular chains.
-/

section

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set

section
section

variable {iota : Type} (X : TopCat) (U : iota → Set X)

/-- A selected cover member through which a cover-small simplex factors. -/
noncomputable def coverSmallSimplexPreimageIndex
    {n : SimplexCategoryᵒᵖ}
    (x : (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj n) : iota :=
  ((_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.mem_coverSmallSingularSubcomplex_iff_exists_preimage X U x.1).mp x.2).choose

/-- A selected lift of a cover-small simplex to its selected cover member. -/
noncomputable def coverSmallSimplexPreimage
    {n : SimplexCategoryᵒᵖ}
    (x : (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj n) :
    (TopCat.toSSet.obj
      (TopCat.of (U (coverSmallSimplexPreimageIndex X U x)))).obj n :=
  ((_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.mem_coverSmallSingularSubcomplex_iff_exists_preimage X U x.1).mp
    x.2).choose_spec.choose

/-- The selected lift maps back to the underlying ambient singular simplex. -/
theorem coverSmallSimplexPreimage_spec
    {n : SimplexCategoryᵒᵖ}
    (x : (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj n) :
    (TopCat.toSSet.map
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X
        (U (coverSmallSimplexPreimageIndex X U x)))).app n
        (coverSmallSimplexPreimage X U x) = x.1 :=
  ((_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.mem_coverSmallSingularSubcomplex_iff_exists_preimage X U x.1).mp
    x.2).choose_spec.choose_spec

/-- Affine subdivision of a cover-small generator, performed in a cover member and then mapped
back into the cover-small complex. -/
noncomputable def coverSmallAffineSubdivisionSimplexChain
    (n : ℕ)
    (x : (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X n :=
  _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSubdivisionSingularSimplexChain
      (TopCat.of (U (coverSmallSimplexPreimageIndex X U x))) n
      (coverSmallSimplexPreimage X U x) ≫
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallIntegralSingularChains X U
      (coverSmallSimplexPreimageIndex X U x)).f n

/-- The degreewise affine subdivision endomorphism of cover-small chains. -/
noncomputable def coverSmallAffineSubdivisionComponent (n : ℕ) :
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X n ⟶
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X n :=
  Sigma.desc (coverSmallAffineSubdivisionSimplexChain X U n)

@[reassoc (attr := simp)]
theorem iota_coverSmallAffineSubdivisionComponent
    (n : ℕ)
    (x : (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).ιChainComplex x ≫
        coverSmallAffineSubdivisionComponent X U n =
      coverSmallAffineSubdivisionSimplexChain X U n x := by
  apply Sigma.ι_comp_desc

/-- Subdivision of a selected cover-small generator agrees with full subdivision after
inclusion. -/
theorem coverSmallAffineSubdivisionSimplexChain_comp_inclusion
    (n : ℕ)
    (x : (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    coverSmallAffineSubdivisionSimplexChain X U n x ≫
        (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n =
      _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSubdivisionSingularSimplexChain X n x.1 := by
  let j := coverSmallSimplexPreimageIndex X U x
  let y := coverSmallSimplexPreimage X U x
  change (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSubdivisionSingularSimplexChain
      (TopCat.of (U j)) n y ≫
        (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallSingularSet X U j)
          (AddCommGrpCat.of ℤ)).f n) ≫
      (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f n =
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSubdivisionSingularSimplexChain X n x.1
  have hcover := congrArg (fun F ↦ F.f n)
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallIntegralSingularChains_comp_inclusion X U j)
  change (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallSingularSet X U j)
        (AddCommGrpCat.of ℤ)).f n ≫
      (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f n =
    (SSet.chainComplexMap
      (TopCat.toSSet.map (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X (U j)))
      (AddCommGrpCat.of ℤ)).f n at hcover
  rw [Category.assoc, hcover, ← _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSubdivisionSingularSimplexChain_naturality]
  change _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSubdivisionSingularSimplexChain X n
      ((TopCat.toSSet.map (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X (U j))).app _ y) =
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSubdivisionSingularSimplexChain X n x.1
  rw [show (TopCat.toSSet.map
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X (U j))).app _ y = x.1 from
    coverSmallSimplexPreimage_spec X U x]

/-- Cover-small affine subdivision agrees with full affine subdivision after inclusion. -/
theorem coverSmallAffineSubdivisionComponent_comp_inclusion
    (n : ℕ) :
    coverSmallAffineSubdivisionComponent X U n ≫
        (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n =
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n ≫
        _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionComponent X n := by
  change coverSmallAffineSubdivisionComponent X U n ≫
      (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f n =
    (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
      (AddCommGrpCat.of ℤ)).f n ≫
      _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionComponent X n
  apply (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_coverSmallAffineSubdivisionComponent]
  simp only [SSet.ι_chainComplexMap_f_assoc,
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.iota_affineSingularSubdivisionComponent]
  exact coverSmallAffineSubdivisionSimplexChain_comp_inclusion X U n x

/-- The cover-small affine subdivision components commute with the small-chain boundary. -/
theorem coverSmallAffineSubdivisionComponents_commute
    (n : ℕ) :
    coverSmallAffineSubdivisionComponent X U (n + 1) ≫
        (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).d (n + 1) n =
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫
        coverSmallAffineSubdivisionComponent X U n := by
  let I := SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
    (AddCommGrpCat.of ℤ)
  let A := coverSmallAffineSubdivisionComponent X U
  let B := _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionComponent X
  have : Mono I := by
    dsimp [I]
    exact _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion_mono X U
  have : Mono (I.f n) := by
    change Mono ((HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) n).map I)
    exact Functor.map_mono (HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) n) I
  have hAI (k : ℕ) : A k ≫ I.f k = I.f k ≫ B k :=
    coverSmallAffineSubdivisionComponent_comp_inclusion X U k
  apply (cancel_mono (I.f n)).mp
  rw [Category.assoc, ← I.comm, ← Category.assoc, hAI, Category.assoc,
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionComponents_commute, ← Category.assoc, I.comm,
    Category.assoc, ← hAI, ← Category.assoc]

/-- Affine barycentric subdivision as an endomorphism of the cover-small chain complex. -/
noncomputable def coverSmallAffineSubdivisionChainMap :
    _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U ⟶
      _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U :=
  ChainComplex.ofHom (coverSmallAffineSubdivisionComponent X U)
    (coverSmallAffineSubdivisionComponents_commute X U)

@[simp]
theorem coverSmallAffineSubdivisionChainMap_f (n : ℕ) :
    (coverSmallAffineSubdivisionChainMap X U).f n =
      coverSmallAffineSubdivisionComponent X U n :=
  rfl

/-- Cover-small subdivision is the restriction of full affine singular subdivision. -/
theorem coverSmallAffineSubdivisionChainMap_comp_inclusion :
    coverSmallAffineSubdivisionChainMap X U ≫
        _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U =
      _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U ≫
        _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionChainMap X := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact coverSmallAffineSubdivisionComponent_comp_inclusion X U n

end
end

end
end

end OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall
