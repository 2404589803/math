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

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffinePrism
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffineSmall

import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomologicalComplexLimits

namespace OAI.AlgebraicTopology.Singular.SubdivisionAffineSmallPrism

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# The affine subdivision prism on cover-small singular chains

The universal affine prism only precomposes a singular simplex.  It therefore preserves the
range of any cover member, just as affine subdivision itself does.  This file restricts the
prism to the cover-small chain complex and proves that cover-small affine subdivision is chain
homotopic to the identity there.
-/

section

noncomputable section

open _root_.AlgebraicTopology _root_.CategoryTheory _root_.CategoryTheory.Limits Set

section
section

variable {iota : Type} (X : TopCat) (U : iota → Set X)

/-- The affine prism on a selected lift of a cover-small generator, mapped back into the small
chain complex. -/
noncomputable def coverSmallAffinePrismSimplexChain
    (n : ℕ)
    (x : (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X (n + 1) :=
  (TopCat.toSSet.obj
      (TopCat.of (U (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallSimplexPreimageIndex X U x)))).ιChainComplex
        (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallSimplexPreimage X U x) ≫
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent
      (TopCat.of (U (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallSimplexPreimageIndex X U x))) n ≫
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallIntegralSingularChains X U
      (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallSimplexPreimageIndex X U x)).f (n + 1)

/-- The degree-raising affine prism operator on cover-small chains. -/
noncomputable def coverSmallAffinePrismComponent (n : ℕ) :
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X n ⟶
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X (n + 1) :=
  Sigma.desc (coverSmallAffinePrismSimplexChain X U n)

@[reassoc (attr := simp)]
theorem iota_coverSmallAffinePrismComponent
    (n : ℕ)
    (x : (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).ιChainComplex x ≫
        coverSmallAffinePrismComponent X U n =
      coverSmallAffinePrismSimplexChain X U n x := by
  apply Sigma.ι_comp_desc

/-- The small prism on a generator agrees with the full prism after inclusion. -/
theorem coverSmallAffinePrismSimplexChain_comp_inclusion
    (n : ℕ)
    (x : (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    coverSmallAffinePrismSimplexChain X U n x ≫
        (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f (n + 1) =
      (TopCat.toSSet.obj X).ιChainComplex x.1 ≫
        _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X n := by
  let j := _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallSimplexPreimageIndex X U x
  let y := _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallSimplexPreimage X U x
  let I := SSet.chainComplexMap
    (TopCat.toSSet.map (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X (U j)))
    (AddCommGrpCat.of ℤ)
  have hcover := congrArg (fun F ↦ F.f (n + 1))
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallIntegralSingularChains_comp_inclusion X U j)
  change (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallSingularSet X U j)
        (AddCommGrpCat.of ℤ)).f (n + 1) ≫
      (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f (n + 1) = I.f (n + 1) at hcover
  change (((TopCat.toSSet.obj (TopCat.of (U j))).ιChainComplex y ≫
      _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent (TopCat.of (U j)) n) ≫
        (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallSingularSet X U j)
          (AddCommGrpCat.of ℤ)).f (n + 1)) ≫
      (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f (n + 1) = _
  rw [Category.assoc, hcover, Category.assoc,
    ← _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent_naturality, ← Category.assoc,
    SSet.ι_chainComplexMap_f, show (TopCat.toSSet.map
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X (U j))).app _ y = x.1 from
    _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallSimplexPreimage_spec X U x]

/-- The small prism agrees degreewise with the full prism after inclusion. -/
theorem coverSmallAffinePrismComponent_comp_inclusion
    (n : ℕ) :
    coverSmallAffinePrismComponent X U n ≫
        (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f (n + 1) =
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n ≫
        _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X n := by
  change coverSmallAffinePrismComponent X U n ≫
      (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f (n + 1) =
    (SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
      (AddCommGrpCat.of ℤ)).f n ≫
      _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X n
  apply (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_coverSmallAffinePrismComponent]
  simp only [SSet.ι_chainComplexMap_f_assoc]
  exact coverSmallAffinePrismSimplexChain_comp_inclusion X U n x

/-- The cover-small prism gives the chain-homotopy equation in positive degrees. -/
theorem coverSmallAffinePrismComponent_identity_succ
    (n : ℕ) :
    (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U).f (n + 1) =
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫
          coverSmallAffinePrismComponent X U n +
        coverSmallAffinePrismComponent X U (n + 1) ≫
          (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).d (n + 2) (n + 1) +
        𝟙 ((_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X (n + 1)) := by
  let I := SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
    (AddCommGrpCat.of ℤ)
  have : Mono I := by
    dsimp [I]
    exact _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion_mono X U
  have : Mono (I.f (n + 1)) := by
    change Mono ((HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) (n + 1)).map I)
    infer_instance
  apply (cancel_mono (I.f (n + 1))).mp
  rw [Preadditive.add_comp, Preadditive.add_comp]
  simp only [Category.id_comp]
  rw [_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap_f]
  have hA := _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionComponent_comp_inclusion X U (n + 1)
  change _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionComponent X U (n + 1) ≫ I.f (n + 1) =
    I.f (n + 1) ≫ _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionComponent X (n + 1) at hA
  have hP (k : ℕ) :
      coverSmallAffinePrismComponent X U k ≫ I.f (k + 1) =
        I.f k ≫ _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X k :=
    coverSmallAffinePrismComponent_comp_inclusion X U k
  rw [hA]
  change I.f (n + 1) ≫
      (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionChainMap X).f (n + 1) = _
  rw [_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent_identity_succ,
    Preadditive.comp_add, Preadditive.comp_add]
  simp only [Category.comp_id]
  apply congrArg₂ (fun a b ↦ a + b)
  · apply congrArg₂ (fun a b ↦ a + b)
    · rw [← Category.assoc, I.comm, Category.assoc, ← hP, ← Category.assoc]
    · rw [← Category.assoc, ← hP, Category.assoc, I.comm, ← Category.assoc]
  · rfl

/-- The cover-small prism gives the chain-homotopy equation in degree zero. -/
theorem coverSmallAffinePrismComponent_identity_zero :
    (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U).f 0 =
      coverSmallAffinePrismComponent X U 0 ≫
          (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).d 1 0 +
        𝟙 ((_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X 0) := by
  let I := SSet.chainComplexMap (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
    (AddCommGrpCat.of ℤ)
  have : Mono I := by
    dsimp [I]
    exact _root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion_mono X U
  have : Mono (I.f 0) := by
    change Mono ((HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) 0).map I)
    infer_instance
  apply (cancel_mono (I.f 0)).mp
  rw [Preadditive.add_comp]
  simp only [Category.id_comp]
  rw [_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap_f]
  have hA := _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionComponent_comp_inclusion X U 0
  change _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionComponent X U 0 ≫ I.f 0 =
    I.f 0 ≫ _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionComponent X 0 at hA
  have hP : coverSmallAffinePrismComponent X U 0 ≫ I.f 1 =
      I.f 0 ≫ _root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X 0 :=
    coverSmallAffinePrismComponent_comp_inclusion X U 0
  rw [hA]
  change I.f 0 ≫ (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffine.affineSingularSubdivisionChainMap X).f 0 = _
  rw [_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent_identity_zero,
    Preadditive.comp_add]
  simp only [Category.comp_id]
  apply congrArg₂ (fun a b ↦ a + b)
  · rw [← Category.assoc, ← hP, Category.assoc, I.comm, ← Category.assoc]
  · rfl

/-- The degree-raising small-prism family. -/
noncomputable def coverSmallAffinePrismHom (i j : ℕ) :
    (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X i ⟶
      (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X j :=
  if h : j = i + 1 then by
    subst j
    exact coverSmallAffinePrismComponent X U i
  else 0

@[simp]
theorem coverSmallAffinePrismHom_succ (i : ℕ) :
    coverSmallAffinePrismHom X U i (i + 1) =
      coverSmallAffinePrismComponent X U i := by
  simp [coverSmallAffinePrismHom]

/-- Cover-small affine subdivision is chain homotopic to the identity. -/
noncomputable def coverSmallAffineSubdivisionHomotopy :
    Homotopy (_root_.OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U)
      (𝟙 (_root_.OAI.AlgebraicTopology.Singular.ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U)) where
  hom := coverSmallAffinePrismHom X U
  zero i j hij := by
    rw [coverSmallAffinePrismHom]
    split_ifs with h
    · exfalso
      apply hij
      rw [ComplexShape.down_Rel]
      exact h.symm
    · rfl
  comm i := by
    cases i with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex]
        simp only [coverSmallAffinePrismHom_succ, zero_add,
          HomologicalComplex.id_f]
        exact coverSmallAffinePrismComponent_identity_zero X U
    | succ n =>
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex]
        simp only [coverSmallAffinePrismHom_succ,
          HomologicalComplex.id_f]
        exact coverSmallAffinePrismComponent_identity_succ X U n

end
end

end
end

end OAI.AlgebraicTopology.Singular.SubdivisionAffineSmallPrism
