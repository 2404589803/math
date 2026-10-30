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

import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.ComplexClass
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter

namespace OAI.AlgebraicTopology.LocalHomology.FundamentalClassGenerator

open _root_.AlgebraicTopology

/-!
# Generator properties of the standard complex local class

The ordered real and imaginary coordinate homeomorphism identifies the standard complex local
class with the explicit real local class. This file records that this identification preserves
nonvanishing, linear independence, and generation of local homology.

These results isolate the remaining topological input for local purity: it suffices to prove that
the explicit real affine cycle generates the corresponding real relative homology group.
-/

noncomputable section

open _root_.CategoryTheory Limits
open scoped Simplicial

section
namespace Singular

def standardComplexLocalClassMul (p : ℕ) :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ p) (p * 2) :=
  (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexRealRelativeHomologyIso ℚ p).inv.hom (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ (p * 2))

/-- Transport a relative homology class along an equality of degrees. -/
def relativeHomologyDegreeCast {X : TopPair} {i j : ℕ} (h : i = j)
    (z : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ X i) : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ X j :=
  h ▸ z

lemma relativeHomologyDegreeCast_ne_zero_iff {X : TopPair} {i j : ℕ} (h : i = j)
    (z : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ X i) :
    relativeHomologyDegreeCast h z ≠ 0 ↔ z ≠ 0 := by aesop

lemma span_relativeHomologyDegreeCast_eq_top_iff {X : TopPair} {i j : ℕ} (h : i = j)
    (z : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ X i) :
    Submodule.span ℚ {relativeHomologyDegreeCast h z} = ⊤ ↔
      Submodule.span ℚ {z} = ⊤ := by aesop

lemma standardComplexRealRelativeHomologyIso_hom_standardComplexLocalClassMul (p : ℕ) :
    (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexRealRelativeHomologyIso ℚ p).hom.hom
        (standardComplexLocalClassMul p) =
      _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ (p * 2) := by
  exact (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexRealRelativeHomologyIso ℚ p).inv_hom_id_apply
    (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ (p * 2))

lemma standardComplexLocalClassMul_ne_zero_iff (p : ℕ) :
    standardComplexLocalClassMul p ≠ 0 ↔ _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ (p * 2) ≠ 0 := by
  exact (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexRealRelativeHomologyIso ℚ p).symm.toLinearEquiv.map_ne_zero_iff

lemma standardComplexLocalClass_ne_zero_iff (p : ℕ) :
    _root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ p ≠ 0 ↔ _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ (p * 2) ≠ 0 := by
  change relativeHomologyDegreeCast (Nat.mul_comm p 2)
      (standardComplexLocalClassMul p) ≠ 0 ↔ _
  rw [relativeHomologyDegreeCast_ne_zero_iff,
    standardComplexLocalClassMul_ne_zero_iff]

lemma span_standardComplexLocalClassMul_eq_top_iff (p : ℕ) :
    Submodule.span ℚ {standardComplexLocalClassMul p} = ⊤ ↔
      Submodule.span ℚ {_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ (p * 2)} = ⊤ := by
  let e := (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexRealRelativeHomologyIso ℚ p).toLinearEquiv
  have he : e (standardComplexLocalClassMul p) = _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ (p * 2) :=
    standardComplexRealRelativeHomologyIso_hom_standardComplexLocalClassMul p
  have hmap :
      (Submodule.span ℚ {standardComplexLocalClassMul p}).map e.toLinearMap =
        Submodule.span ℚ {_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ (p * 2)} := by
    rw [Submodule.map_span]
    simp [he]
  have etop : (⊤ : Submodule ℚ _).map e.toLinearMap = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  constructor
  · intro h
    rw [← hmap, h, etop]
  · intro h
    apply Submodule.map_injective_of_injective e.injective
    rw [hmap, h, etop]

lemma span_standardComplexLocalClass_eq_top_iff (p : ℕ) :
    Submodule.span ℚ {_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ p} = ⊤ ↔
      Submodule.span ℚ {_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ (p * 2)} = ⊤ := by
  change Submodule.span ℚ
      {relativeHomologyDegreeCast (Nat.mul_comm p 2) (standardComplexLocalClassMul p)} = ⊤ ↔ _
  rw [span_relativeHomologyDegreeCast_eq_top_iff,
    span_standardComplexLocalClassMul_eq_top_iff]

lemma isEmpty_puncturedPair_zero_simplices (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0).snd) _⦋n⦌) := by
  constructor
  intro σ
  let f := ((_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0).snd.toSSetObjEquiv _ ) σ
  let y := f Convexity.StdSimplex.barycenter
  apply y.2
  funext j
  exact Fin.elim0 j

lemma standardPairChainMap_zero :
    ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).hom = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro σ
  exact (isEmpty_puncturedPair_zero_simplices n).false σ |>.elim

noncomputable instance standardLocalProjectionZeroIsIso :
    IsIso (_root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeChainProjection ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)) :=
  cokernel.π_of_zero standardPairChainMap_zero

/-- The relative-chain projection with its ambient source exposed through the pair functor. -/
def standardRelativeChainProjectionZero :
    ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right ⟶
      _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalRelativeChainComplex ℚ 0 :=
  _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeChainProjection ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)

noncomputable instance standardRelativeChainProjectionZeroIsIso :
    IsIso standardRelativeChainProjectionZero :=
  cokernel.π_of_zero standardPairChainMap_zero

def standardRelativeHomologyProjectionZeroIso :
    ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.homology 0 ≅
      _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0) 0 :=
  HomologicalComplex.homologyMapIso
    (asIso standardRelativeChainProjectionZero) 0

/-- The zero-dimensional standard relative local homology group is canonically one-dimensional. -/
def standardLocalRelativeHomologyZeroIso :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0) 0 ≅ ModuleCat.of ℚ ℚ :=
  letI (j : Fin 0) : TotallyDisconnectedSpace ℝ := Fin.elim0 j
  letI : TotallyDisconnectedSpace (Fin 0 → ℝ) := inferInstance
  standardRelativeHomologyProjectionZeroIso.symm ≪≫
      singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (ModuleCat (R := ℚ)) (ModuleCat.of ℚ ℚ)
          (TopCat.of (Fin 0 → ℝ)) ≪≫
      CategoryTheory.Limits.coproductUniqueIso
        (fun _ : Fin 0 → ℝ ↦ ModuleCat.of ℚ ℚ)

/-- The ambient zero-cycle represented by the unique singular point of `ℝ⁰`. -/
def standardAmbientCycleZero :
    ModuleCat.of ℚ ℚ ⟶
      ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.cycles 0 :=
  ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.liftCycles
    (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardAmbientSimplexChain ℚ 0) 0 (by simp) (by
      rw [((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.shape 0 0 (by simp)]
      exact comp_zero)

/-- The class of the unique singular point in the ambient homology of `ℝ⁰`. -/
def standardAmbientClassZero :
    ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.homology 0 :=
  ((standardAmbientCycleZero ≫
    ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.homologyπ 0).hom) 1

lemma standardAmbientCycleZero_projection :
    standardAmbientCycleZero ≫
        HomologicalComplex.cyclesMap
          standardRelativeChainProjectionZero 0 =
      _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalCycle ℚ 0 := by
  apply (cancel_mono ((_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalRelativeChainComplex ℚ 0).iCycles 0)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClassBoundary.Singular.standardLocalCycle_inclusion,
    ← Category.assoc, standardAmbientCycleZero, HomologicalComplex.liftCycles_i]
  rfl

lemma standardAmbientClassZero_projection :
    standardRelativeHomologyProjectionZeroIso.hom.hom
        standardAmbientClassZero =
      _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0 := by
  have hmor :
      standardAmbientCycleZero ≫
          ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.homologyπ 0 ≫
          standardRelativeHomologyProjectionZeroIso.hom =
        _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalCycle ℚ 0 ≫ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalRelativeChainComplex ℚ 0).homologyπ 0 := by
    change standardAmbientCycleZero ≫
      ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.homologyπ 0 ≫
        HomologicalComplex.homologyMap standardRelativeChainProjectionZero 0 = _
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      standardAmbientCycleZero_projection]
  exact ConcreteCategory.congr_hom hmor 1

/-- The ordinary `H₀` augmentation, with its source exposed through the pair functor. -/
def standardAmbientHomologyZeroε :
    ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.homology 0 ⟶
      ModuleCat.of ℚ ℚ :=
  (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0).fst.singularHomology₀ε (ModuleCat.of ℚ ℚ)

/-- The augmentation on zero-dimensional relative local homology. -/
def standardLocalRelativeHomologyZeroε :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0) 0 ⟶ ModuleCat.of ℚ ℚ :=
  standardRelativeHomologyProjectionZeroIso.inv ≫
    standardAmbientHomologyZeroε

lemma standardAmbientClassZero_epsilon :
    standardAmbientHomologyZeroε.hom
        standardAmbientClassZero = 1 := by
  have h := SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
    (TopCat.toSSet.obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0).fst) (ModuleCat.of ℚ ℚ)
    (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardSingularSimplex 0)
  have hmor : standardAmbientCycleZero ≫
      ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0)).right.homologyπ 0 ≫
        standardAmbientHomologyZeroε = 𝟙 (ModuleCat.of ℚ ℚ) := by
    change
      ((TopCat.toSSet.obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0).fst).chainComplex
        (ModuleCat.of ℚ ℚ)).liftCycles
          ((TopCat.toSSet.obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0).fst).ιChainComplex
            (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardSingularSimplex 0)) 0 (by simp) (by simp) ≫
        ((TopCat.toSSet.obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0).fst).chainComplex
          (ModuleCat.of ℚ ℚ)).homologyπ 0 ≫
        (TopCat.toSSet.obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ 0).fst).homology₀ε
          (ModuleCat.of ℚ ℚ) = 𝟙 (ModuleCat.of ℚ ℚ)
    exact h
  exact ConcreteCategory.congr_hom hmor 1

lemma standardLocalClass_zero_epsilon :
    standardLocalRelativeHomologyZeroε.hom (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0) = 1 := by
  rw [← standardAmbientClassZero_projection]
  change standardAmbientHomologyZeroε.hom
    (standardRelativeHomologyProjectionZeroIso.inv.hom
      (standardRelativeHomologyProjectionZeroIso.hom.hom standardAmbientClassZero)) = 1
  rw [standardRelativeHomologyProjectionZeroIso.hom_inv_id_apply]
  exact standardAmbientClassZero_epsilon

lemma standardLocalClass_zero_ne_zero : _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0 ≠ 0 := by
  intro h
  have := standardLocalClass_zero_epsilon
  rw [h, map_zero] at this
  exact zero_ne_one this

lemma span_standardLocalClass_zero_eq_top :
    Submodule.span ℚ {_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0} = ⊤ := by
  let e := standardLocalRelativeHomologyZeroIso.toLinearEquiv
  have he : e (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0) ≠ (0 : ℚ) :=
    e.map_ne_zero_iff.mpr standardLocalClass_zero_ne_zero
  have hmap :
      (Submodule.span ℚ {_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0}).map e.toLinearMap =
        Submodule.span ℚ {e (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0)} := by
    rw [Submodule.map_span]
    simp only [Set.image_singleton]
    change Submodule.span ℚ {e (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0)} = _
    rfl
  have hone : Submodule.span ℚ {e (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0)} = ⊤ := by
    apply (Submodule.span_singleton_eq_top_iff ℚ (e (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0))).mpr
    intro q
    exact ⟨q / e (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass ℚ 0), by
      simpa only [smul_eq_mul] using div_mul_cancel₀ q he⟩
  apply Submodule.map_injective_of_injective e.injective
  rw [hmap, hone, Submodule.map_top]
  exact (LinearMap.range_eq_top.mpr e.surjective).symm

lemma span_standardComplexLocalClass_zero_eq_top :
    Submodule.span ℚ {_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ 0} = ⊤ := by
  have h := (span_standardComplexLocalClassMul_eq_top_iff 0).mpr
    span_standardLocalClass_zero_eq_top
  simpa [_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass, standardComplexLocalClassMul] using h

end Singular
end

end

end OAI.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
