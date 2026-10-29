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

import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Local.Purity

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean

namespace OAI.AlgebraicGeometry.Cycle.LocalPurityOf

/-!
# Local dual classes on cycle components

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Local.Purity`.
-/

/-! ### Constructions used only in proofs -/

noncomputable section

open _root_.CategoryTheory _root_.Topology

namespace AlgebraicTopology
open _root_.AlgebraicTopology
namespace Singular
open _root_.AlgebraicTopology
open _root_.OAI.AlgebraicTopology.Singular

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

@[simp]
lemma normalizedDual_apply_self (z : M) (hz : z ≠ 0) :
    (_root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedDual (R := R) z hz) z = (1 : R) :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one R hz)

@[simp]
lemma relativeCohomologyEquivDualHomology_normalizedRelativeCoclass {R : Type*} [Field R]
    {X : TopPair} {n : ℕ} (z : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology R X n) (hz : z ≠ 0) :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology R X n (_root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedRelativeCoclass z hz) =
      _root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedDual z hz :=
  (_root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology R X n).apply_symm_apply _

@[simp]
lemma normalizedRelativeCoclass_pairing_self {R : Type*} [Field R] {X : TopPair} {n : ℕ}
    (z : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology R X n) (hz : z ≠ 0) :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology R X n (_root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedRelativeCoclass z hz) z = (1 : R) := by
  rw [relativeCohomologyEquivDualHomology_normalizedRelativeCoclass, normalizedDual_apply_self]

/-- The oriented standard complex local class is nonzero in every complex dimension. -/
lemma standardComplexLocalClass_ne_zero (n : ℕ) :
    _root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ n ≠ 0 := by
  rw [_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClassGenerator.Singular.standardComplexLocalClass_ne_zero_iff]
  by_cases hn : n = 0
  · subst n
    exact _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClassGenerator.Singular.standardLocalClass_zero_ne_zero
  · exact _root_.OAI.AlgebraicTopology.LocalHomology.PuncturedEuclidean.Singular.standardLocalClass_ne_zero_of_pos (n * 2) (Nat.mul_pos (Nat.pos_of_ne_zero hn) (by
      norm_num))

/-- Two one-dimensional vector spaces with specified normalized generators are canonically
linearly equivalent by sending the first generator to the second. -/
def linearEquivOfNormalizedGenerators
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤) :
    M ≃ₗ[R] N :=
  let f : M →ₗ[R] N :=
    (LinearMap.toSpanSingleton R N y).comp (_root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedDual x hx)
  let g : N →ₗ[R] M :=
    (LinearMap.toSpanSingleton R M x).comp (_root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedDual y hy)
  LinearEquiv.ofLinearMap f g
    (by
      apply LinearMap.ext
      intro n
      obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R y).mp hyspan n
      simp [f, g, normalizedDual_apply_self])
    (by
      apply LinearMap.ext
      intro m
      obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R x).mp hxspan m
      simp [f, g, normalizedDual_apply_self])

end Singular
end AlgebraicTopology

end

noncomputable section

open _root_.CategoryTheory _root_.Topology

namespace AlgebraicTopology
open _root_.AlgebraicTopology
namespace Singular
open _root_.AlgebraicTopology
open _root_.OAI.AlgebraicTopology.Singular

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- A normalized dual is unique when its distinguished vector generates the module. -/
lemma normalizedDual_unique {z : M} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤)
    (φ : Module.Dual R M) (hφ : φ z = 1) :
    φ = _root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedDual z hz := by
  ext y
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R z).mp hzspan y
  simp [hφ]

section Coclass

variable {R : Type*} [Field R] {X : TopPair} {n : ℕ}

/-- The normalization condition characterizes the normalized coclass. -/
lemma normalizedRelativeCoclass_unique {z : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology R X n} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤) (β : _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology R X n)
    (hβ : _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology R X n β z = 1) :
    β = _root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedRelativeCoclass z hz :=
  (_root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology R X n).injective <| by
    rw [relativeCohomologyEquivDualHomology_normalizedRelativeCoclass]
    exact normalizedDual_unique hz hzspan _ hβ

end Coclass

@[simp]
lemma linearEquivOfNormalizedGenerators_apply
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤)
    (z : M) :
    linearEquivOfNormalizedGenerators x hx hxspan y hy hyspan z =
      (_root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedDual (R := R) x hx z : R) • y :=
  rfl

@[simp]
lemma linearEquivOfNormalizedGenerators_apply_generator
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤) :
    linearEquivOfNormalizedGenerators x hx hxspan y hy hyspan x = y := by simp

end Singular
end AlgebraicTopology

end

end OAI.AlgebraicGeometry.Cycle.LocalPurityOf
