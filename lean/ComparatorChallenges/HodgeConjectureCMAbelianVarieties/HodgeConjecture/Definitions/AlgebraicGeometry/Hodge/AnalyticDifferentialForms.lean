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

import HodgeConjecture.Lemmas.Algebra.DeRham.Basic
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticSheaf
import HodgeConjecture.Lemmas.Analysis.Calculus.DifferentialForm.ExactWedge

namespace OAI.AlgebraicGeometry.Hodge.AnalyticDifferentialForms

open _root_.AlgebraicGeometry

/-!
# Analytic differential forms

This file constructs analytic differential forms from holomorphic functions and their
manifold derivatives. The pointwise algebra of wedges lives in
`HodgeConjecture.Mathlib.Analysis.NormedSpace.WedgeCovectors` and
`HodgeConjecture.Lemmas.Analysis.Calculus.DifferentialForm.ExactWedge`.

The starting point is `Algebra.DeRham.Form ℂ 𝒪(U) p`, the Kähler differential forms of the
holomorphic functions on `U`, that is `⋀^p Ω[𝒪(U)⁄ℂ]`. In a fixed chart at `z` such a form is
evaluated pointwise as an alternating continuous multilinear map: taking coordinate derivatives
is a `ℂ`-derivation of `𝒪(U)` into covector fields along the coordinate domain, so the universal
property of `Ω[𝒪(U)⁄ℂ]` and then that of the exterior power turn the pointwise wedge of covectors
into `chartEvaluation`. By construction it takes the algebraic exterior derivative to the
analytic one.

Analytic differential forms are then `Algebra.DeRham.Form ℂ 𝒪(U) p` modulo the forms whose
evaluation vanishes in every chart. These relations include analytic identities such as the
chain rule.

In degrees above the complex dimension the evaluation target is zero, so the resulting forms
vanish.
-/

noncomputable section

open _root_.CategoryTheory _root_.OAI.Analysis.DifferentialForms.ExactWedge.DifferentialForm _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

section
namespace ComplexPoint

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

noncomputable instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionPresheafAlgebra
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) :
    Algebra ℂ ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionPresheaf X d).obj U) :=
  inferInstanceAs (Algebra ℂ
    C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)); ℂ⟯)

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. For analytic
opens `V ⊆ U`, this `ℂ`-algebra homomorphism sends a holomorphic function on `U` to its
restriction to `V`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V) :
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionPresheaf X d).obj U : Type) →ₐ[ℂ]
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionPresheaf X d).obj V : Type) where
  toRingHom := ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionSheaf X d).presheaf.map i).hom
  commutes' _ := rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom_id [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d (𝟙 U) = AlgHom.id ℂ _ := rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom_comp [SmoothOfRelativeDimension d X.hom]
    {U V W : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d (i ≫ j) =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d j).comp
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i) := rfl

/-- Let `X` be a smooth complex scheme of dimension `d` and `U` an analytic open in `X(ℂ)`. This is
the complex algebra of holomorphic functions `U → ℂ`, with pointwise operations, defined using
the chosen analytic charts. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) :=
  ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionPresheaf X d).obj U : Type)

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. For an analytic
open `U` and the chosen chart `e` at `z`, this is the set of coordinates `y` in the chart target
such that `e.symm(y) ∈ U`. It is an open subset of `ℂ^d`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    Set (Fin d → ℂ) :=
  (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).target ∩
    (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm ⁻¹'
      ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) :
        Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    IsOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) := by
  simpa [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain, extChartAt_target, extChartAt_coe_symm] using
    (chartAt (Fin d → ℂ) z).isOpen_inter_preimage_symm
      (Opposite.unop U).isOpen

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. For an analytic
open `U` and a holomorphic function `f : U → ℂ`, this total function on `X(ℂ)` equals `f` on `U`
and zero outside `U`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendedSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X → ℂ :=
  Function.extend Subtype.val f.1 0

lemma extendedSection_contMDiffWithinAt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {x : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X}
    (hx : x ∈ (Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))) :
    ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendedSection X d U f)
      ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) :
        Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) x := by
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff
    (U := (Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))
    (x := ⟨x, hx⟩)).mp
  simpa only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendedSection, Subtype.val_injective.extend_apply] using
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionSheaf_section_analytic X d f).contMDiffAt
      (x := ⟨x, hx⟩)

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. For a holomorphic
function `f` on `U`, this is its coordinate expression `f ∘ e.symm` on `D`, defined as a total
function by first extending `f` by zero outside `U`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) : (Fin d → ℂ) → ℂ :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendedSection X d U f ∘
    (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffWithinAt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    ContDiffWithinAt ℂ ω (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y := by
  have hsymm : ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ (Fin d → ℂ)) ω
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y := by
    exact (contMDiffOn_extChartAt_symm
      (I := modelWithCornersSelf ℂ (Fin d → ℂ)) z y hy.1).mono Set.inter_subset_left
  have hext : ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendedSection X d U f)
      ((Opposite.unop U : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) :
        Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y) :=
    extendedSection_contMDiffWithinAt X d U f hy.2
  exact (hext.comp y hsymm (fun _ h ↦ h.2)).contDiffWithinAt

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffOn [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) :
    ContDiffOn ℂ ω (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :=
  fun _ hy ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffWithinAt X d U z f hy

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f y =
      f.1 ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y, hy.2⟩ := by
  change Function.extend Subtype.val f.1 0
      (Subtype.val ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y,
        hy.2⟩) = _
  rw [Subtype.val_injective.extend_apply]

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. For a holomorphic
function `f` on `U`, this is the complex Fréchet derivative of `f ∘ e.symm` within `D` at `y`.
Its value is a continuous complex linear functional on `ℂ^d`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (y : Fin d → ℂ) :
    (Fin d → ℂ) →L[ℂ] ℂ :=
  fderivWithin ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_add [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f g : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (f + g) y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z f y +
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z g y := by
  let S := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z
  have hEq : Set.EqOn (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z (f + g))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f + _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z g) S := by
    intro w hw
    simp only [Pi.add_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_add ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffWithinAt X d U z f hy).differentiableWithinAt (by simp))
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffWithinAt X d U z g hy).differentiableWithinAt (by simp))

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_smul [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (c : ℂ)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (c • f) y =
      c • _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z f y := by
  let S := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z
  have hEq : Set.EqOn (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z (c • f))
      (c • _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f) S := by
    intro w hw
    simp only [Pi.smul_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_const_smul_field c
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_mul [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f g : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (f * g) y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f y • _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z g y +
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z g y •
          _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z f y := by
  let S := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z
  have hEq : Set.EqOn (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z (f * g))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f * _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z g) S := by
    intro w hw
    simp only [Pi.mul_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_mul ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffWithinAt X d U z f hy).differentiableWithinAt (by simp))
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffWithinAt X d U z g hy).differentiableWithinAt (by simp))

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_algebraMap [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (c : ℂ) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z
      (algebraMap ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) c) y = 0 := by
  let S := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z
  have hEq : Set.EqOn
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z
        (algebraMap ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) c))
      (fun _ ↦ c) S := by
    intro w hw
    simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact congrFun
    (fderivWithin_const (𝕜 := ℂ) (E := Fin d → ℂ) (s := S) c) y

/-! ### Reading holomorphic functions in a fixed chart -/

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. This `ℂ`-algebra
homomorphism sends each holomorphic function `f` on `U` to the function `y ↦ f(e.symm(y))` on
`D`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionAlgHom [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U →ₐ[ℂ] (↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → ℂ) where
  toFun f y := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f y.1
  map_one' := by funext y; simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ y.2]; rfl
  map_mul' f g := by
    funext y
    simp only [Pi.mul_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ y.2]
    rfl
  map_zero' := by funext y; simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ y.2]; rfl
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ y.2]
    rfl
  commutes' c := by funext y; simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ y.2]; rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionAlgHom_apply [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (y : ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionAlgHom X d U z f y = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f y.1 := rfl

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. For a complex
vector space `V`, functions `D → V` form a module over `𝒪(U)`, the holomorphic functions on `U`,
by `(f • v)(y) = f(e.symm(y)) • v(y)`. This is that module structure. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartFieldModule [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (V : Type) [AddCommGroup V] [Module ℂ V] :
    Module (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → V) :=
  Module.compHom _ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionAlgHom X d U z).toRingHom

attribute [local instance] _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartFieldModule

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartFieldModule_smul_apply [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (V : Type) [AddCommGroup V] [Module ℂ V]
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (F : ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → V)
    (y : ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    (f • F) y = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f y.1 • F y := rfl

/-- The scalar actions of `ℂ` and of the holomorphic functions on chart fields are compatible. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartFieldTower [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (V : Type) [AddCommGroup V] [Module ℂ V] :
    IsScalarTower ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U)
      (↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → V) := by
  refine ⟨fun c f F => ?_⟩
  funext y
  have h : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z (c • f) y.1 = c * _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f y.1 := by
    simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ y.2]; rfl
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartFieldModule_smul_apply, Pi.smul_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartFieldModule_smul_apply, h, mul_smul]

attribute [local instance] _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartFieldTower

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. This
`ℂ`-derivation sends a holomorphic function `f` on `U` to the covector field `y ↦ D(f ∘
e.symm)(y)` on `D`. Multiplication by holomorphic functions is evaluated in these coordinates,
so the derivative obeys the Leibniz rule. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartDerivation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    Derivation ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U)
      (↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → ((Fin d → ℂ) →L[ℂ] ℂ)) where
  toFun f y := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z f y.1
  map_add' f g := by
    funext y
    exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_add X d U z f g y.2
  map_smul' c f := by
    funext y
    exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_smul X d U z c f y.2
  map_one_eq_zero' := by
    funext y
    show _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z 1 y.1 = 0
    rw [show (1 : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) =
      algebraMap ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) 1 by simp]
    exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_algebraMap X d U z 1 y.2
  leibniz' f g := by
    funext y
    exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_mul X d U z f g y.2

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartDerivation_apply [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (y : ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartDerivation X d U z f y = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z f y.1 := rfl

lemma update_eval {p : ℕ} {V W : Type*} (L : Fin p → V → W) (i : Fin p)
    (a : V → W) (y : V) :
    (fun j => Function.update L i a j y) = Function.update (fun j => L j y) i (a y) := by
  funext j
  by_cases h : j = i <;> simp [h]

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. For a natural
number `p`, this alternating multilinear map sends `p` covector fields on `D` to their pointwise
exterior product. At `y`, it gives an alternating continuous `p`-linear form on `ℂ^d`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartWedge [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ) :
    (↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → ((Fin d → ℂ) →L[ℂ] ℂ))
      [⋀^Fin p]→ₗ[_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U]
      (↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)) where
  toFun L y := _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) fun i => L i y
  map_update_add' := by
    intro instDec L i a b
    obtain rfl : instDec = instDecidableEqFin p := Subsingleton.elim _ _
    funext y
    show _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) (fun j => Function.update L i (a + b) j y) =
      _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) (fun j => Function.update L i a j y) +
        _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) (fun j => Function.update L i b j y)
    rw [update_eval, update_eval, update_eval, Pi.add_apply, _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_update_add]
  map_update_smul' := by
    intro instDec L i f a
    obtain rfl : instDec = instDecidableEqFin p := Subsingleton.elim _ _
    funext y
    show _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) (fun j => Function.update L i (f • a) j y) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f y.1 •
        _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) (fun j => Function.update L i a j y)
    rw [update_eval, update_eval, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartFieldModule_smul_apply,
      _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_update_smul]
  map_eq_zero_of_eq' L i j h hij := by
    funext y
    exact _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_eq_zero_of_eq _ i j (congrFun h y) hij

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartWedge_apply [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (L : Fin p → ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → ((Fin d → ℂ) →L[ℂ] ℂ))
    (y : ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartWedge X d U z p L y = _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) fun i => L i y := rfl

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. Let `𝒪(U)` be the
algebra of holomorphic functions. This `𝒪(U)`-linear map evaluates algebraic Kähler `p`-forms as
alternating-form fields on `D`: it sends `a₀ da₁ ∧ ⋯ ∧ daₚ` to the coordinate value of `a₀`
times the wedge of the coordinate derivatives of the `a_j`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationHolo [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ) :
    _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p →ₗ[_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U]
      (↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)) :=
  exteriorPower.alternatingMapLinearEquiv
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartWedge X d U z p).compLinearMap
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartDerivation X d U z).liftKaehlerDifferential)

lemma chartEvaluationHolo_mk [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a₀ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (v : Fin p → _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U)
    (y : ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationHolo X d U z p
        (_root_.OAI.Algebra.DeRham.Basic.mk ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p a₀ v) y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z a₀ y.1 •
        _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
          fun i => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (v i) y.1 := by
  show _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationHolo X d U z p
    (a₀ • _root_.OAI.Algebra.DeRham.Basic.exact ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p v) y = _
  rw [map_smul, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartFieldModule_smul_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationHolo, _root_.OAI.Algebra.DeRham.Basic.exact,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simp

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. For any type `V`
with zero, this extends a function `D → V` to `ℂ^d` by assigning zero outside `D`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    {V : Type} [Zero V] (F : ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → V) : (Fin d → ℂ) → V :=
  Function.extend Subtype.val F 0

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero_apply_of_mem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    {V : Type} [Zero V] (F : ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → V)
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero X d U z F y = F ⟨y, hy⟩ :=
  Subtype.val_injective.extend_apply F 0 ⟨y, hy⟩

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero_apply_of_notMem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    {V : Type} [Zero V] (F : ↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → V)
    {y : Fin d → ℂ} (hy : y ∉ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero X d U z F y = 0 := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero, Function.extend_apply' _ _ _ ?_]
  · rfl
  · rintro ⟨⟨w, hw⟩, rfl⟩
    exact hy hw

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. For a complex
vector space `V`, this is the complex linear map from functions `D → V` to functions `ℂ^d → V`
that extends by zero off `D`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZeroLinear [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (V : Type) [AddCommGroup V] [Module ℂ V] :
    (↥(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) → V) →ₗ[ℂ] ((Fin d → ℂ) → V) where
  toFun := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero X d U z
  map_add' F G := by
    funext y
    by_cases hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z
    · simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero_apply_of_mem X d U z _ hy]
    · simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero_apply_of_notMem X d U z _ hy]
  map_smul' c F := by
    funext y
    by_cases hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z
    · simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero_apply_of_mem X d U z _ hy]
    · simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero_apply_of_notMem X d U z _ hy]

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. This complex
linear map evaluates algebraic Kähler `p`-forms of `𝒪(U)` as alternating continuous `p`-linear
forms on `ℂ^d` at each point of `D`, using coordinate derivatives. The resulting field is
extended by zero off `D`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ) :
    _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      ((Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZeroLinear X d U z _).comp
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationHolo X d U z p).restrictScalars ℂ)

lemma chartEvaluation_apply_of_mem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ y = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationHolo X d U z p θ ⟨y, hy⟩ :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.extendByZero_apply_of_mem X d U z _ hy

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_zero [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p 0 = 0 :=
  map_zero (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p)

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_add [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a b : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p (a + b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p a + _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p b :=
  map_add (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p) a b

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_smul [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ) (c : ℂ)
    (a : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p (c • a) = c • _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p a :=
  map_smul (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p) c a

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_neg [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p (-a) = -_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p a :=
  map_neg (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p) a

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_sub [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a b : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p (a - b) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p a - _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p b :=
  map_sub (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p) a b

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. For holomorphic
functions `a₀, v₀, …, v_{p-1}` on `U`, this field evaluates the generator `a₀ dv₀ ∧ ⋯ ∧
dv_{p-1}` as `a₀(e.symm(y))` times the wedge of the coordinate derivatives of the `v_j` at `y`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a₀ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (v : Fin p → _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) :
    (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  fun y => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z a₀ y •
    _root_.OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) fun i => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (v i) y

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a₀ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (v : Fin p → _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U)
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p
        (_root_.OAI.Algebra.DeRham.Basic.mk ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p a₀ v) y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation X d U z p a₀ v y := by
  rw [chartEvaluation_apply_of_mem X d U z p _ hy, chartEvaluationHolo_mk]
  rfl

lemma chartEvaluation_mk_eqOn [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a₀ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (v : Fin p → _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) :
    Set.EqOn (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p
        (_root_.OAI.Algebra.DeRham.Basic.mk ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p a₀ v))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation X d U z p a₀ v) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :=
  fun _ hy => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U z p a₀ v hy

/-- Exterior differentiation of `a₀ * d v₀ ∧ ⋯ ∧ d vₚ₋₁` inserts the coefficient as the first
differential. -/
lemma extDerivWithin_chartGeneratorEvaluation
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a₀ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (v : Fin p → _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U)
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    extDerivWithin (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation X d U z p a₀ v)
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation X d U z (p + 1) 1 (Fin.cons a₀ v) y := by
  have h := _root_.OAI.Analysis.DifferentialForms.ExactWedge.DifferentialForm.extDerivWithin_smul_exactWedgeWithin (Fin d → ℂ) p
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z a₀)
    (fun i ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z (v i))
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z) hy
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffOn X d U z a₀)
    (fun i ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffOn X d U z (v i))
  rw [show _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation X d U z p a₀ v =
      (fun w ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z a₀ w •
        _root_.OAI.Analysis.DifferentialForms.ExactWedge.DifferentialForm.exactWedgeWithin (Fin d → ℂ) p
          (fun i ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z (v i))
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) w) from rfl]
  rw [h]
  simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential]
  rw [show _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z (1 : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) y = 1 by
        simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ hy]
        rfl, one_smul]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

lemma chartGeneratorEvaluation_differentiableWithinAt
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (a₀ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (v : Fin p → _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U)
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    DifferentiableWithinAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation X d U z p a₀ v)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y := by
  exact DifferentiableWithinAt.smul
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffWithinAt X d U z a₀ hy).differentiableWithinAt (by simp))
    (_root_.OAI.Analysis.DifferentialForms.ExactWedge.DifferentialForm.exactWedgeWithin_differentiableWithinAt (Fin d → ℂ) p
      (fun i ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z (v i))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z) hy
      (fun i ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffOn X d U z (v i)))

lemma chartEvaluation_differentiableWithinAt
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    DifferentiableWithinAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y := by
  induction θ using _root_.OAI.Algebra.DeRham.Basic.mk_induction with
  | mk a₀ v =>
      exact ((chartGeneratorEvaluation_differentiableWithinAt X d U z p a₀ v hy).congr
        (fun w hw => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U z p a₀ v hw)
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U z p a₀ v hy))
  | zero =>
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_zero]
      exact differentiableWithinAt_const (c := (0 : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ))
  | add a b ha hb => rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_add]; exact ha.add hb
  | smul c a ha => rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_smul]; exact ha.const_smul c

lemma extDerivWithin_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℕ}
    (s : Set E) (x : E) :
    extDerivWithin (0 : E → E [⋀^Fin p]→L[ℂ] ℂ) s x = 0 := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply, fderivWithin_zero]

/-- Fixed-chart evaluation intertwines the algebraic and the analytic exterior derivative. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_differential
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z (p + 1)
        (_root_.OAI.Algebra.DeRham.Basic.differential ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p θ) y =
      extDerivWithin (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ)
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) y := by
  induction θ using _root_.OAI.Algebra.DeRham.Basic.mk_induction with
  | mk a₀ v =>
      rw [_root_.OAI.Algebra.DeRham.Basic.differential_mk, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U z (p + 1) _ _ hy,
        extDerivWithin_congr' (chartEvaluation_mk_eqOn X d U z p a₀ v) hy,
        extDerivWithin_chartGeneratorEvaluation X d U z p a₀ v hy]
  | zero => simp [extDerivWithin_zero]
  | add a b ha hb =>
      rw [map_add, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_add, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_add, Pi.add_apply, ha, hb,
        extDerivWithin_add ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)
          (chartEvaluation_differentiableWithinAt X d U z p a hy)
          (chartEvaluation_differentiableWithinAt X d U z p b hy)]
  | smul c a ha =>
      rw [map_smul, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_smul, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_smul, Pi.smul_apply, ha,
        extDerivWithin_smul c _
          ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)]

/-- Let `X` be a smooth complex scheme of dimension `d`, `U ⊆ X(ℂ)` open, and `e` the chosen chart
at `z`. Its coordinate domain over `U` is `D = {y ∈ e.target | e.symm y ∈ U}`. For a natural
number `p` and a coordinate point `y`, this complex linear map evaluates an algebraic Kähler
`p`-form of `𝒪(U)` at `y` using coordinate derivatives, producing an alternating continuous
`p`-linear form on `ℂ^d`. Its value is zero off `D`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationAt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ) (y : Fin d → ℂ) :
    _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  (LinearMap.proj y).comp (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p)

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. For an analytic
open `U`, this is the complex subspace of algebraic Kähler `p`-forms of `𝒪(U)` whose evaluations
by coordinate derivatives vanish at every point in every chosen analytic chart. These are the
relations imposed to obtain analytic differential forms. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (_root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p) :=
  ⨅ (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), ⨅ (y : Fin d → ℂ),
    ⨅ (_ : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z),
      LinearMap.ker (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationAt X d U z p y)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (p : ℕ)
    (θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p) :
    θ ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p ↔
      ∀ z y, y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z →
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ y = 0 := by
  simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel, Submodule.mem_iInf, LinearMap.mem_ker, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationAt]

/-- Coordinate-zero identities remain coordinate-zero after exterior differentiation. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.differential_mem_chartEvaluationKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (p : ℕ)
    {θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p}
    (hθ : θ ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p) :
    _root_.OAI.Algebra.DeRham.Basic.differential ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p θ ∈
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U (p + 1) := by
  have hθ' := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X d U p θ).1 hθ
  refine (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X d U (p + 1) _).2 fun z y hy ↦ ?_
  have hEq : Set.EqOn (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ) 0
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z) := fun w hw ↦ hθ' z w hw
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_differential X d U z p θ hy, extDerivWithin_congr' hEq hy,
    extDerivWithin_zero]

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. For analytic
opens `V ⊆ U` and a natural number `p`, restriction `𝒪(U) → 𝒪(V)` induces this map on algebraic
Kähler `p`-forms, sending `a₀ da₁ ∧ ⋯ ∧ daₚ` to the form obtained by restricting each function
to `V`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d V) p :=
  _root_.OAI.Algebra.DeRham.Basic.map ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i) p

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_id [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (p : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d (𝟙 U) p = LinearMap.id := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom_id, _root_.OAI.Algebra.DeRham.Basic.map_id]

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_comp [SmoothOfRelativeDimension d X.hom]
    {U V W : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (p : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d (i ≫ j) p =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d j p).comp (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i p) := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom_comp, _root_.OAI.Algebra.DeRham.Basic.map_comp]

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_mk [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (a₀ : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (v : Fin p → _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i p (_root_.OAI.Algebra.DeRham.Basic.mk ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p a₀ v) =
      _root_.OAI.Algebra.DeRham.Basic.mk ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d V) p
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i a₀)
        fun k => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i (v k) :=
  _root_.OAI.Algebra.DeRham.Basic.map_mk ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i) p a₀ v

/-- Fixed-chart values of holomorphic functions commute with restriction. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_holomorphicRestrictionAlgHom
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d V z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d V z (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i f) y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f y := by
  have hyU : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z :=
    ⟨hy.1, leOfHom i.unop hy.2⟩
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d V z _ hy,
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X d U z _ hyU]
  rfl

/-- Fixed-chart derivatives of holomorphic functions commute with restriction. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_holomorphicRestrictionAlgHom
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (f : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d V z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d V z
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i f) y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z f y := by
  have hyU : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z :=
    ⟨hy.1, leOfHom i.unop hy.2⟩
  have heq : Filter.EventuallyEq (nhds y)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d V z
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i f))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection X d U z f) := by
    filter_upwards [(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d V z).mem_nhds hy] with w hw
    exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_holomorphicRestrictionAlgHom X d i z f hw
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential,
    fderivWithin_of_isOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d V z) hy,
    fderivWithin_of_isOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X d U z) hyU]
  exact heq.fderiv_eq

/-- Fixed-chart evaluation of a differential form commutes with restriction. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_formRestriction
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d V z) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d V z p (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i p θ) y =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ y := by
  have hyU : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U z := ⟨hy.1, leOfHom i.unop hy.2⟩
  induction θ using _root_.OAI.Algebra.DeRham.Basic.mk_induction with
  | mk a₀ v =>
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_mk, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d V z p _ _ hy,
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X d U z p a₀ v hyU]
      simp only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation]
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSection_holomorphicRestrictionAlgHom X d i z a₀ hy]
      have hd :
          (fun j ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d V z
            (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i (v j)) y) =
          (fun j ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X d U z (v j) y) := by
        funext j
        exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential_holomorphicRestrictionAlgHom X d i z (v j) hy
      rw [hd]
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul c a ha => simp [ha]

/-- Restriction preserves forms that vanish in every chart. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_mem_chartEvaluationKernel
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {θ : _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p}
    (hθ : θ ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i p θ ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d V p := by
  refine (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X d V p _).2 fun z y hy ↦ ?_
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_formRestriction X d i z p θ hy]
  exact (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X d U p θ).1 hθ z y
    ⟨hy.1, leOfHom i.unop hy.2⟩

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. For an analytic
open `U` and a natural number `p`, holomorphic `p`-forms are defined as `⋀^p_{𝒪(U)} Ω_{𝒪(U)/ℂ}`
modulo the forms whose evaluations by coordinate derivatives vanish everywhere in every chosen
chart. Here `𝒪(U)` is the algebra of holomorphic functions on `U`. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (p : ℕ) :=
  _root_.OAI.Algebra.DeRham.Basic.Form ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p ⧸
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. For an analytic
open `U`, this complex linear map sends `c ∈ ℂ` to the zero-form represented by the constant
holomorphic function `c` in the quotient of algebraic forms by those vanishing in all charts. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) :
    ℂ →ₗ[ℂ] _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U 0 :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U 0).mkQ.comp
    (_root_.OAI.Algebra.DeRham.Basic.ofConstant ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U))

/-- Let `X` be a smooth complex scheme of dimension `d` and `U` an analytic open in `X(ℂ)`. This
complex linear exterior derivative sends holomorphic `p`-forms to `(p+1)`-forms. It descends the
Kähler exterior derivative to the quotient by forms whose coordinate derivative evaluations
vanish everywhere. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (p : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p →ₗ[ℂ] _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U (p + 1) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p).liftQ
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U (p + 1)).mkQ.comp
      (_root_.OAI.Algebra.DeRham.Basic.differential ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p)) (by
        intro θ hθ
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.differential_mem_chartEvaluationKernel X d U p hθ)

/-- Let `X` be a smooth complex scheme of dimension `d` and `V ⊆ U` analytic opens. This complex
linear map restricts holomorphic `p`-forms from `U` to `V`, by restricting their coefficient
functions and passing to the quotient by forms whose coordinate evaluations vanish. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p →ₗ[ℂ] _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d V p :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p).liftQ
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d V p).mkQ.comp (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i p)) (by
      intro θ hθ
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_mem_chartEvaluationKernel X d i p hθ)

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction_ofConstant
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V) (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i 0
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d U c) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d V c := by
  change Submodule.Quotient.mk
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i 0 (_root_.OAI.Algebra.DeRham.Basic.ofConstant ℂ _ c)) = _
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction, _root_.OAI.Algebra.DeRham.Basic.map_ofConstant]
  rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential_ofConstant
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (c : ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d U 0
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d U c) = 0 := by
  change Submodule.Quotient.mk
      (_root_.OAI.Algebra.DeRham.Basic.differential ℂ _ 0 (_root_.OAI.Algebra.DeRham.Basic.ofConstant ℂ _ c)) = 0
  rw [_root_.OAI.Algebra.DeRham.Basic.differential_ofConstant]
  exact Submodule.Quotient.mk_zero _

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction_id [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (p : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d (𝟙 U) p = LinearMap.id := by
  apply LinearMap.ext
  intro θ
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p) θ
  change Submodule.Quotient.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d (𝟙 U) p θ) = _
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_id]
  rfl

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction_comp [SmoothOfRelativeDimension d X.hom]
    {U V W : (Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (p : ℕ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d (i ≫ j) p =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d j p).comp
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i p) := by
  apply LinearMap.ext
  intro θ
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p) θ
  change Submodule.Quotient.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d (i ≫ j) p θ) = _
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.formRestriction_comp]
  rfl

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Hodge.AnalyticDifferentialForms
