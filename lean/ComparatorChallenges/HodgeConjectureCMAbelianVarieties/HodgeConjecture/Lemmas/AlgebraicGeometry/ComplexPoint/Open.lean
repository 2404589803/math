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
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicGeometry.ComplexPoint.Open

open _root_.AlgebraicGeometry

/-!
# Complex points of open subschemes

Analytification respects restriction to an open subscheme. More precisely, complex points of an
open subscheme are canonically homeomorphic to the corresponding open subspace of the complex
points of the ambient scheme. In particular, an open immersion of this form induces an open
embedding on complex points.
-/

section

open _root_.CategoryTheory _root_.Topology

section
section

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

noncomputable section

variable (X : Over (Spec ↧ℂ)) (U : X.left.Opens)

/-- An open subscheme with its induced complex structure. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme : Over (Spec ↧ℂ) :=
  Over.mk (U.ι ≫ X.hom)

/-- The inclusion of an open subscheme as a morphism over `Spec ℂ`. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U ⟶ X :=
  Over.homMk U.ι rfl

/-- The image of a complex point lying in `U` is contained in the image of its inclusion. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.point_range_subset (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hz : z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U) :
    Set.range z.left ⊆ Set.range U.ι := by
  rintro y ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := Spec ↧ℂ) _ _
  subst x
  exact hz

/-- A complex point in an open set factors through the corresponding open subscheme. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.liftToOpen (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hz : z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U) :
    Spec ↧ℂ ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι z.left (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.point_range_subset X U z hz)

@[reassoc (attr := simp)]
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.liftToOpen_fac (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hz : z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.liftToOpen X U z hz ≫ U.ι = z.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- A point of `X` lying in `U`, regarded as a complex point of the open subscheme `U`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.asOpenPoint (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hz : z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U) :=
  Over.homMk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.liftToOpen X U z hz) (by
    change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.liftToOpen X U z hz ≫ (U.ι ≫ X.hom) = 𝟙 _
    rw [← Category.assoc, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.liftToOpen_fac]
    exact Over.w z)

/-- Complex points of an open subscheme are the ambient complex points lying in the open. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U) ≃
      {z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X // z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U} where
  toFun z := ⟨_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U) z, by
    change (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U) z).underlying ∈ U
    rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.underlying_map]
    exact z.underlying.property⟩
  invFun z := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.asOpenPoint X U z.1 z.2
  left_inv z := by
    apply Over.OverMorphism.ext
    symm
    apply IsOpenImmersion.lift_uniq U.ι (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U) z).left
    simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map]
  right_inv z := Subtype.ext (Over.OverMorphism.ext (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.liftToOpen_fac X U z.1 z.2))

@[simp]
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv_coe (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U)) :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U z).1 = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U) z :=
  rfl

/-- The map from an open subscheme to its ambient open subspace is continuous. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_openEquiv :
    @Continuous
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U))
      {z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X // z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U}
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology (TopologicalSpace.induced Subtype.val _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U) :=
  @Continuous.subtype_mk
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U))
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology
    (fun z ↦ z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U))
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.continuous_map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U)) _

/-- Evaluation is unchanged when both a point and a section are transported across equal opens. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_eq {Y : Over (Spec ↧ℂ)}
    {V W : Y.left.Opens} (e : V = W) (t : Γ(Y.left, V)) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate V t z = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate W (Y.left.presheaf.map (eqToHom e.symm).op t) z := by aesop

/-- Evaluation commutes with the equivalence between an open subscheme and its ambient open. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_openEquiv {V : U.toScheme.Opens} (t : Γ(U.toScheme, V))
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U) z) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate V t z := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate_map]
  let e : U.ι ⁻¹ᵁ U.ι ''ᵁ V = V := U.ι.preimage_image_eq V
  let q := U.ι.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv t)
  have hq : q = U.toScheme.presheaf.map (eqToHom e).op t := by
    change ((U.ι.appIso V).inv ≫ U.ι.app (U.ι ''ᵁ V)) t = _
    rw [U.ι.appIso_inv_app]
  calc
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate (U.ι ⁻¹ᵁ U.ι ''ᵁ V) q z =
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate V (U.toScheme.presheaf.map (eqToHom e.symm).op q) z :=
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_eq (Y := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U) e q z
    _ = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate V t z := by
      congr 2
      rw [hq]
      change (U.toScheme.presheaf.map (eqToHom e).op ≫
        U.toScheme.presheaf.map (eqToHom e.symm).op) t = t
      rw [← Functor.map_comp]
      simp
      rfl

/-- The inverse map from the ambient open subspace is continuous. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_openEquiv_symm :
    @Continuous
      {z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X // z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U}
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U))
      (TopologicalSpace.induced Subtype.val _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology) _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).symm := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.continuous_iff_analyticSubbasis]
  rintro W ⟨V, t, O, hO, rfl⟩
  let A : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen (U.ι ''ᵁ V) ∩
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) ⁻¹' O
  have hA : @IsOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology A :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.isOpen_overOpen_inter_preimage _ _ _ hO
  rw [show (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).symm ⁻¹'
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen V ∩ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate V t ⁻¹' O) = Subtype.val ⁻¹' A by
    ext y
    let z := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).symm y
    have hy : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U z = y :=
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).apply_symm_apply y
    rw [← hy]
    simp only [Set.mem_preimage, Equiv.symm_apply_apply, Set.mem_inter_iff]
    change (z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen V ∧ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate V t z ∈ O) ↔
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U) z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen (U.ι ''ᵁ V) ∧
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U) z) ∈ O)
    rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_openEquiv]
    exact and_congr_left' (by simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen])]
  exact @isOpen_induced
    {z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X // z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U}
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology Subtype.val A hA

/-- Analytification of an open subscheme is the corresponding analytic open subspace. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openHomeomorph :
    @Homeomorph
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U))
      {z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X // z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U}
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology (TopologicalSpace.induced Subtype.val _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology) where
  toEquiv := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U
  continuous_toFun := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_openEquiv X U
  continuous_invFun := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_openEquiv_symm X U

/-- Inclusion of an open subscheme induces an open embedding on complex points. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpenEmbedding_map_open :
    IsOpenEmbedding (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U) :
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X U) → _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) := by
  have hU : IsOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.isOpen_overOpen (X := X) U
  have h := hU.isOpenEmbedding_subtypeVal.comp (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openHomeomorph X U).isOpenEmbedding
  simpa [Function.comp_def, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openHomeomorph, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openEquiv] using h

end


end
end

end

end OAI.AlgebraicGeometry.ComplexPoint.Open
