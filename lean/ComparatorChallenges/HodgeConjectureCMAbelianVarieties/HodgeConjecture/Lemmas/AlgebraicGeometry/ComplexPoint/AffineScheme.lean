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
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.Logic.Equiv.PartialEquiv

namespace OAI.AlgebraicGeometry.ComplexPoint.AffineScheme

open _root_.AlgebraicGeometry

/-!
# Complex points of affine schemes

The complex points of `Spec R` are canonically homeomorphic to the space of complex algebra
homomorphisms from `R` to `ℂ`, equipped with the topology of pointwise convergence. The proof of
continuity in the reverse direction uses the localization description of regular functions on
principal opens.
-/

section

open _root_.CategoryTheory _root_.Topology

section
section

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

noncomputable section

variable (R : Type) [CommRing R] [Algebra ℂ R]

/-- The topology of pointwise convergence on complex algebra homomorphisms. -/
noncomputable instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology : TopologicalSpace (R →ₐ[ℂ] ℂ) :=
  TopologicalSpace.induced (fun φ : R →ₐ[ℂ] ℂ ↦ (φ : R → ℂ)) inferInstance

/-- The structure morphism of an affine complex scheme. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap : Spec ↧R ⟶ Spec ↧ℂ :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ R))

/-- Complex points of `Spec R` correspond to complex algebra homomorphisms from `R` to `ℂ`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R)) ≃ (R →ₐ[ℂ] ℂ) where
  toFun z :=
    { toRingHom := (Spec.homEquiv z.left).hom
      commutes' c := by
        have hz := congrArg Spec.preimage (Over.w z)
        have hr : CommRingCat.ofHom (algebraMap ℂ R) ≫ Spec.preimage z.left =
            𝟙 (CommRingCat.of ℂ) := by
          simpa [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap, Spec.preimage_comp] using hz
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hr) c }
  invFun φ := Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) = 𝟙 (Spec ↧ℂ)
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact φ.commutes c)
  left_inv z := Over.OverMorphism.ext (Spec.map_preimage z.left)
  right_inv φ := by
    ext r
    simp [Spec.homEquiv_apply]

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv_apply
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R))) (r : R) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R z r =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ ((Scheme.ΓSpecIso ↧R).inv r) z := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_top_eq_appTop]
  change (Spec.preimage z.left).hom r =
    (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appTop ((Scheme.ΓSpecIso ↧R).inv r))
  have h := Scheme.ΓSpecIso_naturality (Spec.preimage z.left)
  have h' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h)
    ((Scheme.ΓSpecIso ↧R).inv r)
  simpa using h'.symm

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_affineSpecEquiv_symm_top (s : Γ(Spec ↧R, ⊤)) (φ : R →ₐ[ℂ] ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ s ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) =
      φ ((Scheme.ΓSpecIso ↧R).hom s) := by
  calc
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ s ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) =
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ ((Scheme.ΓSpecIso ↧R).inv
          ((Scheme.ΓSpecIso ↧R).hom s)) ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) := by simp
    _ = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ)
          ((Scheme.ΓSpecIso ↧R).hom s) :=
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv_apply R _ _).symm
    _ = φ ((Scheme.ΓSpecIso ↧R).hom s) := by simp

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineAlgebraHom_apply (r : R) :
    Continuous (fun φ : R →ₐ[ℂ] ℂ ↦ φ r) :=
  (continuous_apply r).comp continuous_induced_dom

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpecEquiv :
    @Continuous
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R)))
      (R →ₐ[ℂ] ℂ) _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology R)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R) := by
  rw [continuous_induced_rng]
  exact continuous_pi fun r ↦ by
    simpa only [Function.comp_apply, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv_apply] using
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_evaluate_top (X := Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R))
        ((Scheme.ΓSpecIso ↧R).inv r)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_affineSpecEquiv_symm_preimage_overOpen_basicOpen
    (s : Γ(Spec ↧R, ⊤)) :
    IsOpen ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((Spec ↧R).basicOpen s)) := by
  rw [show (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((Spec ↧R).basicOpen s) =
      {φ | φ ((Scheme.ΓSpecIso ↧R).hom s) ≠ 0} by
    ext φ
    exact (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R)) (U := ⊤)
      s ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) trivial).trans
        (Iff.of_eq (congrArg (· ≠ 0) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_affineSpecEquiv_symm_top R s φ)))]
  exact isOpen_ne_fun
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineAlgebraHom_apply R ((Scheme.ΓSpecIso ↧R).hom s))
    continuous_const

/-- On an affine scheme, evaluation of a section on a principal open is locally a quotient of
evaluations of global sections. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_evaluate_affine_basicOpen_eq_div {X : Over (Spec ↧ℂ)} [IsAffine X.left]
    (f : Γ(X.left, ⊤)) (t : Γ(X.left, X.left.basicOpen f)) :
    ∃ (k : ℕ) (a : Γ(X.left, ⊤)),
      ∀ z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X, z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen (X.left.basicOpen f) →
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate (X.left.basicOpen f) t z = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ a z / _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ f z ^ k :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.exists_evaluate_basicOpen_eq_div (X := X) (isAffineOpen_top X.left) f t

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_evaluate_affineSpec_basicOpen_eq_div
    (f : Γ(Spec ↧R, ⊤))
    (t : Γ(Spec ↧R, (Spec ↧R).basicOpen f)) :
    ∃ (k : ℕ) (a : Γ(Spec ↧R, ⊤)),
      ∀ z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R)),
        z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((Spec ↧R).basicOpen f) →
          _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ((Spec ↧R).basicOpen f) t z =
            _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ a z / _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ f z ^ k := by
  let : IsAffine (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R)).left :=
    inferInstanceAs (IsAffine (Spec ↧R))
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_evaluate_affine_basicOpen_eq_div (X := Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R)) f t

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuousOn_evaluate_affineSpec_basicOpen_equiv_symm
    (f : Γ(Spec ↧R, ⊤))
    (t : Γ(Spec ↧R, (Spec ↧R).basicOpen f)) :
    ContinuousOn
      (fun φ : R →ₐ[ℂ] ℂ ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ((Spec ↧R).basicOpen f) t
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ))
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((Spec ↧R).basicOpen f)) := by
  obtain ⟨k, a, h⟩ := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_evaluate_affineSpec_basicOpen_eq_div R f t
  have ha : Continuous (fun φ : R →ₐ[ℂ] ℂ ↦
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ a ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ)) := by
    simpa only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_affineSpecEquiv_symm_top] using
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineAlgebraHom_apply R ((Scheme.ΓSpecIso ↧R).hom a)
  have hf : Continuous (fun φ : R →ₐ[ℂ] ℂ ↦
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ)) := by
    simpa only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_affineSpecEquiv_symm_top] using
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineAlgebraHom_apply R ((Scheme.ΓSpecIso ↧R).hom f)
  have hrat : ContinuousOn
      (fun φ : R →ₐ[ℂ] ℂ ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ a ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) /
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) ^ k)
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((Spec ↧R).basicOpen f)) :=
    ha.continuousOn.div (hf.pow k).continuousOn fun φ hφ ↦
      pow_ne_zero k ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
        (X := Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R)) (U := ⊤) f _ trivial).mp hφ)
  exact hrat.congr fun φ hφ ↦ h _ hφ

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpecEquiv_symm :
    @Continuous (R →ₐ[ℂ] ℂ)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R)))
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology R) _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.continuous_iff_analyticSubbasis]
  rintro W ⟨U, s, V, hV, rfl⟩
  apply isOpen_iff_forall_mem_open.mpr
  rintro φ ⟨hφU, hφV⟩
  obtain ⟨f, hfU, hφf⟩ :=
    (isAffineOpen_top (Spec ↧R)).exists_basicOpen_le
      ⟨((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ).underlying, hφU⟩ trivial
  let t := (Spec ↧R).presheaf.map (homOfLE hfU).op s
  let N := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((Spec ↧R).basicOpen f) ∩
    (fun ψ : R →ₐ[ℂ] ℂ ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ((Spec ↧R).basicOpen f) t
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm ψ)) ⁻¹' V
  have hNopen : IsOpen N :=
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuousOn_evaluate_affineSpec_basicOpen_equiv_symm R f t).isOpen_inter_preimage
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_affineSpecEquiv_symm_preimage_overOpen_basicOpen R f) hV
  refine ⟨N, ?_, hNopen, ?_⟩
  · rintro ψ ⟨hψf, hψV⟩
    have hψU : (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm ψ ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U := hfU hψf
    refine ⟨hψU, ?_⟩
    change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate U s ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm ψ) ∈ V
    rwa [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate_res hfU s _ hψf]
  · refine ⟨hφf, ?_⟩
    change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ((Spec ↧R).basicOpen f) t
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) ∈ V
    exact (congrArg (fun c ↦ c ∈ V) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate_res hfU s _ hφf)).mp hφV

/-- The complex points of `Spec R` are homeomorphic to the complex algebra homomorphisms
from `R` to `ℂ`, with their topology of pointwise convergence. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecHomeomorph :
    @Homeomorph
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap R)))
      (R →ₐ[ℂ] ℂ) _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineAlgebraHomTopology R) where
  toEquiv := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv R
  continuous_toFun := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpecEquiv R
  continuous_invFun := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpecEquiv_symm R

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.specMap_comp_affineSpecStructureMap (g : A →ₐ[ℂ] B) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap A =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap B := by
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact g.commutes c

/-- The map on complex points contravariantly associated to a complex algebra homomorphism. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecComplexPointMap (g : A →ₐ[ℂ] B) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap B)) →
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap A)) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom))
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.specMap_comp_affineSpecStructureMap g))

/-- Under the affine-point equivalence, an affine scheme map acts by precomposition of algebra
homomorphisms. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv_affineSpecComplexPointMap (g : A →ₐ[ℂ] B)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecStructureMap B))) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv A (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecComplexPointMap g z) =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv B z).comp g := by
  ext a
  simp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecComplexPointMap, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpecEquiv, Spec.preimage_comp]

end

end
end

end

end OAI.AlgebraicGeometry.ComplexPoint.AffineScheme
