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
import Mathlib.AlgebraicGeometry.AffineSpace

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Topology.Algebra.MvPolynomial

namespace OAI.AlgebraicGeometry.ComplexPoint.AffineSpace

open _root_.AlgebraicGeometry

/-!
# Complex points of affine space

The complex points of algebraic affine space are canonically homeomorphic to tuples of complex
numbers. The proof identifies global regular functions with multivariate polynomials. It then uses
the localization description of sections on principal opens to handle every local regular function
appearing in the analytic topology.
-/

section

open _root_.CategoryTheory _root_.Topology

section
section

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

noncomputable section

/-- Evaluation of a global section at a complex point is pullback of that section to `Spec ℂ`. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_top_eq_appTop {X : Over (Spec ↧ℂ)}
    (s : Γ(X.left, ⊤)) (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ s z = (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appTop s) := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate, dite_eq_left (by exact trivial)]
  have h := Scheme.germ_stalkClosedPointTo (R := ↧ℂ) (X := X.left) z.left ⊤ trivial
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) s

/-- Evaluation of a global regular function is continuous in the analytic topology. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_evaluate_top {X : Over (Spec ↧ℂ)}
    (s : Γ(X.left, ⊤)) :
    @Continuous (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) ℂ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology inferInstance
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ s) := by
  rw [continuous_def]
  intro V hV
  simpa [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen] using
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.isOpen_overOpen_inter_preimage (X := X) (⊤ : X.left.Opens) s V hV

/-- Complex affine space as a scheme over `Spec ℂ`. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace (n : Type) : Scheme :=
  AffineSpace n (Spec ↧ℂ)

/-- Algebraic coordinates identify complex points of affine space with tuples of complex numbers. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv (n : Type) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ)) ≃ (n → ℂ) where
  toFun z i :=
    (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appTop (AffineSpace.coord (Spec ↧ℂ) i))
  invFun v :=
    Over.homMk (AffineSpace.homOfVector (𝟙 _)
      (fun i ↦ (Scheme.ΓSpecIso ↧ℂ).inv (v i))) (by simp)
  left_inv z := by
    apply Over.OverMorphism.ext
    apply AffineSpace.hom_ext
    · simpa using (Over.w z).symm
    · intro i
      simp
  right_inv v := by
    funext i
    simp

@[simp]
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv_apply (n : Type)
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ))) (i : n) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n z i =
      (Scheme.ΓSpecIso ↧ℂ).hom
        (z.left.appTop (AffineSpace.coord (Spec ↧ℂ) i)) :=
  rfl

/-- The algebraic coordinate equivalence is continuous for the analytic topology. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpaceEquiv (n : Type) :
    @Continuous
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ)))
      (n → ℂ) _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology inferInstance (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n) := by
  apply @continuous_pi
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ)))
    n (fun _ ↦ ℂ) _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology (fun _ ↦ inferInstance) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n)
  intro i
  let s := AffineSpace.coord (Spec ↧ℂ) i
  have heq : (fun z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ)) ↦
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n z i) = _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ s :=
    funext fun z ↦ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_top_eq_appTop s z).symm
  rw [heq]
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_evaluate_top (X := Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ)) s

/-- The polynomial represented by a global regular function on complex affine space. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineGlobalPolynomial {n : Type} (s : Γ(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n, ⊤)) :
    MvPolynomial n ℂ :=
  (Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).hom
    ((AffineSpace.SpecIso n ↧ℂ).inv.appTop s)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.SpecIso_hom_appTop_affineGlobalPolynomial {n : Type}
    (s : Γ(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n, ⊤)) :
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop
        ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineGlobalPolynomial s)) = s := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineGlobalPolynomial, Iso.hom_inv_id_apply]
  change ((AffineSpace.SpecIso n ↧ℂ).inv.appTop ≫
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop) s = s
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rfl

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.SpecIso_hom_appTop_X {n : Type} (i : n) :
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop
        ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (MvPolynomial.X i)) =
      AffineSpace.coord (Spec ↧ℂ) i := by
  rw [← AffineSpace.SpecIso_inv_appTop_coord ↧ℂ i]
  change ((AffineSpace.SpecIso n ↧ℂ).inv.appTop ≫
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop)
      (AffineSpace.coord (Spec ↧ℂ) i) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rfl

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.SpecIso_hom_appTop_C {n : Type} (c : ℂ) :
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop
        ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (MvPolynomial.C c)) =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ).appTop
        ((Scheme.ΓSpecIso ↧ℂ).inv c) := by
  rw [AffineSpace.SpecIso_hom_appTop]
  simp

/-- In affine coordinates, evaluation of a global section is evaluation of its polynomial. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_affineSpaceEquiv_symm_top {n : Type} (s : Γ(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n, ⊤))
    (v : n → ℂ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ s ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm v) =
      MvPolynomial.eval v (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineGlobalPolynomial s) := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_top_eq_appTop]
  let h := ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm v).left
  let φ : MvPolynomial n ℂ →+* ℂ :=
    ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv ≫
      (AffineSpace.SpecIso n ↧ℂ).hom.appTop ≫ h.appTop ≫
      (Scheme.ΓSpecIso ↧ℂ).hom).hom
  have hφ : φ = MvPolynomial.eval v := by
    apply MvPolynomial.ringHom_ext
    · intro c
      dsimp [φ]
      rw [MvPolynomial.eval_C]
      change (Scheme.ΓSpecIso ↧ℂ).hom
        (h.appTop ((AffineSpace.SpecIso n ↧ℂ).hom.appTop
          ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (MvPolynomial.C c)))) = c
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.SpecIso_hom_appTop_C]
      change (Scheme.ΓSpecIso ↧ℂ).hom
        (((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ).appTop ≫
          (AffineSpace.homOfVector (𝟙 _) fun i ↦
            (Scheme.ΓSpecIso ↧ℂ).inv (v i)).appTop)
              ((Scheme.ΓSpecIso ↧ℂ).inv c)) = c
      rw [← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over, Scheme.Hom.id_appTop]
      simp
    · intro i
      dsimp [φ]
      rw [MvPolynomial.eval_X]
      change (Scheme.ΓSpecIso ↧ℂ).hom
        (h.appTop ((AffineSpace.SpecIso n ↧ℂ).hom.appTop
          ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (MvPolynomial.X i)))) = v i
      rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.SpecIso_hom_appTop_X]
      simp [h, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv]
  calc
    (Scheme.ΓSpecIso ↧ℂ).hom (h.appTop s) =
        (Scheme.ΓSpecIso ↧ℂ).hom
          (h.appTop ((AffineSpace.SpecIso n ↧ℂ).hom.appTop
            ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv
              (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineGlobalPolynomial s)))) := by
                rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.SpecIso_hom_appTop_affineGlobalPolynomial]
    _ = φ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineGlobalPolynomial s) := rfl
    _ = MvPolynomial.eval v (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineGlobalPolynomial s) := by rw [hφ]

/-- Pullback of a global affine regular function along the coordinate inverse is continuous. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_evaluate_top_affineSpaceEquiv_symm {n : Type}
    (s : Γ(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n, ⊤)) :
    Continuous fun v : n → ℂ ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ s ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm v) := by
  simpa only [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.evaluate_affineSpaceEquiv_symm_top] using
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineGlobalPolynomial s).continuous_eval

/-- Principal opens of complex affine space pull back to Euclidean open sets. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen {n : Type}
    (s : Γ(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n, ⊤)) :
    IsOpen ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm ⁻¹'
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).basicOpen s)) := by
  rw [show (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm ⁻¹'
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).basicOpen s) =
      {v | _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ s ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm v) ≠ 0} by
    ext v
    exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ)) (U := ⊤) s _ trivial]
  exact isOpen_ne_fun (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_evaluate_top_affineSpaceEquiv_symm s) continuous_const

/-- Evaluation on a principal open is continuous on the corresponding Euclidean open set. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuousOn_evaluate_basicOpen_affineSpaceEquiv_symm {n : Type}
    (f : Γ(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n, ⊤))
    (t : Γ(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n, (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).basicOpen f)) :
    ContinuousOn
      (fun v : n → ℂ ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).basicOpen f) t
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm v))
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm ⁻¹'
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).basicOpen f)) := by
  obtain ⟨k, a, h⟩ :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.exists_evaluate_basicOpen_eq_div (X := Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ))
      (isAffineOpen_top (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n)) f t
  have ha := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_evaluate_top_affineSpaceEquiv_symm a
  have hf := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_evaluate_top_affineSpaceEquiv_symm f
  have hrat : ContinuousOn
      (fun v : n → ℂ ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ a ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm v) /
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ⊤ f ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm v) ^ k)
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm ⁻¹'
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).basicOpen f)) :=
    ha.continuousOn.div (hf.pow k).continuousOn fun v hv ↦
      pow_ne_zero k ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
        (X := Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ)) (U := ⊤) f _ trivial).mp hv)
  exact hrat.congr fun v hv ↦ h _ hv

/-- The inverse coordinate map is continuous for every local regular-function subbasis set. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpaceEquiv_symm (n : Type) :
    @Continuous (n → ℂ)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ)))
      inferInstance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.continuous_iff_analyticSubbasis]
  rintro W ⟨U, s, V, hV, rfl⟩
  apply isOpen_iff_forall_mem_open.mpr
  rintro v ⟨hvU, hvV⟩
  obtain ⟨f, hfU, hvf⟩ :=
    (isAffineOpen_top (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n)).exists_basicOpen_le
      ⟨((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm v).underlying, hvU⟩ trivial
  let t := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).presheaf.map (homOfLE hfU).op s
  let N := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm ⁻¹'
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).basicOpen f) ∩
    (fun w : n → ℂ ↦ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).basicOpen f) t
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm w)) ⁻¹' V
  have hNopen : IsOpen N :=
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuousOn_evaluate_basicOpen_affineSpaceEquiv_symm f t).isOpen_inter_preimage
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen f) hV
  refine ⟨N, ?_, hNopen, ?_⟩
  · rintro w ⟨hwf, hwV⟩
    have hwU : (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm w ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U := hfU hwf
    refine ⟨hwU, ?_⟩
    change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate U s ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm w) ∈ V
    rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate_res hfU s _ hwf]
    exact hwV
  · refine ⟨hvf, ?_⟩
    change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n).basicOpen f) t
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n).symm v) ∈ V
    exact (congrArg (fun c ↦ c ∈ V) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate_res hfU s _ hvf)).mp hvV

/-- Complex affine space with the evaluation topology is ordinary complex affine space. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceHomeomorph (n : Type) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (Over.mk (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexAffineSpace n ↘ Spec ↧ℂ)) ≃ₜ (n → ℂ) where
  toEquiv := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.affineSpaceEquiv n
  continuous_toFun := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpaceEquiv n
  continuous_invFun := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.continuous_affineSpaceEquiv_symm n

end


end
end

end

end OAI.AlgebraicGeometry.ComplexPoint.AffineSpace
