/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections
import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend

namespace OAI.Algebra.Homology.MapExtendNaturality

open _root_.CochainComplex
open _root_.HomologicalComplex

/-! # Naturality of the additive map/extension comparison -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace HomologicalComplex
open _root_.HomologicalComplex

universe u v

variable {C D : Type u} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  {i i' : Type v} {c : ComplexShape i} {c' : ComplexShape i'}

set_option backward.isDefEq.respectTransparency false in
/-- The additive map/extension isomorphism is natural in chain maps. -/
@[reassoc]
lemma mapExtendCanonicalIso_inv_naturality
    (F : Functor C D) [F.Additive] {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') :
    extendMap ((F.mapHomologicalComplex c).map f) e ≫ (_root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F L e).inv =
      (_root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K e).inv ≫
        (F.mapHomologicalComplex c').map (extendMap f e) := by
  rw [Iso.comp_inv_eq, Category.assoc, _root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality F K e f,
    Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality in a transformation out of the identity functor. This
fixes the normalization of restriction after extending a complex by zero. -/
@[reassoc]
lemma mapExtendCanonicalIso_hom_naturality_from_id
    (F : C ⥤ C) [F.Additive] (τ : 𝟭 C ⟶ F) (K : HomologicalComplex C c)
    (e : c.Embedding c') :
    (τ.mapHomologicalComplex c').app (K.extend e) ≫ (_root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K e).hom =
      extendMap ((τ.mapHomologicalComplex c).app K) e := by
  apply HomologicalComplex.Hom.ext
  funext q
  change τ.app (extend.X K (e.r q)) ≫ (_root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalXIso F K (e.r q)).hom =
    extend.mapX ((τ.mapHomologicalComplex c).app K) (e.r q)
  generalize e.r q = x
  cases x with
  | none => exact (Limits.isZero_zero C).eq_of_src _ _
  | some n =>
    change τ.app (K.X n) ≫ 𝟙 _ = τ.app (K.X n)
    simp

end HomologicalComplex

namespace CochainComplex
open _root_.CochainComplex

universe u

variable {C D : Type u} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℕ} (f : K ⟶ L)
  [QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map f)]

/-- If applying an additive functor to a nonnegative chain map gives a
quasi-isomorphism, the same holds for its extension to integer degrees. -/
lemma quasiIso_map_extendMap_nat :
    QuasiIso ((F.mapHomologicalComplex ℤᵘᵖ).map
      (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) := by
  have : QuasiIso ((_root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K ComplexShape.embeddingUpNat).inv ≫
      (F.mapHomologicalComplex ℤᵘᵖ).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) := by
    rw [← _root_.OAI.Algebra.Homology.MapExtendNaturality.HomologicalComplex.mapExtendCanonicalIso_inv_naturality F f ComplexShape.embeddingUpNat]
    infer_instance
  exact quasiIso_of_comp_left
    (_root_.OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K ComplexShape.embeddingUpNat).inv _

end CochainComplex

end

end OAI.Algebra.Homology.MapExtendNaturality
