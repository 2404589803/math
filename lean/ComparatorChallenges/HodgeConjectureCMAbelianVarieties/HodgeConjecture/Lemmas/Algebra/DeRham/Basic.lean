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

import HodgeConjecture.Definitions.Algebra.DeRham.Basic

namespace OAI.Algebra.DeRham.BasicSquared

open _root_.Algebra

/-!
# Algebraic de Rham forms

Lemmas about the definitions in
`HodgeConjecture.Definitions.Algebra.DeRham.Basic`.
-/

noncomputable section

universe u

section
section

open CliffordAlgebra (involute involute_ι)
open TrivSqZeroExt (snd)

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

variable {R A}

variable (R A)

/-- The exterior derivative anticommutes with the grade involution, since it raises the degree
by one. -/
lemma extDeriv_involute (x : _root_.OAI.Algebra.DeRham.Basic.ExtAlg R A) :
    _root_.OAI.Algebra.DeRham.Basic.extDeriv R A (involute x) = -involute (_root_.OAI.Algebra.DeRham.Basic.extDeriv R A x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι ω => simp [_root_.OAI.Algebra.DeRham.Basic.involute_snd_phi]
  | mul x y hx hy =>
      rw [map_mul, _root_.OAI.Algebra.DeRham.Basic.extDeriv_mul, hx, hy, _root_.OAI.Algebra.DeRham.Basic.extDeriv_mul, map_add, map_mul, map_mul,
        CliffordAlgebra.involute_involute]
      simp only [mul_neg, neg_mul, neg_add]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

lemma extDeriv_snd_phi (ω : Ω[A⁄R]) : _root_.OAI.Algebra.DeRham.Basic.extDeriv R A (snd (_root_.OAI.Algebra.DeRham.Basic.phi R A ω)) = 0 := by
  induction ω using _root_.OAI.Algebra.DeRham.Basic.D_induction with
  | D a => simp
  | zero => simp
  | add x y hx hy => rw [map_add, TrivSqZeroExt.snd_add, map_add, hx, hy, add_zero]
  | smul a x hx =>
      rw [_root_.OAI.Algebra.DeRham.Basic.snd_phi_smul, map_add, Algebra.smul_def, _root_.OAI.Algebra.DeRham.Basic.extDeriv_mul, _root_.OAI.Algebra.DeRham.Basic.extDeriv_mul, hx,
        AlgHom.commutes, _root_.OAI.Algebra.DeRham.Basic.extDeriv_algebraMap, mul_zero, zero_add, involute_ι]
      simp only [_root_.OAI.Algebra.DeRham.Basic.extDeriv_ι, _root_.OAI.Algebra.DeRham.Basic.phi_D, TrivSqZeroExt.snd_inl, zero_mul, add_zero, neg_mul]
      abel

/-- The exterior derivative squares to zero. -/
lemma extDeriv_extDeriv (x : _root_.OAI.Algebra.DeRham.Basic.ExtAlg R A) : _root_.OAI.Algebra.DeRham.Basic.extDeriv R A (_root_.OAI.Algebra.DeRham.Basic.extDeriv R A x) = 0 := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι ω => rw [_root_.OAI.Algebra.DeRham.Basic.extDeriv_ι]; exact extDeriv_snd_phi R A ω
  | mul x y hx hy =>
      rw [_root_.OAI.Algebra.DeRham.Basic.extDeriv_mul, map_add, _root_.OAI.Algebra.DeRham.Basic.extDeriv_mul, _root_.OAI.Algebra.DeRham.Basic.extDeriv_mul, hx, hy, extDeriv_involute,
        CliffordAlgebra.involute_involute]
      simp only [mul_zero, zero_mul, neg_mul, zero_add, add_zero, neg_add_cancel]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

lemma differential_squared (p : ℕ) (x : _root_.OAI.Algebra.DeRham.Basic.Form R A p) :
    _root_.OAI.Algebra.DeRham.Basic.differential R A (p + 1) (_root_.OAI.Algebra.DeRham.Basic.differential R A p x) = 0 :=
  Subtype.ext (extDeriv_extDeriv R A x)

/-! ### Functoriality -/

section Tower

variable (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

lemma extAlgMap_involute (x : _root_.OAI.Algebra.DeRham.Basic.ExtAlg R A) :
    _root_.OAI.Algebra.DeRham.Basic.extAlgMap R A B (involute x) = involute (_root_.OAI.Algebra.DeRham.Basic.extAlgMap R A B x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι ω => simp
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma extAlgMap_snd_phi (ω : Ω[A⁄R]) :
    _root_.OAI.Algebra.DeRham.Basic.extAlgMap R A B (snd (_root_.OAI.Algebra.DeRham.Basic.phi R A ω)) =
      snd (_root_.OAI.Algebra.DeRham.Basic.phi R B (KaehlerDifferential.map R R A B ω)) := by
  induction ω using _root_.OAI.Algebra.DeRham.Basic.D_induction with
  | D a => simp
  | zero => simp
  | add x y hx hy => simp only [map_add, _root_.OAI.Algebra.DeRham.Basic.Sq.snd_add, hx, hy]
  | smul a x hx =>
      rw [_root_.OAI.Algebra.DeRham.Basic.snd_phi_smul, map_add, map_smul, hx, map_mul, _root_.OAI.Algebra.DeRham.Basic.extAlgMap_ι, _root_.OAI.Algebra.DeRham.Basic.extAlgMap_ι,
        KaehlerDifferential.map_D, map_smul,
        ← algebraMap_smul (R := A) B a (KaehlerDifferential.map R R A B x), _root_.OAI.Algebra.DeRham.Basic.snd_phi_smul,
        ← algebraMap_smul (R := A) B a (snd (_root_.OAI.Algebra.DeRham.Basic.phi R B (KaehlerDifferential.map R R A B x)))]

lemma extAlgMap_extDeriv (x : _root_.OAI.Algebra.DeRham.Basic.ExtAlg R A) :
    _root_.OAI.Algebra.DeRham.Basic.extAlgMap R A B (_root_.OAI.Algebra.DeRham.Basic.extDeriv R A x) = _root_.OAI.Algebra.DeRham.Basic.extDeriv R B (_root_.OAI.Algebra.DeRham.Basic.extAlgMap R A B x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a =>
      rw [_root_.OAI.Algebra.DeRham.Basic.extDeriv_algebraMap, _root_.OAI.Algebra.DeRham.Basic.extAlgMap_ι, KaehlerDifferential.map_D, _root_.OAI.Algebra.DeRham.Basic.extAlgMap_algebraMap,
        _root_.OAI.Algebra.DeRham.Basic.extDeriv_algebraMap]
  | ι ω => rw [_root_.OAI.Algebra.DeRham.Basic.extDeriv_ι, extAlgMap_snd_phi, _root_.OAI.Algebra.DeRham.Basic.extAlgMap_ι, _root_.OAI.Algebra.DeRham.Basic.extDeriv_ι]
  | mul x y hx hy =>
      rw [_root_.OAI.Algebra.DeRham.Basic.extDeriv_mul, map_add, map_mul, map_mul, hx, hy, extAlgMap_involute, map_mul,
        _root_.OAI.Algebra.DeRham.Basic.extDeriv_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tower

section AlgHomMap

variable {A}
variable {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

lemma map_differential (f : A →ₐ[R] B) (p : ℕ) (x : _root_.OAI.Algebra.DeRham.Basic.Form R A p) :
    _root_.OAI.Algebra.DeRham.Basic.map R f (p + 1) (_root_.OAI.Algebra.DeRham.Basic.differential R A p x) = _root_.OAI.Algebra.DeRham.Basic.differential R B p (_root_.OAI.Algebra.DeRham.Basic.map R f p x) := by
  let _ := f.toAlgebra
  exact Subtype.ext (extAlgMap_extDeriv R A B x)

end AlgHomMap

end
end

end

end OAI.Algebra.DeRham.BasicSquared
