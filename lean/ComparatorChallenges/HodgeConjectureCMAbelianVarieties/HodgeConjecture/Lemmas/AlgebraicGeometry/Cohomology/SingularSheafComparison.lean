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

import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SingularComparison

namespace OAI.AlgebraicGeometry.Cohomology.SingularSheafComparison

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# Singular and constant-sheaf comparison

On the analytic space of a smooth complex scheme, the rational constant sheaf is resolved by
the sheafified rational singular-cochain complex. Localizing at quasi-isomorphisms gives a
canonical comparison equivalence in every cohomological degree.
-/

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace

section
namespace ComplexPoint

open _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (X : Over (Spec ↧ℂ))

/-- The rational constant-sheaf comparison with the integer-indexed singular-cochain
resolution. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X ⟶
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℚ :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℚ

/-- The rational constant-to-singular comparison is a quasi-isomorphism on a smooth
complex-point space. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X) := by
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt_quasiIso X ℚ

/-- Hypercohomology of the integer-indexed rational singular-cochain sheaf complex. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.RationalSingularCochainHypercohomology (n : ℤ) : Type 1 :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℚ) n

/-- Hypercohomology of the rational constant sheaf complex is canonically additively equivalent
to the hypercohomology of its singular-cochain resolution. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalHypercohomologySingularCochainAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X) n ≃+
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.RationalSingularCochainHypercohomology X n where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt_quasiIso X)
  map_add' α β :=
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X) n).map_add α β

@[simp]
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalHypercohomologySingularCochainAddEquiv_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X) n) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalHypercohomologySingularCochainAddEquiv X n α =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X) n α :=
  rfl

/-- Rational constant-sheaf cohomology is canonically additively equivalent to the
hypercohomology of its singular-cochain resolution. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalCohomologySingularCochainAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    H^n(X; ℚ) ≃+ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.RationalSingularCochainHypercohomology X n :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm.trans
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalHypercohomologySingularCochainAddEquiv X n)

@[simp]
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalCohomologySingularCochainAddEquiv_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (α : H^n(X; ℚ)) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalCohomologySingularCochainAddEquiv X n α =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X) n
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm α) :=
  rfl

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cohomology.SingularSheafComparison
