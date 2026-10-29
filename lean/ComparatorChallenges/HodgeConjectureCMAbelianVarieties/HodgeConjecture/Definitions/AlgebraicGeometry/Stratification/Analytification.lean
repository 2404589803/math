/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.SingularLocusDimension
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI.AlgebraicGeometry.Stratification.Analytification

open _root_.AlgebraicGeometry

/-!
# Complex points of the smooth decomposition

The finite algebraic decomposition induces a partition of complex-point sets into the images of
smooth complex schemes. The images are analytically locally closed, and the lifting assertion
follows from the equivalence between complex points and closed scheme points.

Analytic triangulation, homology-dimension theorems, and frontier conditions are outside the
scope of this file.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

section
namespace ComplexPoint

variable (X : Over (Spec ↧ℂ)) {Y : Over (Spec ↧ℂ)}

variable [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.reducedClosedSmoothPiece_locallyOfFiniteType (T : Closeds X.left) :
    LocallyOfFiniteType (Over.mk (_root_.OAI.AlgebraicGeometry.Stratification.BasicLe.reducedClosedSmoothPieceι X.hom T ≫ X.hom)).hom := by
  change LocallyOfFiniteType (_root_.OAI.AlgebraicGeometry.Stratification.BasicLe.reducedClosedSmoothPieceι X.hom T ≫ X.hom)
  infer_instance

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Stratification.Analytification
