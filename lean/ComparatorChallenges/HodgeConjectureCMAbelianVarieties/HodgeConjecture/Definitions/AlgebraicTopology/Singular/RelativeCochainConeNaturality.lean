/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality
import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality

namespace OAI.AlgebraicTopology.Singular.RelativeCochainConeNaturality

/-! # Canonical natural relative-cochain cone comparison

The explicit short-exact-sequence lift is natural already before passage to homology.

The lift is positive `(inclusion, 0)`; Mathlib's cone connecting morphism is the negative first
projection. Their composite is displayed below.

Agreement with `relativeCochainConeCohomologyEquiv`, which is built from a completed triangle map,
is a separate comparison theorem.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

section
section

variable (R : Type u) [CommRing R]

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This
identifies `H^n(C^*(X, A; R))` with `H^{n-1}(Cone(C^*(X; R) → C^*(A; R)))`. The complexes are
extended by zero to integer degrees before taking the cone. The comparison uses the map with
components `(inclusion, 0)`, fixing its sign. -/
def relativeDualCochainHomologyIsoCone (X : TopPair.{u}) (n : ℕ) :
    (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) ≅
      (CochainComplex.mappingCone (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) :=
  _root_.OAI.Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone
    (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt R X)
    (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainG.relativeDualCochainShortComplexInt_shortExact R X) ((n : ℤ) - 1) n (by omega)

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`.
Extending the relative cochain complex by zero to negative integer degrees leaves its degree-`n`
cohomology unchanged. This is the resulting linear equivalence with relative singular cohomology
`H^n(X, A; R)`. -/
def relativeDualCochainCohomologyEquiv (X : TopPair.{u}) (n : ℕ) :
    (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) ≃ₗ[R]
      _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology R X n :=
  ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCochainComplex R X).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).toLinearEquiv

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This
linear equivalence identifies `H^{n-1}(Cone(C^*(X; R) → C^*(A; R)))` with relative singular
cohomology `H^n(X, A; R)`. It is inverse to the cohomology map induced by the relative-cochain
inclusion with zero second cone component. -/
def relativeCochainConeCohomologyEquivCanonical (X : TopPair.{u}) (n : ℕ) :
    (CochainComplex.mappingCone (_root_.OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) ≃ₗ[R] _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology R X n :=
  (relativeDualCochainHomologyIsoCone R X n).symm.toLinearEquiv.trans
    (relativeDualCochainCohomologyEquiv R X n)

end
end

end

end OAI.AlgebraicTopology.Singular.RelativeCochainConeNaturality
