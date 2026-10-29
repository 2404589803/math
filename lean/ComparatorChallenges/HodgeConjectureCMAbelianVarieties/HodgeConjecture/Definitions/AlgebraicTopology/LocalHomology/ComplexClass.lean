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

import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClass
import HodgeConjecture.Lemmas.LinearAlgebra.ComplexOrientation
import HodgeConjecture.Mathlib.Topology.Category.TopPair
import Mathlib.Analysis.Complex.Basic

namespace OAI.AlgebraicTopology.LocalHomology.ComplexClass

/-!
# The standard complex local class

This file identifies `ℂ^p` with an ordered real coordinate space by listing the real and imaginary
part of each complex coordinate consecutively. It transports the explicit standard local cycle to
`H_{2p}(ℂ^p, ℂ^p ∖ {0}; R)`. Thus the complex orientation is constructed from complex coordinates
rather than supplied as data.
-/

open _root_.CategoryTheory

noncomputable section

section
namespace Singular

variable (R : Type) [CommRing R]

/-- For a natural number `p`, this homeomorphism `ℂ^p ≃ ℝ^{2p}` sends each complex coordinate to its
real and imaginary parts, ordered consecutively as `(Re z₀, Im z₀, Re z₁, Im z₁, …)`. This
ordering fixes the convention for complex orientation. -/
def complexRealHomeomorph (p : ℕ) : (Fin p → ℂ) ≃ₜ (Fin (p * 2) → ℝ) :=
  (_root_.OAI.LinearAlgebra.Foundations.ComplexOrientation.Complex.piCoordCLE p).toHomeomorph

/-- For a natural number `p`, splitting each complex coordinate into consecutive real and imaginary
parts gives this isomorphism of pairs `(ℂ^p, ℂ^p \ {0}) ≅ (ℝ^{2p}, ℝ^{2p} \ {0})`. -/
def standardComplexRealPairIso (p : ℕ) :
    _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ p ≅ _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ (p * 2) :=
  _root_.OAI.Topology.Category.TopPairOf.TopPair.isoOfSubset (complexRealHomeomorph p) fun _ =>
    not_congr (_root_.OAI.LinearAlgebra.Foundations.ComplexOrientation.Complex.piCoordCLE p).map_eq_zero_iff

/-- Let `R` be a commutative ring and `p` a natural number. This isomorphism `H_{2p}(ℂ^p, ℂ^p \ {0};
R) ≅ H_{2p}(ℝ^{2p}, ℝ^{2p} \ {0}; R)` is induced by the coordinate map ordering the real and
imaginary parts consecutively. -/
def standardComplexRealRelativeHomologyIso (p : ℕ) :
    -- `H_{2p}(ℂ^p, ℂ^p \ {0}; R) ≅ H_{2p}(ℝ^{2p}, ℝ^{2p} \ {0}; R)`.
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology R (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ p) (p * 2) ≅
      _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology R (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ (p * 2)) (p * 2) :=
  (_root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeHomologyFunctor R (p * 2)).mapIso (standardComplexRealPairIso p)

/-- Let `R` be a commutative ring and `p` a natural number. This class in `H_{2p}(ℂ^p, ℂ^p \ {0};
R)` is transported from the affine simplex in `ℝ^{2p}` with ordered vertices the standard basis
followed by `(-1, …, -1)`, with coefficient `1`. Transport uses consecutive real and imaginary
coordinates and fixes the normalization of the local complex class. -/
def standardComplexLocalClass (p : ℕ) :
    -- The complex-orientation generator of `H_{2p}(ℂ^p, ℂ^p \ {0}; R)`.
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology R (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ p) (2 * p) :=
  (Nat.mul_comm p 2) ▸
    (standardComplexRealRelativeHomologyIso R p).inv.hom (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.standardLocalClass R (p * 2))

end Singular
end

end

end OAI.AlgebraicTopology.LocalHomology.ComplexClass
