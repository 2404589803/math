/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.EuclideanVanishing
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.ChainStalk

namespace OAI.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing

/-!
# Local homology concentration on a smooth complex scheme

The compressed-chart map is an isomorphism in every local-homology degree, by
neighborhood excision. Euclidean local homology vanishing therefore proves concentration
in real dimension `2*d`, and stalk exactness gives the corresponding homology-sheaf
vanishing.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace

namespace AlgebraicTopology
open _root_.AlgebraicTopology
namespace Singular
open _root_.AlgebraicTopology
open _root_.OAI.AlgebraicTopology.Singular

/-- Complex coordinate space has local homology only in twice its complex dimension. -/
theorem standardComplexLocalHomology_isZero_of_ne (d n : ℕ) (hn : n ≠ 2 * d) :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ d) n) :=
  (_root_.OAI.AlgebraicTopology.LocalHomology.EuclideanVanishing.Singular.standardLocalHomology_isZero_of_ne (d * 2) n (by omega)).of_iso
    ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeHomologyFunctor ℚ n).mapIso (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexRealPairIso d))

end Singular
end AlgebraicTopology

end

end OAI.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing
