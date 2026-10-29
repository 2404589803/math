/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.FlasqueLowestCohomology

namespace OAI.AlgebraicTopology.Sheaf.FlasqueLowestIsoHom

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# The lowest-degree cohomology comparison for flasque complexes

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.FlasqueLowestCohomology`.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

universe u

section
namespace TopCat
open _root_.TopCat

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

@[simp] theorem lowestSectionCohomologyIso_hom (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque)
    (U : Opens X) :
    (_root_.OAI.AlgebraicTopology.Sheaf.FlasqueLowestCohomology.TopCat.lowestSectionCohomologyIso X K N n hK hflasque U).hom =
      _root_.OAI.AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection X K n U := rfl

end TopCat
end

end

end OAI.AlgebraicTopology.Sheaf.FlasqueLowestIsoHom
