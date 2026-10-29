/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothClosedLift
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.OpenTransport
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf
import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula

namespace OAI.AlgebraicGeometry.Cycle.ComponentSmoothSupportPurity

open _root_.AlgebraicGeometry

/-!
# Purity along the smooth locus of an integral cycle component

The coefficient complex is the ambient injective resolution, with support in the full cycle
component, restricted to the complement of the canonical singular boundary. Normal
neighborhoods of the smooth-locus closed lift show its cohomology sheaves are concentrated
in degree `2p`.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace Opposite

section
namespace ComplexPoint

open _root_.OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the analytic open subset `X(ℂ) \ Z_sing(ℂ)`, on which the
remaining support is the complex manifold `Z_reg(ℂ)`. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
  -- `X(ℂ) \ Z_sing(ℂ)`.
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x 0).compl

include hx in
/-- Every `y ∈ Z(ℂ) \ Z_sing(ℂ)` has arbitrarily small open neighborhoods `W` in `X(ℂ)` with
`H^n(W, W \ Z(ℂ); ℚ) = 0` for `n ≠ 2p`. -/
theorem cycleComponentSmoothSupport_exists_relativeCohomology_vanishing
    (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hy : y ∈ _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x)
    (hyU : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), W ≤ V ∧ y ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * p →
        -- `H^n(W, W \ Z(ℂ); ℚ)` vanishes away from degree `2p`.
        IsZero (ModuleCat.of ℚ (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
          (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
            -- `Z(ℂ)`.
            (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x)) n)) := by
  let O := _root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x
  let OX := _root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x
  let Y := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x
  let i : Y ⟶ OX := _root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x
  let : SmoothOfRelativeDimension (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) Y.hom :=
    _root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothCoe.cycleComponentSmoothLocus_smoothOfRelativeDimension X x hx
  have : SmoothOfRelativeDimension (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) OX.hom := by
    change SmoothOfRelativeDimension (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) O.ι X.hom
  let f := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X O)
  have hS : f ⁻¹' _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x = Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i) :=
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusClosedLift_complexPoints_range X x).symm
  obtain ⟨w, rfl⟩ := (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusAmbientOpen_analytic_image X x).ge hyU
  obtain ⟨z, rfl⟩ := hS.le hy
  have hpd : p ≤ _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left := by
    have h := _root_.OAI.AlgebraicGeometry.Smooth.DimensionFormula.SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) x
    rw [hx] at h
    exact_mod_cast h
  obtain ⟨W, hWV, hzW, hW⟩ := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_smoothClosedSupportImageNeighborhood
    OX Y i (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) f (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpenEmbedding_map_open X O)
    (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x) hS z V hyV
  refine ⟨W, hWV, hzW, ?_⟩
  intro n hn
  exact hW n (by omega)

include hx in
/-- For each `n ≠ 2p`, every `y ∈ X(ℂ) \ Z_sing(ℂ)` has arbitrarily small open neighborhoods `W`
(depending on `n`) with `H^n_{Z(ℂ)}(W; ℚ) = 0`, where `H^n_{Z(ℂ)}(W; ℚ) = H^n(Γ(W, RΓ_{Z(ℂ)}(ℚ)))`
is computed in the fixed injective resolution. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ))
    (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) (hyU : y ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), W ≤ V ∧ y ∈ W ∧
      -- `H^n_{Z(ℂ)}(W; ℚ)` vanishes away from degree `2p`.
      IsZero ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
        -- `X(ℂ)`.
        (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
        -- Sections over the open `W`.
        W).mapHomologicalComplex ℤᵘᵖ).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
          -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) V).map_isZero
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x
    · obtain ⟨W, hWV, hyW, hW⟩ :=
        cycleComponentSmoothSupport_exists_relativeCohomology_vanishing X x hx
          y hy hyU V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
          (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
            (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) W q
      let : Subsingleton ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
          (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) W).mapHomologicalComplex ℤᵘᵖ).obj
            (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))).homology
              (q : ℤ)) := e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact _root_.OAI.AlgebraicTopology.Support.SectionRestrictionIs.TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x).compl W
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. Take the subsheaves of sections supported in `Z(ℂ)` of a chosen
injective resolution of `ℚ` on `X(ℂ)`, then restrict the resulting complex to `X(ℂ) \
Z_sing(ℂ)`. This is the resulting integer-indexed sheaf complex. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothRestrictedInjectiveComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat
      (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x))) ℤ :=
  -- `RΓ_{Z(ℂ)}(ℚ)`, restricted to the open `X(ℂ) \ Z_sing(ℂ)`.
  let U : Opens (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x
  -- Restriction of sheaves to the open `U = X(ℂ) \ Z_sing(ℂ)`.
  ((U.isOpenEmbedding.sheafPullback
    AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z(ℂ)}(ℚ)` on `X(ℂ)`.
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothRestrictedInjectiveComplex_isStrictlyGE :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothRestrictedInjectiveComplex X x).IsStrictlyGE 0 := by
  dsimp [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothRestrictedInjectiveComplex]
  infer_instance

include hx in
/-- Purity: on `X(ℂ) \ Z_sing(ℂ)`, the cohomology sheaves `𝓗^n(RΓ_{Z(ℂ)}(ℚ))` vanish for
`n ≠ 2p`. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ)) :
    -- The cohomology sheaf `𝓗^n(RΓ_{Z(ℂ)}(ℚ))` on `X(ℂ) \ Z_sing(ℂ)` is zero for `n ≠ 2p`.
    IsZero ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothRestrictedInjectiveComplex X x).homology n) :=
  _root_.OAI.AlgebraicTopology.Sheaf.OpenRestrictedVanishing.TopCat.openRestriction_homology_isZero_of_cofinal_sections
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) _ _ n
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing X x hx n hn)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Put `U = X(ℂ) \ Z_sing(ℂ)` and let `K` be the
subsheaf complex of a rational injective resolution consisting of sections supported in `Z(ℂ)`.
Purity implies `𝓗^j(K)|_U = 0` for `j < 2p`, giving this isomorphism `H^{2p}(Γ(U, K)) ≅ Γ(U,
𝓗^{2p}(K))`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportLowestSectionCohomologyIso :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ); ℚ)`.
    ((((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
      -- Sections over the open `X(ℂ) \ Z_sing(ℂ)`.
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex ℤᵘᵖ).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))).homology
          -- Degree `2p`.
          (2 * (p : ℤ))) ≅
      -- Sections of the cohomology sheaf `𝓗^{2p}(RΓ_{Z(ℂ)}(ℚ))` over `X(ℂ) \ Z_sing(ℂ)`.
      ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)).homology
        -- Degree `2p`.
        (2 * (p : ℤ))).presheaf.obj
          -- The open `X(ℂ) \ Z_sing(ℂ)`.
          (op (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)) :=
  _root_.OAI.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology.TopCat.openRestrictedLowestSectionCohomologyIso
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))
    0 (2 * (p : ℤ))
    (fun j hj => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
      X x hx j (ne_of_lt hj))
    (fun j => _root_.OAI.AlgebraicTopology.Support.FlasqueSections.TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x).compl
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).X j))

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.ComponentSmoothSupportPurity
