/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.NormalCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FlattenedSupport
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone

namespace OAI.AlgebraicGeometry.Cycle.LocalLocalHomology

open _root_.AlgebraicGeometry

/-!
# Local relative homology for smooth closed supports

Every prescribed open neighborhood of a point on a smooth closed complex subvariety contains
a smaller open neighborhood whose support-complement pair has rational
relative homology and cohomology only in degree twice the complex codimension. The comparison
and the exactly normalized normal class come from flattening, radial compression, and tangent
contraction.

This is a cofinal local singular calculation. The identification with derived sheaf sections
with support, and gluing its normalizations across overlapping charts, are separate theorems.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace
open _root_.OAI.AlgebraicTopology.Singular

section
namespace ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y)
  (V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (hzV : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z ∈ V)

/-- Let `i : Y → X` be a closed immersion of smooth schemes over `ℂ` of dimensions `m` and `d`,
respectively. For `z ∈ Y(ℂ)` and an ambient open `V ⊆ X(ℂ)`, this is the chart at `i(z)` with
source restricted to `V`. Its coordinates lie in `ℂ^m × ℂ^{d-m}`, and the image of `Y(ℂ)` is
given by vanishing of the second coordinate. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart :
    OpenPartialHomeomorph (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z).restrOpen V V.isOpen

include hzV in
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_source :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z ∈
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V).source :=
  ⟨_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_source X Y i m d z, hzV⟩

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_center :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_center X Y i m d z

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_range_iff (y : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V).source) :
    y ∈ Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i) ↔
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V y).2 = 0 :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_range_iff X Y i m d z y hy.1

/-- A small open support-model neighborhood inside the prescribed open. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
  _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood (Fin m → ℂ) (d - m)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_smoothClosedSupportNeighborhood :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood X Y i m d z V hzV :=
  _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.mem_flattenedSupportNeighborhood _ _ _ _ _

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood_le :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood X Y i m d z V hzV ≤ V :=
  fun _ hy ↦ (_root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood_subset_source (Fin m → ℂ) (d - m)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)
    hy).2

/-- The local support-complement pair, with the image as support. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair : TopPair :=
  _root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood X Y i m d z V hzV)
    (Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i))

/-- The pair homeomorphism to the product normal model. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPairIso :
    _root_.OAI.AlgebraicTopology.LocalHomology.NormalSlicePurity.Singular.normalSlicePair (Fin m → ℂ) (d - m) ≅
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV :=
  _root_.OAI.AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportPairIso (Fin m → ℂ) (d - m)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)
    (Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i))
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
    (congrArg Prod.snd (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_center X Y i m d z V))

/-- All-degree local relative homology, computed from the pair maps. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso (n : ℕ) :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n ≅
        _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ (d - m)) n :=
  ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeHomologyFunctor ℚ n).mapIso
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPairIso X Y i m d z V hzV).symm) ≪≫
    _root_.OAI.AlgebraicTopology.LocalHomology.NormalSlicePurity.Singular.normalSliceRelativeHomologyIso (Fin m → ℂ) (d - m) n

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing.AlgebraicTopology.Singular.standardComplexLocalHomology_isZero_of_ne (d - m) n hn).of_iso
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV n)

/-- The exact complex-normal class in the local support pair. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) (2 * (d - m)) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
    (2 * (d - m))).inv.hom (_root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ (d - m))

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass_normalization :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
      (2 * (d - m))).hom.hom
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass X Y i m d z V hzV) =
        _root_.OAI.AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ (d - m) :=
  ConcreteCategory.congr_hom
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
      (2 * (d - m))).inv_hom_id _

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass_ne_zero :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass X Y i m d z V hzV ≠ 0 := by
  intro hzero
  have h := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass_normalization X Y i m d z V hzV
  rw [hzero, map_zero] at h
  exact _root_.OAI.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator.Singular.standardComplexLocalClass_ne_zero_for_chart (d - m) h.symm

/-- The coclass normalized to pair to one with the exact complex normal class. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalCoclass :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV)
        (2 * (d - m)) :=
  _root_.OAI.AlgebraicGeometry.Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedRelativeCoclass (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass X Y i m d z V hzV)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass_ne_zero X Y i m d z V hzV)

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalCoclass_apply_class :
    _root_.OAI.AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology ℚ
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) (2 * (d - m))
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalCoclass X Y i m d z V hzV)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass X Y i m d z V hzV) = 1 :=
  _root_.OAI.AlgebraicGeometry.Cycle.LocalPurityOf.AlgebraicTopology.Singular.normalizedRelativeCoclass_pairing_self _ _

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeCohomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n) :=
  _root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeCohomology_isZero ℚ _ n
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomology_isZero_of_ne X Y i m d z V hzV n hn)

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.LocalLocalHomology
