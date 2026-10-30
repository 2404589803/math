/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
import HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologyOpenTransport

namespace OAI.AlgebraicGeometry.Cycle.SmoothSupportCoclassSection

open scoped OAI.AlgebraicTopology.Support.RelativeCohomologySheaf.Singular

open _root_.AlgebraicGeometry

/-!
# The normalized component coclass on the original ambient smooth-support open

The component's smooth locus is closed in the complement of its singular boundary. Its exactly
normalized smooth-support section there is transported through the analytic open embedding,
giving a section of the original ambient relative-cohomology sheaf on the singular-boundary
complement.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.Topology Opposite
open _root_.OAI.AlgebraicTopology.Singular

section
namespace ComplexPoint

section Component

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include hx in
/-- The dimension of the smooth locus, bundled over `Spec ℂ`. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x).hom :=
  _root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothCoe.cycleComponentSmoothLocus_smoothOfRelativeDimension X x hx

include X hx in
omit [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
/-- The codimension arithmetic, from the coheight bound. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension :
    _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) = p := by
  have h := _root_.OAI.AlgebraicGeometry.Smooth.DimensionFormula.SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) x
  rw [hx] at h
  have hpd : p ≤ _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left := by exact_mod_cast h
  omega

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. On the analytic space of the open scheme `X \
Z_sing`, this is the global section of the sheafification of `V ↦ H^{2p}(V, V \ Z_reg(ℂ); ℚ)`
obtained by gluing local normal orientation coclasses. The local class is normalized to pair to
`1` with the orientation class of the complex normal space. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftCoclassSection :
    -- The support is the image of `Z_reg`; if `Z ⊆ X` is the variety, the ambient space is the
    -- `X \ Z_sing` open, as a complex manifold.
    (𝓗_[Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x))]^(2 * p)
      (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x)); ℚ)).presheaf.obj
      (op ⊤) :=
  letI := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have hdeg := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension X x hx
  hdeg ▸ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x)
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x) (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the continuous map `(X \ Z_sing)(ℂ) → X(ℂ)` induced by
inclusion of the open subscheme. It identifies its source with the analytic open subset `X(ℂ) \
Z_sing(ℂ)`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap :
    TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x)) ⟶
    TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) :=
  TopCat.ofHom (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.continuousMap
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x)))

omit [IsIntegral X.left] [Smooth X.hom] in
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding :
    IsOpenEmbedding (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap X x) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.isOpenEmbedding_map_open X (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x)

/-- Support membership is transported by the lift-image theorem. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_support :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap X x ⁻¹' _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x =
      Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x)) :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusClosedLift_complexPoints_range X x).symm

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The image open is exactly the complement of the canonical first singular boundary. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_imageOpen :
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤ =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x := by
  apply Opens.ext
  change (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap X x) '' Set.univ = _
  rw [Set.image_univ]
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusAmbientOpen_analytic_image X x

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This section of `𝓗^{2p}_S` on
`U` is obtained by gluing the local coclasses defined by complex normal coordinates along
`Z_reg(ℂ)`. The local class is normalized to pair to `1` with the orientation class of the
complex normal space. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportCoclassSection :
    -- The support is `Z(ℂ)`, the complex points of the subvariety, inside `X(ℂ)`.
    (𝓗_[_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x]^(2 * p)(TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℚ)).presheaf.obj
      -- The open set of complex points of the complement of the singular boundary, i.e. `X(ℂ) \ Z_sing(ℂ)`.
      (op (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)) :=
  _root_.OAI.AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologySectionOnOpen (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap X x)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x)
    (Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x)))
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftCoclassSection X x hx)

end Component

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.SmoothSupportCoclassSection
