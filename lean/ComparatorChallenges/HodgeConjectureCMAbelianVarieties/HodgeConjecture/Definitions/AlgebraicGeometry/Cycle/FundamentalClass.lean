/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtension
import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison

namespace OAI.AlgebraicGeometry.Cycle.FundamentalClass

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicTopology.Support.RelativeCohomologySheaf.Singular
open scoped OAI.AlgebraicGeometry.Cohomology.WithSupport.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# Sheaf cycle classes in arbitrary codimension

The exactly normalized normal-chart coclass on a component's smooth locus is transported to the
supported cohomology sheaf. Lowest-degree purity and unique extension across the singular
boundary then give a supported class on the original ambient variety, and forgetting its support
lands in ordinary rational cohomology.

The corresponding Borel–Moore fundamental class is obtained through the complex-orientation
duality for the ambient chain sheaf. Compactification independence and rational-equivalence
invariance are separate statements.
-/

noncomputable section

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite
open _root_.OAI.AlgebraicTopology.Singular

section
namespace ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X) := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.analyticTopology

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `S ⊆ X(ℂ)` closed. For a natural
number `n`, this identifies the degree-`n` cohomology sheaf of `Γ_S(I^•)` with the
sheafification of `V ↦ H^n(V, V \ S; ℚ)`. Here `ℚ → I^•` is an injective resolution and `Γ_S`
takes sections vanishing off `S`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveCohomologySheafIsoRelative
    (S : Closeds (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ) :
    -- The `n`-th cohomology sheaf of `RΓ_S(ℚ)`.
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S).homology (n : ℤ) ≅
      𝓗_[S]^n(TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℚ) :=
  letI : ∀ V : Opens (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace V := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  (asIso (HomologicalComplex.homologyMap
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).symm ≪≫
      _root_.OAI.AlgebraicTopology.Support.SingularCohomologySheafComparison.Singular.supportedSingularCohomologySheafIsoRelative
        (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) S S.isClosed n

section

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. For a natural number `p`, this is `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`,
computed from global sections of the subsheaves supported in `Z(ℂ)` of a chosen injective
resolution of the constant rational sheaf. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology (p : ℕ) : AddCommGrpCat :=
  -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, with `Z` the subvariety with generic point `x`.
  (((_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
    -- `X(ℂ)`.
    (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
    -- Global sections, i.e. sections over all of `X(ℂ)`.
    ⊤).mapHomologicalComplex ℤᵘᵖ).obj
    -- `RΓ_{Z(ℂ)}(ℚ)`.
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
      -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))).homology
    -- Degree `2p`.
    (2 * (p : ℤ))

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and `𝓗^{2p}_S` for the
sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. For a natural number `p`, this is the abelian group
`Γ(U, 𝓗^{2p}_S)` of sections of the local relative-cohomology sheaf away from the singular locus
of `Z`. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSmoothCoclassSections (p : ℕ) : AddCommGrpCat :=
  -- Sections of `𝓗^{2p}_{Z(ℂ)}` over `X(ℂ) \ Z_sing(ℂ)`, with support `Z(ℂ)` and degree `2p`.
  (𝓗_[_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x]^(2 * p)(TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X); ℚ)).presheaf.obj
      -- The open `X(ℂ) \ Z_sing(ℂ)`.
      (op (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x))

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This is the isomorphism
`H^{2p}_S(X(ℂ); ℚ) ≅ Γ(U, 𝓗^{2p}_S)`. It restricts a supported class to `U` and takes its local
relative classes. Purity on the smooth locus and vanishing of cohomology supported on the
singular locus make the map invertible. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedClassNormalizationIso :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p ≅ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSmoothCoclassSections X x p :=
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportExtensionIso X x hx ≪≫
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx ≪≫
      (he ▸ (_root_.OAI.AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)).mapIso
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveCohomologySheafIsoRelative X
            (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) (2 * p)))

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This additive map `Γ(U,
𝓗^{2p}_S) → H^{2p}_S(X(ℂ); ℚ)` assigns to a section its unique supported class on all of `X(ℂ)`.
It inverts restriction followed by passage to local relative-cohomology classes. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentExtendSmoothCoclass :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSmoothCoclassSections X x p →+ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p :=
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedClassNormalizationIso X x hx).inv.hom

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. This is the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` computed from
sections supported on `Z(ℂ)` of an injective resolution of the constant rational sheaf. Its
local classes along the smooth locus of `Z` evaluate to `1` on the complex orientation classes
of the normal spaces. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedInjectiveClass : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentExtendSmoothCoclass X x hx
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportCoclassSection X x hx)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. This is the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` whose local classes
along the smooth locus of `Z` evaluate to `1` on the complex orientation classes of the normal
spaces. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafSupportedClass :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`.
    H_[_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x]^(2 * p)(X; ℚ) :=
  have he : 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by omega
  (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)
    (2 * p)).symm (he ▸ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedInjectiveClass X x hx)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. The fundamental cohomology class `[Z] ∈ H^{2p}(X(ℂ);ℚ)` is
obtained by forgetting the support of the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` whose local classes
along the smooth locus evaluate to `1` on the complex orientation classes of the normal spaces. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClass : H^(2 * p)(X; ℚ) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) (2 * p)
    (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafSupportedClass X x hx)

end

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `p` a natural number. This is the
rational subspace of `H^{2p}(X(ℂ); ℚ)` spanned by the fundamental cohomology classes of all
codimension-`p` integral closed subvarieties of `X`. Their classes are normalized by the complex
orientations of their normal spaces on their smooth loci. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan (p : ℕ) : Submodule ℚ (H^(2 * p)(X; ℚ)) :=
  sSup {Submodule.span ℚ {_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClass X x hx} |
    (x : X.left) (hx : Order.coheight x = p) }

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.FundamentalClass
