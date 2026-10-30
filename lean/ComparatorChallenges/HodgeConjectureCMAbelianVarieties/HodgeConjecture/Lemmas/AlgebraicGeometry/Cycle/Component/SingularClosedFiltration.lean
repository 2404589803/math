/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

namespace OAI.AlgebraicGeometry.Cycle.ComponentSingularGe

open _root_.AlgebraicGeometry

/-!
# Ambient closed supports for singular-component localization induction

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration`.
-/

/-! ### Constructions used only in proofs -/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

section

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This is the length of the finite list defining the filtration; all terms from this
index onward are empty. -/
abbrev cycleComponentSingularFiltrationLength : ℕ :=
  (_root_.OAI.AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This smooth scheme is the stratum `S_k \ S_{k+1}` with its induced reduced structure. -/
abbrev cycleComponentSingularFiltrationStratum (k : ℕ) : Scheme :=
  _root_.OAI.AlgebraicGeometry.Stratification.BasicLe.reducedClosedSmoothPiece (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k)

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This morphism is the inclusion of the smooth stratum `S_k \ S_{k+1}` into `X`. -/
def cycleComponentSingularFiltrationStratumι (k : ℕ) :
    cycleComponentSingularFiltrationStratum X x k ⟶ X.left :=
  _root_.OAI.AlgebraicGeometry.Stratification.BasicLe.reducedClosedSmoothPieceι (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k) ≫ _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x

/-- A singular-filtration stratum with its induced structure map to `Spec ℂ`. -/
abbrev cycleComponentSingularFiltrationStratumOver (k : ℕ) : Over (Spec ↧ℂ) :=
  Over.mk (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)

/-- The stratum immersion bundled over `Spec ℂ`. -/
def cycleComponentSingularFiltrationStratumOverι (k : ℕ) :
    cycleComponentSingularFiltrationStratumOver X x k ⟶ X :=
  Over.homMk (cycleComponentSingularFiltrationStratumι X x k) rfl

instance cycleComponentSingularFiltrationStratumOverι_isImmersion (k : ℕ) :
    IsImmersion (cycleComponentSingularFiltrationStratumOverι X x k).left := by
  change IsImmersion (_root_.OAI.AlgebraicGeometry.Stratification.BasicLe.reducedClosedSmoothPieceι (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k) ≫ _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance cycleComponentSingularFiltrationStratumι_isImmersion (k : ℕ) :
    IsImmersion (cycleComponentSingularFiltrationStratumι X x k) := by
  dsimp [cycleComponentSingularFiltrationStratumι]
  infer_instance

instance cycleComponentSingularFiltrationStratum_smooth (k : ℕ) :
    Smooth (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom) := by
  change Smooth ((_root_.OAI.AlgebraicGeometry.Stratification.BasicLe.reducedClosedSmoothPieceι (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k) ≫ _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

instance cycleComponentSingularFiltrationStratumOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (cycleComponentSingularFiltrationStratumOver X x k).hom := by
  change LocallyOfFiniteType (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The successive ambient difference is precisely the image of the smooth stratum. -/
theorem cycleComponentSingularAmbientClosedFiltration_layer (k : ℕ) :
    Set.range (cycleComponentSingularFiltrationStratumι X x k) =
      (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k : Set X.left) \
        (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x (k + 1) : Set X.left) := by
  rw [cycleComponentSingularFiltrationStratumι, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, _root_.OAI.AlgebraicGeometry.Stratification.ClosedFiltration.reducedSmoothClosedFiltration_layer]
  exact Set.image_sdiff (_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x).isClosedEmbedding.injective _ _

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This open subscheme is `X \ S_{k+1}`, in which the `k`-th stratum is closed. -/
def cycleComponentSingularStratumAmbientOpen (k : ℕ) : X.left.Opens :=
  (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x (k + 1)).compl

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This is the inclusion of the smooth stratum `S_k \ S_{k+1}` into the open subscheme
`X \ S_{k+1}`. -/
def cycleComponentSingularStratumClosedLift (k : ℕ) :
    cycleComponentSingularFiltrationStratum X x k ⟶
      cycleComponentSingularStratumAmbientOpen X x k :=
  IsOpenImmersion.lift (cycleComponentSingularStratumAmbientOpen X x k).ι
    (cycleComponentSingularFiltrationStratumι X x k) (by
      rw [Scheme.Opens.range_ι]
      intro y hy
      exact ((cycleComponentSingularAmbientClosedFiltration_layer X x k).le hy).2)

/-- The localization open with its induced structure map to `Spec ℂ`. -/
abbrev cycleComponentSingularStratumAmbientOpenOver (k : ℕ) : Over (Spec ↧ℂ) :=
  _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openScheme X (cycleComponentSingularStratumAmbientOpen X x k)

instance cycleComponentSingularStratumAmbientOpenOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (cycleComponentSingularStratumAmbientOpenOver X x k).hom := by
  change LocallyOfFiniteType
    ((cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom)
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] in
@[reassoc (attr := simp)]
theorem cycleComponentSingularStratumClosedLift_ι (k : ℕ) :
    cycleComponentSingularStratumClosedLift X x k ≫
      (cycleComponentSingularStratumAmbientOpen X x k).ι =
        cycleComponentSingularFiltrationStratumι X x k :=
  IsOpenImmersion.lift_fac _ _ _

/-- The closed stratum lift bundled over `Spec ℂ`. -/
def cycleComponentSingularStratumClosedLiftOver (k : ℕ) :
    cycleComponentSingularFiltrationStratumOver X x k ⟶
      cycleComponentSingularStratumAmbientOpenOver X x k :=
  Over.homMk (cycleComponentSingularStratumClosedLift X x k) (by
    change cycleComponentSingularStratumClosedLift X x k ≫
      ((cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) =
        cycleComponentSingularFiltrationStratumι X x k ≫ X.hom
    rw [← Category.assoc, cycleComponentSingularStratumClosedLift_ι])

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Its closed image is exactly the restriction of the current support to that open. -/
theorem range_cycleComponentSingularStratumClosedLift (k : ℕ) :
    Set.range (cycleComponentSingularStratumClosedLift X x k) =
      (cycleComponentSingularStratumAmbientOpen X x k).ι ⁻¹'
        (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k : Set X.left) := by
  have hf (w : cycleComponentSingularFiltrationStratum X x k) :
      (cycleComponentSingularStratumAmbientOpen X x k).ι
        (cycleComponentSingularStratumClosedLift X x k w) =
          cycleComponentSingularFiltrationStratumι X x k w :=
    congrArg (fun f => f w) (cycleComponentSingularStratumClosedLift_ι X x k)
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ((cycleComponentSingularAmbientClosedFiltration_layer X x k).le ⟨w, (hf w).symm⟩).1
  · intro hy
    obtain ⟨w, hw⟩ := (cycleComponentSingularAmbientClosedFiltration_layer X x k).ge ⟨hy, y.2⟩
    exact ⟨w, (cycleComponentSingularStratumAmbientOpen X x k).ι.isOpenEmbedding.injective
      ((hf w).trans hw)⟩

/-- Each layer is a closed immersion in precisely the open needed by localization. -/
instance cycleComponentSingularStratumClosedLift_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (cycleComponentSingularStratumClosedLift X x k) := by
  have : IsPreimmersion (cycleComponentSingularStratumClosedLift X x k ≫
      (cycleComponentSingularStratumAmbientOpen X x k).ι) := by
    rw [cycleComponentSingularStratumClosedLift_ι]
    infer_instance
  let : IsPreimmersion (cycleComponentSingularStratumClosedLift X x k) :=
    .of_comp (cycleComponentSingularStratumClosedLift X x k)
      (cycleComponentSingularStratumAmbientOpen X x k).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_cycleComponentSingularStratumClosedLift]
  exact (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k).isClosed.preimage
    (cycleComponentSingularStratumAmbientOpen X x k).ι.continuous

instance cycleComponentSingularStratumClosedLiftOver_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (cycleComponentSingularStratumClosedLiftOver X x k).left := by
  change IsClosedImmersion (cycleComponentSingularStratumClosedLift X x k)
  infer_instance

/-- The localization open remains smooth of the original ambient dimension. -/
instance cycleComponentSingularStratumAmbientOpen_smoothOfRelativeDimension
    (k d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    SmoothOfRelativeDimension d ((cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (cycleComponentSingularStratumAmbientOpen X x k).ι X.hom

instance cycleComponentSingularStratumClosedLift_smooth (k : ℕ) :
    Smooth (cycleComponentSingularStratumClosedLift X x k ≫
      (cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) := by
  rw [← Category.assoc, cycleComponentSingularStratumClosedLift_ι]
  infer_instance

namespace ComplexPoint

/-- The smooth-locus immersion into the ambient variety, bundled over `Spec ℂ`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOverι : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x ⟶ X :=
  Over.homMk ((_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x) rfl

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOverι_isImmersion :
    IsImmersion (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOverι X x).left := by
  change IsImmersion ((_root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x)
  infer_instance

end ComplexPoint
end

end

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

section

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [_root_.OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

theorem cycleComponentSingularClosedFiltration_length :
    _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x
      (_root_.OAI.AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length = ⊥ := by
  let := _root_.OAI.AlgebraicGeometry.Cycle.SupportEq.cycleComponent_isNoetherian X x
  exact _root_.OAI.AlgebraicGeometry.Stratification.ClosedFiltration.reducedSmoothClosedFiltration_length _ _

omit [IsIntegral X.left] [Smooth X.hom] in
theorem cycleComponentSingularAmbientClosedFiltration_antitone :
    Antitone (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x) :=
  fun _ _ hkl ↦ Set.image_mono (_root_.OAI.AlgebraicGeometry.Stratification.ClosedFiltration.reducedSmoothClosedFiltration_antitone _ _ hkl)

theorem cycleComponentSingularAmbientClosedFiltration_length :
    _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x
      (_root_.OAI.AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length = ⊥ := by
  apply SetLike.coe_injective
  change _root_.OAI.AlgebraicGeometry.Cycle.Support.cycleComponentι X.left x ''
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x
      (_root_.OAI.AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length : Set _) = ∅
  rw [cycleComponentSingularClosedFiltration_length]
  exact Set.image_empty _

/-- Every closed remainder stays below the singular-boundary dimension bound. -/
theorem cycleComponentSingularClosedFiltration_dimension_lt
    {p : ℕ} (hx : Order.coheight x = p) (k : ℕ) :
    topologicalKrullDim (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k) < (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p : ℕ) :=
  (IsEmbedding.inclusion (_root_.OAI.AlgebraicGeometry.Stratification.ClosedFiltration.reducedSmoothClosedFiltration_le _ _ k)).isInducing.topologicalKrullDim_le.trans_lt
    (_root_.OAI.AlgebraicGeometry.Smooth.SingularLocusDimension.topologicalKrullDim_cycleComponent_singularLocus_lt X x hx)

/-- Every smooth layer has strictly smaller dimension than the component. -/
theorem cycleComponentSingularFiltrationStratum_dimension_lt
    {p : ℕ} (hx : Order.coheight x = p) (k : ℕ) :
    topologicalKrullDim (cycleComponentSingularFiltrationStratum X x k) < (_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p : ℕ) :=
  (_root_.OAI.AlgebraicGeometry.Smooth.SingularLocusDimension.topologicalKrullDim_reducedClosedSmoothPiece_le _ le_rfl).trans_lt
    (cycleComponentSingularClosedFiltration_dimension_lt X x hx k)

/-- The normal codimension lower bound is realized on standard-smooth affine
neighborhoods of every stratum point, including strata of nonconstant dimension. -/
theorem cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge
    {p : ℕ} (hx : Order.coheight x = p) (k : ℕ)
    (z : cycleComponentSingularFiltrationStratum X x k) :
    ∃ (U : (cycleComponentSingularFiltrationStratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p ∧ p + 1 ≤ _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - n ∧
        RingHom.IsStandardSmoothOfRelativeDimension n
          ((cycleComponentSingularFiltrationStratumι X x k ≫ X.hom).appLE ⊤ U (by simp)).hom := by
  obtain ⟨U, hU, hzU, n, hn, hstd⟩ :=
    _root_.OAI.AlgebraicGeometry.Smooth.SingularLocusDimension.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)
      (cycleComponentSingularFiltrationStratum_dimension_lt X x hx k) z
  exact ⟨U, hU, hzU, n, hn, by omega, hstd⟩

/-- The dimension bound supplies smooth scheme morphisms of fixed local
dimension, ready for the normal-coordinate construction. -/
theorem cycleComponentSingularFiltrationStratum_exists_smooth_relativeDimension
    {p : ℕ} (hx : Order.coheight x = p) (k : ℕ)
    (z : cycleComponentSingularFiltrationStratum X x k) :
    ∃ (U : (cycleComponentSingularFiltrationStratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p ∧ p + 1 ≤ _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - n ∧
        SmoothOfRelativeDimension n (U.ι ≫ cycleComponentSingularFiltrationStratumι X x k ≫ X.hom) := by
  obtain ⟨U, hU, hzU, n, hn, hcodim, hstd⟩ :=
    cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge X x
      hx k z
  exact ⟨U, hU, hzU, n, hn, hcodim,
    _root_.OAI.AlgebraicGeometry.Smooth.AffineRelativeDimension.smoothOfRelativeDimension_affineOpen_of_isStandardSmooth _ hU hstd⟩

namespace ComplexPoint

omit [IsIntegral X.left] [Smooth X.hom] in
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_antitone :
    Antitone (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x) :=
  fun _ _ hkl _ hz ↦ _root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_antitone X x hkl hz

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_length :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x
      (_root_.OAI.AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length = ⊥ := by
  apply SetLike.coe_injective
  change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.underlying ⁻¹'
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x
      (_root_.OAI.AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length : Set X.left) = ∅
  rw [_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_length]
  exact Set.preimage_empty

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Each analytic successive difference is the complex-point image of its smooth stratum. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_layer (k : ℕ) :
    Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOverι X x k)) =
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) \
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1) : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion X]
  change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.underlying ⁻¹' Set.range (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k) = _
  rw [_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_layer]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Inside the localization open, the stratum's closed-embedding image is the current analytic
closed support restricted to that open. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularStratumClosedLift_complexPoints_range (k : ℕ) :
    Set.range (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLiftOver X x k)) =
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k)) ⁻¹'
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)) := by
  rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion]
  change (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.underlying : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver X x k) →
    (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver X x k).left) ⁻¹'
      Set.range (_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k) = _
  rw [_root_.OAI.AlgebraicGeometry.Cycle.ComponentSingularGe.range_cycleComponentSingularStratumClosedLift]
  rfl

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.Cycle.ComponentSingularGe
