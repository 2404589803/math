/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse

namespace OAI.AlgebraicGeometry.ClosedImmersion.AnalyticLeftAt

open _root_.AlgebraicGeometry

/-!
# Analytic local left inverses from section lifting

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse`.
-/

noncomputable section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace Filter

section

universe u

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- Any family of sections on an intrinsic open lifts, after restriction, on a single
affine ambient neighborhood of the selected point. The lifts come from the
surjective closed-immersion map on affine sections. -/
theorem Scheme.Hom.exists_affine_local_section_lifts
    {J : Type*} (V : Y.Opens) (s : J → Γ(Y, V)) (y : Y) (hy : y ∈ V) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hUV : i ⁻¹ᵁ U ≤ V),
      i y ∈ U ∧ ∃ r : J → Γ(X, U),
        ∀ j, i.app U (r j) = Y.presheaf.map (homOfLE hUV).op (s j) := by
  obtain ⟨W, hW, hpre⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  have hyW : i y ∈ W := show y ∈ ⇑i ⁻¹' W from hpre ▸ hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hyW hW
  have hUV : i ⁻¹ᵁ U ≤ V := fun z hz ↦ show z ∈ (V : Set Y) from hpre ▸ hUW hz
  choose r hr using fun j => i.app_surjective U hU
    (Y.presheaf.map (homOfLE hUV).op (s j))
  exact ⟨U, hU, hUV, hyU, r, hr⟩

end

section
namespace ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts_at_center (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y) :
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z) =
        _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) := by
  unfold _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts
  rw [(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z).left_inv (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source Y m z)]

/-- Analyticity is inherited from the morphism of smooth schemes. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y) :
    AnalyticAt ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z)
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z) := by
  apply _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_map Y X i m d z
    ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z).map_source (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source Y m z))
  rw [(_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z).left_inv (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source Y m z)]
  exact _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)

/-- A smooth closed immersion has an analytic local left inverse in complex coordinates,
obtained by lifting the intrinsic coordinate sections. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_analytic_localLeftInverse_of_isClosedImmersion [IsClosedImmersion i.left]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y) :
    ∃ L : (Fin d → ℂ) → (Fin m → ℂ),
      AnalyticAt ℂ L
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z
          (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z)) ∧
      (L ∘ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z) =ᶠ[
        𝓝 (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z)] id := by
  let D := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates Y m z
  have hzD : z.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [D, _root_.OAI.AlgebraicGeometry.ComplexPoint.SmoothCoordinates.LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen, Set.mem_ofPred_eq] using
      _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localEtaleCoordinates Y m z
  obtain ⟨U, _hU, hUV, hzU, r, hr⟩ := (_root_.OAI.AlgebraicGeometry.ClosedImmersion.AnalyticLeftAt.Scheme.Hom.exists_affine_local_section_lifts i.left)
    D.ambientCoordinateOpen D.ambientCoordinateSection z.underlying hzD
  let eY := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z
  let eX := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)
  let L : (Fin d → ℂ) → (Fin m → ℂ) :=
    fun w j => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate U (r j) (eX.symm w)
  have hzY : z ∈ eY.source := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source Y m z
  have hzX : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z ∈ eX.source :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)
  have hzYt : eY z ∈ eY.target := eY.map_source hzY
  have hzXt : eX (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) ∈ eX.target := eX.map_source hzX
  refine ⟨L, ?_, ?_⟩
  · rw [_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts_at_center]
    refine AnalyticAt.pi fun j ↦ ?_
    apply _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_evaluate X d (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z) hzXt U (r j)
    change eX.symm (eX (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i z)) ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U
    rw [eX.left_inv hzX]
    exact hzU
  · have hc : ContinuousAt (fun v => _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i (eY.symm v)) (eY z) :=
      (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.continuous_map i).continuousAt.comp (eY.continuousAt_symm hzYt)
    have hX : ∀ᶠ v in 𝓝 (eY z), _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i (eY.symm v) ∈ eX.source := by
      apply hc (eX.open_source.mem_nhds _)
      change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i (eY.symm (eY z)) ∈ eX.source
      rw [eY.left_inv hzY]
      exact hzX
    have hU : ∀ᶠ v in 𝓝 (eY z), _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i (eY.symm v) ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U := by
      apply hc ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.isOpen_overOpen U).mem_nhds _)
      change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i (eY.symm (eY z)) ∈ _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.overOpen U
      rw [eY.left_inv hzY]
      exact hzU
    filter_upwards [eY.open_target.mem_nhds hzYt, hX, hU] with v hvY hvX hvU
    funext j
    change _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate U (r j)
      (eX.symm (eX (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map i (eY.symm v)))) = v j
    rw [eX.left_inv hvX, _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate_map, hr,
      ← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.evaluate_res hUV (D.ambientCoordinateSection j) (eY.symm v)
        ((_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.mem_overOpen_map_iff i _ U).mp hvU),
      ← _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart_apply_component_eq_evaluate Y m z (eY.symm v) (eY.map_target hvY) j]
    exact congrFun (eY.right_inv hvY) j

/-- The derivative of a smooth closed immersion has a continuous-linear left
inverse, obtained by differentiating the analytic local left inverse. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_leftInverse_fderiv_inclusionInComplexCharts [IsClosedImmersion i.left]
    (z : _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint Y) :
    ∃ P : (Fin d → ℂ) →L[ℂ] (Fin m → ℂ),
      P.comp (fderiv ℂ (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z)
        (_root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z)) = ContinuousLinearMap.id ℂ (Fin m → ℂ) := by
  obtain ⟨L, hL, hleft⟩ :=
    _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_analytic_localLeftInverse_of_isClosedImmersion X Y i m d z
  let φ := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z
  let a := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z
  refine ⟨fderiv ℂ L (φ a), ?_⟩
  have hφ := _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts X Y i m d z
  have hc := hL.differentiableAt.hasFDerivAt.comp a hφ.differentiableAt.hasFDerivAt
  exact (hc.congr_of_eventuallyEq hleft.symm).unique (hasFDerivAt_id a)

end ComplexPoint
end

end

end OAI.AlgebraicGeometry.ClosedImmersion.AnalyticLeftAt
