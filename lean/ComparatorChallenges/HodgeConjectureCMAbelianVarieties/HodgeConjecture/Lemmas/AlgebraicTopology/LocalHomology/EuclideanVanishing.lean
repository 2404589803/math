/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.HomologyZeroNaturality
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Analysis.Normed.Module.Connected

namespace OAI.AlgebraicTopology.LocalHomology.EuclideanVanishing

/-!
# Dimensional vanishing for Euclidean local homology

These vanishing statements use the affine boundary chain-homotopy equivalence
and the dimension bound on normalized simplicial chains. They are prerequisites for proving
that the concrete relative-chain sheaf has cohomology only in the orientation degree.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open scoped Simplicial

section
namespace Singular

/-- In positive degrees strictly below its sphere dimension, the normalized boundary
complex is exact: its three relevant groups agree with those of the full simplex. -/
theorem standardSphereSucc_normalizedChains_exactAt_of_lt
    (n k : ℕ) (hk : k ≠ 0) (hlt : k < n + 1) :
    (_root_.OAI.AlgebraicTopology.LocalHomology.SphereSimplicial.Singular.standardSphereSuccNormalizedRationalChains n).ExactAt k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  let f := SSet.normalizedChainComplexMap
    (SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι
      (ModuleCat.of ℚ ℚ)
  let : IsIso (f.f (m + 2)) :=
    (_root_.OAI.AlgebraicTopology.LocalHomology.SphereSimplicial.Singular.standardSphereSuccNormalizedChainsXIsoStandard n (m + 2) (by omega)).isIso_hom
  let : IsIso (f.f (m + 1)) :=
    (_root_.OAI.AlgebraicTopology.LocalHomology.SphereSimplicial.Singular.standardSphereSuccNormalizedChainsXIsoStandard n (m + 1) (by omega)).isIso_hom
  let : IsIso (f.f m) :=
    (_root_.OAI.AlgebraicTopology.LocalHomology.SphereSimplicial.Singular.standardSphereSuccNormalizedChainsXIsoStandard n m (by omega)).isIso_hom
  let φ := (shortComplexFunctor' (ModuleCat ℚ) (ComplexShape.down ℕ)
    (m + 2) (m + 1) m).map f
  let : IsIso φ.τ₁ := by dsimp [φ, shortComplexFunctor']; infer_instance
  let : IsIso φ.τ₂ := by dsimp [φ, shortComplexFunctor']; infer_instance
  let : IsIso φ.τ₃ := by dsimp [φ, shortComplexFunctor']; infer_instance
  let : IsIso φ := ShortComplex.isIso_of_isIso φ
  have hfull := ShortComplex.exact_of_iso
    ((_root_.OAI.AlgebraicTopology.LocalHomology.SphereSimplicial.Singular.standardSimplexSuccNormalizedRationalChains n).isoSc'
      (m + 2) (m + 1) m (by simp) (by simp))
    (_root_.OAI.AlgebraicTopology.LocalHomology.SphereSimplicial.Singular.standardSimplexSucc_normalizedChains_exactAt n (m + 1) (by omega))
  exact ShortComplex.exact_of_iso
    ((_root_.OAI.AlgebraicTopology.LocalHomology.SphereSimplicial.Singular.standardSphereSuccNormalizedRationalChains n).isoSc'
      (m + 2) (m + 1) m (by simp) (by simp)).symm
    (ShortComplex.exact_of_iso (asIso φ).symm hfull)

/-- Punctured real space has no positive homology strictly below the sphere degree. -/
theorem standardPuncturedHomology_isZero_of_lt (d k : ℕ)
    (hk : k ≠ 0) (hlt : k + 1 < d) :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.Homology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).snd k) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  have hnorm := standardSphereSucc_normalizedChains_exactAt_of_lt n k hk (by omega)
  have hchains := (exactAt_iff_of_quasiIsoAt
    ((∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of ℚ ℚ)) k).mpr hnorm
  exact hchains.isZero_homology.of_iso
    ((_root_.OAI.AlgebraicTopology.LocalHomology.PuncturedEuclidean.Singular.standardAffineBoundaryChainHomotopyEquiv (n + 2)).toHomologyIso k).symm

/-- The punctured real `d`-space has no homology in degrees at least `d`, including
the empty punctured zero-dimensional space. -/
theorem standardPuncturedHomology_isZero_of_dimension_le (d k : ℕ) (hk : d ≤ k) :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.Homology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).snd k) := by
  exact ((∂Δ[d] : SSet.{0}).isZero_homology_of_hasDimensionLT
    (ModuleCat.of ℚ ℚ) k d hk).of_iso
      ((_root_.OAI.AlgebraicTopology.LocalHomology.PuncturedEuclidean.Singular.standardAffineBoundaryChainHomotopyEquiv d).toHomologyIso k).symm

/-- Local homology of real `d`-space vanishes above degree `d`, degree one in dimension zero
included. -/
theorem standardLocalHomology_isZero_of_dimension_lt (d k : ℕ) (hk : d < k) :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d) k) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact (_root_.OAI.AlgebraicTopology.LocalHomology.Euclidean.Singular.relativeSingular_homology_exact_relative (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d)
    n).isZero_of_both_isZero (_root_.OAI.AlgebraicTopology.LocalHomology.Euclidean.Singular.standardRealModel_homology_isZero d (n + 1) (by omega))
    (standardPuncturedHomology_isZero_of_dimension_le d n (by omega))

/-- Positive-dimensional punctured Euclidean space is nonempty. -/
theorem puncturedPair_nonempty (d : ℕ) (hd : 0 < d) :
    Nonempty (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).snd := by
  refine ⟨⟨fun _ ↦ 1, ?_⟩⟩
  intro h
  have := congrFun h ⟨0, hd⟩
  norm_num at this

/-- In real dimension greater than one, punctured Euclidean space is path-connected. -/
theorem puncturedPair_pathConnectedSpace (d : ℕ) (hd : 1 < d) :
    PathConnectedSpace (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).snd := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_compl_singleton_of_one_lt_rank
  simpa only [rank_fun', Fintype.card_fin] using
    (show (1 : Cardinal) < (d : Cardinal) from by exact_mod_cast hd)

/-- In a pair with nonempty subspace and path-connected ambient space, degree-zero
relative homology vanishes. -/
theorem relativeHomology_zero_isZero_of_pathConnected (P : TopPair)
    [Nonempty P.snd] [PathConnectedSpace P.fst] :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ P 0) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  refine (_root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeChainShortComplex_shortExact ℚ P).exactAt_X₃ 0 ?_ ?_
  · exact _root_.OAI.AlgebraicTopology.Singular.HomologyZeroNaturality.TopCat.singularHomologyMap_zero_epi (X := P.snd) (Y := P.fst)
      P.map (ModuleCat.of ℚ ℚ)
  · intro j hj
    simp [ComplexShape.down_Rel] at hj

/-- Local degree-zero homology vanishes in positive real dimension. -/
theorem standardLocalHomology_zero_isZero (d : ℕ) (hd : 0 < d) :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d) 0) := by
  let : Nonempty (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).snd := puncturedPair_nonempty d hd
  let : PathConnectedSpace (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).fst :=
    inferInstanceAs (PathConnectedSpace (Fin d → ℝ))
  exact relativeHomology_zero_isZero_of_pathConnected (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d)

/-- Local degree-one homology vanishes in real dimension greater than one. -/
theorem standardLocalHomology_one_isZero (d : ℕ) (hd : 1 < d) :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d) 1) := by
  let : PathConnectedSpace (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).snd :=
    puncturedPair_pathConnectedSpace d hd
  let : PathConnectedSpace (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).fst :=
    inferInstanceAs (PathConnectedSpace (Fin d → ℝ))
  apply HomologicalComplex.ExactAt.isZero_homology
  refine (_root_.OAI.AlgebraicTopology.Singular.CohomologyTo.relativeChainShortComplex_shortExact ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d)).exactAt_X₃ 1 ?_ ?_
  · exact (_root_.OAI.AlgebraicTopology.LocalHomology.Euclidean.Singular.standardRealModel_homology_isZero d 1 (by omega)).epi _
  · intro j hj
    have hj0 : j = 0 := by simpa [ComplexShape.down_Rel] using hj
    subst j
    let : IsIso (HomologicalComplex.homologyMap
        ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d)).hom 0) :=
      _root_.OAI.AlgebraicTopology.Singular.HomologyZeroNaturality.TopCat.singularHomologyMap_zero_isIso
        (X := (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).snd) (Y := (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).fst)
        (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d).map (ModuleCat.of ℚ ℚ)
    change Mono (HomologicalComplex.homologyMap
      ((_root_.OAI.AlgebraicTopology.Singular.Cohomology.chainPairFunctor ℚ).obj (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d)).hom 0)
    infer_instance

/-- Local homology of real coordinate space vanishes in every degree other than
the real dimension, with the degree-zero and degree-one endpoints included. -/
theorem standardLocalHomology_isZero_of_ne (d k : ℕ) (hk : k ≠ d) :
    IsZero (_root_.OAI.AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d) k) := by
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · rcases k with _ | _ | n
    · exact standardLocalHomology_zero_isZero d hlt
    · exact standardLocalHomology_one_isZero d hlt
    · exact
        (_root_.OAI.AlgebraicTopology.LocalHomology.Euclidean.Singular.relativeSingular_homology_exact_relative (_root_.OAI.AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℝ d)
          (n + 1)).isZero_of_both_isZero (_root_.OAI.AlgebraicTopology.LocalHomology.Euclidean.Singular.standardRealModel_homology_isZero d (n + 2) (by omega))
          (standardPuncturedHomology_isZero_of_lt d (n + 1) (by omega) (by omega))
  · exact standardLocalHomology_isZero_of_dimension_lt d k hgt

end Singular
end

end

end OAI.AlgebraicTopology.LocalHomology.EuclideanVanishing
