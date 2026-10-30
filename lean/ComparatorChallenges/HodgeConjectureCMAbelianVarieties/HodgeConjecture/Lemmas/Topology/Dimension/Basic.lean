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

import HodgeConjecture.Definitions.Topology.Dimension.Basic

import HodgeConjecture.Mathlib.Topology.KrullDimension

namespace OAI.Topology.Dimension.BasicEq

open _root_.TopologicalSpace

/-!
# The dimension of an irreducible topological space

Lemmas about the definitions in
`HodgeConjecture.Definitions.Topology.Dimension.Basic`.
-/

noncomputable section

namespace TopologicalSpace
open _root_.TopologicalSpace

attribute [local instance] specializationOrder in
/-- On a sober space, and in particular on a scheme, the dimension counts chains of points under
specialisation. -/
lemma dim_eq_krullDim (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] [T0Space X]
    [QuasiSober X] : _root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim X = ((Order.krullDim X).unbotD 0).toNat := by
  rw [_root_.OAI.Topology.Dimension.Basic.TopologicalSpace.dim, _root_.OAI.Topology.Foundations.KrullDimension.topologicalKrullDim_eq_krullDim]

end TopologicalSpace

end

end OAI.Topology.Dimension.BasicEq
