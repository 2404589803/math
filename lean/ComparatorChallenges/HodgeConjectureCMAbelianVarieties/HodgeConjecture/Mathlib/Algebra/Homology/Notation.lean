/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.

This file has been modified.
-/

import Mathlib.Algebra.Homology.ComplexShape

namespace OAI.Algebra.Homology.Notation

/-!
# Notation for the cohomological complex shape

`ℤᵘᵖ` denotes the cohomological complex shape on the integers, whose differentials increase
degree by one.
-/

section

/-- `ℤᵘᵖ` is `ComplexShape.up ℤ`, the cohomological complex shape on integer degrees: its
potentially nonzero differentials have type `K.X n ⟶ K.X (n + 1)`. -/
notation "ℤᵘᵖ" => ComplexShape.up Int

end

end OAI.Algebra.Homology.Notation
