/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Butson-type Hadamard matrices

The definition `IsButsonHadamard`, copied verbatim from Formal Conjectures,
`FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at commit `2207c54d`.
-/

@[expose] public section

namespace ButsonHadamardMatrix

/-- `M` is a **Butson-type Hadamard matrix** $H(k, n)$ if $k > 0$, every entry satisfies
$z^k = 1$, and $M M^* = n I_n$. -/
def IsButsonHadamard {n : ℕ} (k : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  0 < k ∧ (∀ i j, M i j ^ k = 1) ∧ M * M.conjTranspose = (n : ℂ) • 1

end ButsonHadamardMatrix
