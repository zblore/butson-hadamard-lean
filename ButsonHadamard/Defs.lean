/-
Copyright 2026 The Formal Conjectures Authors.
Copyright (c) 2026 Zayn Blore.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Modified by Zayn Blore, 2026: the definition `IsButsonHadamard` is extracted from Formal
Conjectures, `FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at commit `2207c54d`; the
import of `FormalConjecturesUtil` is replaced by two Mathlib imports, and the module docstring is
new.
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
