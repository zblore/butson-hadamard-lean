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

Modified by Zayn Blore, 2026: the definition `IsButsonHadamard` and the statement
`butson_prime_divisibility` are extracted from Formal Conjectures,
`FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at commit `2207c54d`; the import of
`FormalConjecturesUtil` is replaced by two Mathlib imports, the module docstring is new, and the
`category` and `AMS` attributes are removed.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Butson's prime divisibility theorem

A *Butson-type Hadamard matrix* `H(k, n)` is an `n × n` complex matrix `M` whose entries are `k`-th
roots of unity (`k > 0`, `M i j ^ k = 1`) and whose rows are mutually orthogonal, so that
`M * Mᴴ = n • 1`. Butson (*Generalized Hadamard matrices*, Proc. Amer. Math. Soc. 13 (1962),
894–898) proved that if `H(p, n)` exists with `p` prime and `n ≥ 2`, then `p ∣ n`.

The definition `IsButsonHadamard` and the statement `butson_prime_divisibility` are copied verbatim
from Formal Conjectures, `FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at commit
`2207c54d`, under the same namespace and names; only the `category` and `AMS` attributes, which
Formal Conjectures defines, are left out. The theorem ends in `sorry`.
-/

@[expose] public section

namespace ButsonHadamardMatrix

/-- `M` is a **Butson-type Hadamard matrix** $H(k, n)$ if $k > 0$, every entry satisfies
$z^k = 1$, and $M M^* = n I_n$. -/
def IsButsonHadamard {n : ℕ} (k : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  0 < k ∧ (∀ i j, M i j ^ k = 1) ∧ M * M.conjTranspose = (n : ℂ) • 1

/--
**Butson's prime divisibility theorem** [Bu62]: if $p$ is prime, $n \ge 2$, and a Butson-type
Hadamard matrix $H(p, n)$ exists, then $p \mid n$.

The hypothesis $n \ge 2$ excludes the trivial $1 \times 1$ matrix $[1]$, which satisfies
$H(p, 1)$ for every $p \ge 1$.
-/
theorem butson_prime_divisibility {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    (hex : ∃ M, IsButsonHadamard (n := n) p M) :
    p ∣ n := by
  sorry

end ButsonHadamardMatrix
