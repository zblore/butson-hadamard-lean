/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
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
