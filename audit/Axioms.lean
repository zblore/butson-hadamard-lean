/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import ButsonHadamard

/-!
# Axioms of the main result

Fails if the theorem, or its key lemma, comes to depend on anything beyond Lean's three standard
axioms.
-/

/--
info: 'ButsonHadamardMatrix.butson_prime_divisibility' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ButsonHadamardMatrix.butson_prime_divisibility

/--
info: 'ButsonHadamardMatrix.dvd_card_of_sum_pow_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ButsonHadamardMatrix.dvd_card_of_sum_pow_eq_zero
