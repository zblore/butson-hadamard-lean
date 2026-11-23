/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import ButsonHadamard

/-!
# Controls

* The positive controls below are named theorems, and each one's axioms are checked with
  `#guard_msgs`, so none of them can come to rest on `sorry` (or on the canary at the end of this
  file) without failing.
* The hypothesis is satisfiable for every prime: the `n × n` Fourier matrix `(ωⁱʲ)`, with
  `ω = exp (2πi/n)`, is a Butson-type Hadamard matrix `H(n, n)` for every `n ≥ 1`; in particular
  `H(p, p)` exists for every prime `p`, and the theorem gives `p ∣ p`.
* The theorem has content: it rules out `H(2, 3)` (Formal Conjectures proves this one by brute
  force) and `H(3, 4)`.
* The hypothesis `2 ≤ n` is needed: the `1 × 1` matrix `[1]` is an `H(p, 1)` for every `p > 0`.
* The axiom audit would catch a `sorry`: `#print axioms` reports `sorryAx` for an unproved
  statement. This canary comes last, so that no control above can use it.
-/

open Finset

namespace ButsonHadamardMatrix.Control

/-- `ω = exp (2πi/n)`. -/
public noncomputable def omega (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `n × n` **Fourier matrix** `(ωⁱʲ)`, `ω = exp (2πi/n)`. -/
public noncomputable def fourier (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => omega n ^ (i.val * j.val)

/-- For any primitive `n`-th root of unity `ω`, the matrix `(ωⁱʲ)` is an `H(n, n)`. -/
public theorem of_pow_isButsonHadamard {n : ℕ} [NeZero n] {ω : ℂ} (hζ : IsPrimitiveRoot ω n) :
    IsButsonHadamard n (Matrix.of fun i j : Fin n => ω ^ (i.val * j.val)) := by
  have hnorm : ‖ω‖ = 1 := hζ.norm'_eq_one (NeZero.ne n)
  have hstar : star ω = ω⁻¹ := (Complex.inv_eq_conj hnorm).symm
  have hω0 : ω ≠ 0 := hζ.ne_zero (NeZero.ne n)
  refine ⟨Nat.pos_of_ne_zero (NeZero.ne n), fun i j => ?_, ?_⟩
  · rw [Matrix.of_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have hterm : ∀ k : Fin n, (Matrix.of fun i j : Fin n => ω ^ (i.val * j.val)) i k *
        (Matrix.of fun i j : Fin n => ω ^ (i.val * j.val)).conjTranspose k j
        = (ω ^ i.val * ω⁻¹ ^ j.val) ^ k.val := by
      intro k
      rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, star_pow, hstar,
        mul_pow, ← pow_mul, ← pow_mul]
    rw [Finset.sum_congr rfl fun k _ => hterm k,
      Fin.sum_univ_eq_sum_range (fun k => (ω ^ i.val * ω⁻¹ ^ j.val) ^ k) n]
    by_cases hij : i = j
    · subst hij
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hω0)]
      simp
    · rw [ite_eq_right hij, mul_zero]
      have hr1 : ω ^ i.val * ω⁻¹ ^ j.val ≠ 1 := by
        intro h
        rw [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hω0)] at h
        exact hij (Fin.ext (hζ.pow_inj i.isLt j.isLt h))
      have hrn : (ω ^ i.val * ω⁻¹ ^ j.val) ^ n = 1 := by
        simp only [mul_pow, inv_pow, ← pow_mul]
        rw [mul_comm i.val n, mul_comm j.val n, pow_mul, pow_mul, hζ.pow_eq_one]
        simp
      rw [geom_sum_eq hr1, hrn, sub_self, zero_div]

/-- The Fourier matrix is a Butson-type Hadamard matrix `H(n, n)`. -/
public theorem fourier_isButsonHadamard (n : ℕ) [NeZero n] :
    IsButsonHadamard n (fourier n) :=
  of_pow_isButsonHadamard (Complex.isPrimitiveRoot_exp n (NeZero.ne n))

/-- Non-vacuity for every prime: `H(p, p)` exists, and the theorem applies to it. -/
public theorem prime_instance (p : ℕ) (hp : p.Prime) : p ∣ p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  exact butson_prime_divisibility hp hp.two_le ⟨fourier p, fourier_isButsonHadamard p⟩

/-- Content: there is no `H(2, 3)`. -/
public theorem not_exists_two_three : ¬ ∃ M, IsButsonHadamard (n := 3) 2 M := fun h =>
  absurd (butson_prime_divisibility Nat.prime_two (by norm_num) h) (by norm_num)

/-- Content: there is no `H(3, 4)`. -/
public theorem not_exists_three_four : ¬ ∃ M, IsButsonHadamard (n := 4) 3 M := fun h =>
  absurd (butson_prime_divisibility Nat.prime_three (by norm_num) h) (by norm_num)

/-- The hypothesis `2 ≤ n` is needed: `[1]` is an `H(p, 1)` for every `p > 0`. -/
public theorem one_by_one (p : ℕ) (hp : 0 < p) : IsButsonHadamard (n := 1) p 1 := by
  refine ⟨hp, fun i j => ?_, ?_⟩
  · fin_cases i; fin_cases j; simp
  · simp

/-! ### No positive control rests on `sorry` -/

/--
info: 'ButsonHadamardMatrix.Control.fourier_isButsonHadamard' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fourier_isButsonHadamard

/--
info: 'ButsonHadamardMatrix.Control.prime_instance' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prime_instance

/--
info: 'ButsonHadamardMatrix.Control.not_exists_two_three' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_exists_two_three

/--
info: 'ButsonHadamardMatrix.Control.not_exists_three_four' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_exists_three_four

/--
info: 'ButsonHadamardMatrix.Control.one_by_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms one_by_one

/-! ### The canary, last -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
public theorem unproved : ∀ n : ℕ, Nonempty (Fin n) := by
  sorry

/-- info: 'ButsonHadamardMatrix.Control.unproved' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms unproved

end ButsonHadamardMatrix.Control
