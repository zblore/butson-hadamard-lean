/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import ButsonHadamard.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Butson's prime divisibility theorem

If a Butson-type Hadamard matrix `H(p, n)` exists with `p` prime and `n ≥ 2`, then `p ∣ n`.

The proof is the standard vanishing-sum argument for this theorem. The first two rows `a`, `b` are orthogonal, so `∑ⱼ aⱼ · conj bⱼ = 0`, and
each term is a `p`-th root of unity, hence a power `ζ ^ kⱼ` of `ζ = exp (2πi/p)` with `kⱼ < p`
(`exists_pow_eq_of_pow_eq_one`). Counting how often each power occurs, `cₖ = #{j | kⱼ = k}`, gives
`∑_{k<p} cₖ ζᵏ = 0`. The polynomial `P = ∑_{k<p} cₖ Xᵏ ∈ ℚ[X]` therefore vanishes at `ζ`, so the
minimal polynomial of `ζ`, the cyclotomic polynomial `Φ_p = 1 + X + ⋯ + X^{p-1}`, divides it.
Since `deg P ≤ p - 1 = deg Φ_p`, `P` is a constant multiple of `Φ_p`, so all the counts are equal,
and `n = ∑ₖ cₖ = p · c₀`.
-/

@[expose] public section

open Polynomial Finset

namespace ButsonHadamardMatrix

/-- The two rows of an orthogonal pair give a vanishing sum. -/
theorem sum_mul_star_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : M * M.conjTranspose = (n : ℂ) • 1) {i i' : Fin n} (hii' : i ≠ i') :
    ∑ j, M i j * star (M i' j) = 0 := by
  have := congr_fun (congr_fun h i) i'
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_ne hii'] using this

/-- A product `a · conj b` of two `p`-th roots of unity is a `p`-th root of unity. -/
theorem mul_star_pow_eq_one {p : ℕ} {a b : ℂ} (ha : a ^ p = 1) (hb : b ^ p = 1) :
    (a * star b) ^ p = 1 := by
  rw [mul_pow, ← star_pow, ha, hb, star_one, mul_one]

/-- **Vanishing sums of `p`-th roots of unity.** If `p` is prime and `∑ⱼ ζ ^ f j = 0` for a
primitive `p`-th root of unity `ζ` and exponents `f j < p`, then each exponent `k < p` occurs the
same number of times, so the number of terms is a multiple of `p`. -/
theorem dvd_card_of_sum_pow_eq_zero {p : ℕ} (hp : p.Prime) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p)
    {ι : Type*} [Fintype ι] (f : ι → ℕ) (hf : ∀ j, f j < p) (hsum : ∑ j, ζ ^ f j = 0) :
    p ∣ Fintype.card ι := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  -- The counts.
  set c : ℕ → ℕ := fun k => (univ.filter fun j => f j = k).card with hc
  have hmaps : ∀ j ∈ (univ : Finset ι), f j ∈ range p := fun j _ => mem_range.mpr (hf j)
  have hcount : Fintype.card ι = ∑ k ∈ range p, c k := by
    rw [← card_univ, card_eq_sum_card_fiberwise hmaps]
  have hfib : ∑ j, ζ ^ f j = ∑ k ∈ range p, (c k : ℂ) * ζ ^ k := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_congr rfl fun j hj => by rw [(mem_filter.mp hj).2], sum_const, nsmul_eq_mul]
  -- The counting polynomial.
  set P : ℚ[X] := ∑ k ∈ range p, C (c k : ℚ) * X ^ k with hP
  have hPζ : aeval ζ P = 0 := by
    rw [hP, map_sum, ← hsum, hfib]
    refine sum_congr rfl fun k _ => ?_
    simp
  have hdvd : cyclotomic p ℚ ∣ P := by
    rw [cyclotomic_eq_minpoly_rat hζ hp.pos]
    exact minpoly.dvd ℚ ζ hPζ
  have hdeg : P.natDegree ≤ (cyclotomic p ℚ).natDegree := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp]
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_sub_one_of_lt (mem_range.mp hk))
  have hPeq : P = C P.leadingCoeff * cyclotomic p ℚ :=
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic p ℚ) hdvd hdeg
  -- Coefficients: `P` has coefficient `c k` at `k < p`, and `Φ_p` has coefficient `1`.
  have hcoeffP : ∀ k < p, P.coeff k = c k := by
    intro k hk
    rw [hP, finsetSum_coeff, sum_eq_single k]
    · simp
    · intro b _ hb
      rw [coeff_C_mul_X_pow, ite_eq_right (Ne.symm hb)]
    · intro h; exact absurd (mem_range.mpr hk) h
  have hcoeffΦ : ∀ k < p, (cyclotomic p ℚ).coeff k = 1 := by
    intro k hk
    rw [cyclotomic_prime, finsetSum_coeff, sum_eq_single k]
    · simp
    · intro b _ hb
      rw [coeff_X_pow, ite_eq_right (Ne.symm hb)]
    · intro h; exact absurd (mem_range.mpr hk) h
  have hconst : ∀ k < p, (c k : ℚ) = P.leadingCoeff := by
    intro k hk
    have := congr_arg (fun q : ℚ[X] => q.coeff k) hPeq
    simp only [coeff_C_mul, hcoeffΦ k hk, mul_one] at this
    rw [← hcoeffP k hk, this]
  have hall : ∀ k ∈ range p, c k = c 0 := by
    intro k hk
    have h1 := hconst k (mem_range.mp hk)
    have h0 := hconst 0 hp.pos
    exact_mod_cast h1.trans h0.symm
  rw [hcount, sum_congr rfl hall, sum_const, card_range, smul_eq_mul]
  exact dvd_mul_right p _

/-- **Butson's prime divisibility theorem** (Butson 1962): if `p` is prime, `n ≥ 2`, and a
Butson-type Hadamard matrix `H(p, n)` exists, then `p ∣ n`. -/
theorem butson_prime_divisibility {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    (hex : ∃ M, IsButsonHadamard (n := n) p M) :
    p ∣ n := by
  obtain ⟨M, -, hpow, horth⟩ := hex
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / p)) p :=
    Complex.isPrimitiveRoot_exp p hp.ne_zero
  set ζ := Complex.exp (2 * Real.pi * Complex.I / p)
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have hroot : ∀ j, ∃ k < p, ζ ^ k = M i₀ j * star (M i₁ j) := fun j =>
    hζ.eq_pow_of_pow_eq_one (mul_star_pow_eq_one (hpow i₀ j) (hpow i₁ j))
  choose f hf hfz using hroot
  have hsum : ∑ j, ζ ^ f j = 0 := by
    simp only [hfz]
    exact sum_mul_star_eq_zero horth hne
  simpa using dvd_card_of_sum_pow_eq_zero hp hζ f hf hsum

end ButsonHadamardMatrix
