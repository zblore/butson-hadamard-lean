# Butson's prime divisibility theorem, in Lean

A Butson-type Hadamard matrix H(k, n) is an n × n complex matrix whose entries are k-th roots of unity and whose rows are mutually orthogonal: M Mᴴ = n · 1. H(2, n) are the real Hadamard matrices; complex Hadamard matrices of this kind are also the building blocks of mutually unbiased bases in quantum information.

**Butson's theorem** (A. T. Butson, "Generalized Hadamard matrices", *Proc. Amer. Math. Soc.* 13 (1962), 894–898): if H(p, n) exists with p prime and n ≥ 2, then p divides n.

This repository proves it in Lean 4. The statement and the definition are [Formal Conjectures'](https://github.com/google-deepmind/formal-conjectures/blob/2207c54d0dbe960de591d280f997b195bf3f6e28/FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean) (`ButsonHadamardMatrix.butson_prime_divisibility`, marked research solved there), copied verbatim.

## The proof

It is Butson's argument.

1. Two different rows a, b of M are orthogonal: ∑ⱼ aⱼ · conj(bⱼ) = 0. Each term is a p-th root of unity, so it is ζ^kⱼ for ζ = exp(2πi/p) and some kⱼ < p.
2. Let cₖ count the j with kⱼ = k. Then ∑_{k<p} cₖ ζᵏ = 0, so the rational polynomial P = ∑_{k<p} cₖ Xᵏ vanishes at ζ.
3. The minimal polynomial of ζ over ℚ is the cyclotomic polynomial Φ_p = 1 + X + ⋯ + X^{p−1} (Mathlib's `cyclotomic_eq_minpoly_rat`), so Φ_p divides P. Both have degree at most p − 1, so P is a constant multiple of Φ_p: every count cₖ is the same.
4. So n = ∑ₖ cₖ = p · c₀.

In Lean the counting step is `ButsonHadamardMatrix.dvd_card_of_sum_pow_eq_zero` (a vanishing sum of p-th roots of unity has a multiple of p terms), and the theorem is `ButsonHadamardMatrix.butson_prime_divisibility`, both in `ButsonHadamard/Main.lean`.

## Related work

- I haven't found another Lean proof. I searched GitHub code search (Lean files, default branches) for "butson" and "ButsonHadamard", and the Palomar registry for "Butson" and "Hadamard", on 23 November 2026; the only hit is Formal Conjectures' statement. Absence from those searches isn't proof that none exists.
- The same Formal Conjectures file states, also as research solved, that H(p, mp) need not exist for odd primes p (no H(3, 15); de Launey 1984, Winterhof 2000). That isn't proved here.

## Files

- `Challenge.lean` states the theorem with Formal Conjectures' definition, ending in `sorry`. It imports only Mathlib.
- `ButsonHadamard/Defs.lean` holds the same definition for the proof; `ButsonHadamard/Main.lean` the proof; `Solution.lean` re-exports it.

## Checks

- `scripts/check-fc-match.py` downloads Formal Conjectures' file at commit `2207c54d`, requires its SHA-256 to match the recorded one, and requires `Challenge.lean`'s code to be exactly Formal Conjectures' definition and statement (without the `category` and `AMS` attributes), and `ButsonHadamard/Defs.lean` to contain the definition verbatim. With `--self-test` it also confirms that 6 altered inputs are rejected.
- `audit/Axioms.lean` uses `#guard_msgs` to require that the theorem and its key lemma use only `propext`, `Classical.choice` and `Quot.sound`.
- `audit/Control.lean` states its controls as named theorems and checks each one's axioms, so none can come to rest on `sorry`. It shows that the Fourier matrix (ωⁱʲ) is an H(n, n) for every n, so the hypothesis is satisfiable for every prime; that the theorem rules out H(2, 3) and H(3, 4); and that [1] is an H(p, 1), so the hypothesis n ≥ 2 is needed. Last, a canary confirms that the axiom audit detects `sorry`.
- `scripts/verify-comparator.sh` runs `lake comparator` in CI after a push, sandboxed on Linux. It checks the Challenge against the proof and replays the proof through Lean's kernel, nanoda and con-ron. I have run it locally on Windows, unsandboxed (`--inadvisably-no-sandbox`, with full paths to the nanoda and con-ron binaries in a copy of `comparator.json`), on 23 November 2026: it ended "Your solution is okay!", with con-ron (28,700 declarations), nanoda and Lean's kernel all accepting the proof. An unsandboxed run is not the trusted check; the sandboxed Linux run in CI is.

## Building

Lean `v4.35.0-rc3` and Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.

```
lake exe cache get
lake build
lake env lean audit/Axioms.lean
lake env lean audit/Control.lean
python3 scripts/check-fc-match.py --self-test
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
```

## How it was made

I drafted the Lean with Claude Code.

## Licence

Apache 2.0.
