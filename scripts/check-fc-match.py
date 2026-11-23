#!/usr/bin/env python3
"""Check that Challenge.lean and ButsonHadamard/Defs.lean are exactly what they claim to be.

Palomar's Comparator checks that Solution proves the statement of Challenge.lean, with the same
definitions. This script checks the other link: that Challenge.lean is Formal Conjectures' text.

It reads `FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at FC_COMMIT (downloaded from
GitHub, or from a local file given with --fc-file), requires its SHA-256 to be FC_SHA256, and
extracts two blocks verbatim:

* the definition `IsButsonHadamard`, from its docstring to the end of its body;
* the theorem `butson_prime_divisibility`, from its docstring to `sorry`, with FC's attribute line
  `@[category research solved, AMS 5 15]` removed (Formal Conjectures defines those attributes).

It then builds the complete expected text of both files, the fixed preambles below (licence and
modification notice, `module`, the two Mathlib imports, the module docstring) followed by the code
built from those blocks, and requires each file to equal it exactly, character for character
(line endings aside). Comparing whole files means nothing can be added anywhere: no extra import,
no command hidden in or after a comment, no extra declaration.

`--self-test` also runs the check on mutated copies (a changed exponent, a dropped hypothesis, a
changed constant, an extra declaration, a command smuggled out of the module docstring, an extra
import, and a Defs file whose real definition is commented out and replaced), each of which must
be rejected.
"""
import hashlib
import pathlib
import re
import sys
import urllib.request

FC_COMMIT = "2207c54d0dbe960de591d280f997b195bf3f6e28"
FC_PATH = "FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean"
FC_SHA256 = "e0ff83d900cd3e7183e3286ea0eeae1ec67c2a3a18b6c5a38b7404b86c4465fa"
ATTRIBUTE = "@[category research solved, AMS 5 15]\n"
ROOT = pathlib.Path(__file__).resolve().parent.parent

LICENCE = """Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
"""

IMPORTS = """module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

"""

CHALLENGE_PREAMBLE = ("""/-
Copyright 2026 The Formal Conjectures Authors.
Copyright (c) 2026 Zayn Blore.

""" + LICENCE + """
Modified by Zayn Blore, 2026: the definition `IsButsonHadamard` and the statement
`butson_prime_divisibility` are extracted from Formal Conjectures,
`FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at commit `2207c54d`; the import of
`FormalConjecturesUtil` is replaced by two Mathlib imports, the module docstring is new, and the
`category` and `AMS` attributes are removed.
-/
""" + IMPORTS + """/-!
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

""")

DEFS_PREAMBLE = ("""/-
Copyright 2026 The Formal Conjectures Authors.
Copyright (c) 2026 Zayn Blore.

""" + LICENCE + """
Modified by Zayn Blore, 2026: the definition `IsButsonHadamard` is extracted from Formal
Conjectures, `FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at commit `2207c54d`; the
import of `FormalConjecturesUtil` is replaced by two Mathlib imports, and the module docstring is
new.
-/
""" + IMPORTS + """/-!
# Butson-type Hadamard matrices

The definition `IsButsonHadamard`, copied verbatim from Formal Conjectures,
`FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at commit `2207c54d`.
-/

""")


def fc_source(local=None):
    if local:
        data = pathlib.Path(local).read_bytes()
    else:
        url = f"https://raw.githubusercontent.com/google-deepmind/formal-conjectures/{FC_COMMIT}/{FC_PATH}"
        with urllib.request.urlopen(url, timeout=60) as response:
            data = response.read()
    digest = hashlib.sha256(data).hexdigest()
    if digest != FC_SHA256:
        raise SystemExit(f"FC source hash {digest} != recorded {FC_SHA256}; read the new text first")
    return data.decode("utf-8").replace("\r\n", "\n")


def blocks(fc):
    d = re.search(r"/-- `M` is a \*\*Butson-type Hadamard matrix\*\*.*?\n  0 < k ∧ .*?\n", fc, re.S)
    t = re.search(r"/--\n\*\*Butson's prime divisibility theorem\*\*.*?\n  sorry\n", fc, re.S)
    if not d or not t:
        raise SystemExit("could not find the definition or the theorem in the FC source")
    theorem = t.group(0)
    if theorem.count(ATTRIBUTE) != 1:
        raise SystemExit("FC attribute line not found exactly once")
    return d.group(0), theorem.replace(ATTRIBUTE, "")


def expected_files(definition, theorem):
    opening = "@[expose] public section\n\nnamespace ButsonHadamardMatrix\n\n"
    closing = "end ButsonHadamardMatrix\n"
    challenge = CHALLENGE_PREAMBLE + opening + definition + "\n" + theorem + "\n" + closing
    defs = DEFS_PREAMBLE + opening + definition + "\n" + closing
    return challenge, defs


def check(challenge_text, defs_text, expected):
    errors = []
    if challenge_text.replace("\r\n", "\n") != expected[0]:
        errors.append("Challenge.lean differs from the expected text (FC's definition and statement)")
    if defs_text.replace("\r\n", "\n") != expected[1]:
        errors.append("ButsonHadamard/Defs.lean differs from the expected text (FC's definition)")
    return errors


def main():
    args = sys.argv[1:]
    local = args[args.index("--fc-file") + 1] if "--fc-file" in args else None
    expected = expected_files(*blocks(fc_source(local)))
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    defs = (ROOT / "ButsonHadamard" / "Defs.lean").read_text(encoding="utf-8")
    errors = check(challenge, defs, expected)
    for e in errors:
        print("error:", e)
    if errors:
        raise SystemExit(1)
    print("Challenge.lean and ButsonHadamard/Defs.lean match Formal Conjectures at", FC_COMMIT[:8])
    if "--self-test" in args:
        smuggled = ("-/\nlocal macro_rules | `($a ∣ $b) => `(True)\n/- -/\n\n@[expose] public section")
        challenge_mutations = [
            ("(n : ℂ) • 1\n", "(n : ℂ) • 2\n"),
            ("(hn : 2 ≤ n)", "(hn : 1 ≤ n)"),
            ("    p ∣ n := by", "    p ∣ 2 * n := by"),
            ("(∀ i j, M i j ^ k = 1)", "(∀ i j, M i j ^ (k + 1) = 1)"),
            ("end ButsonHadamardMatrix", "theorem extra : True := trivial\n\nend ButsonHadamardMatrix"),
            ("-/\n\n@[expose] public section", smuggled),
            ("public import Mathlib.LinearAlgebra.Matrix.ConjTranspose\n",
             "public import Mathlib.LinearAlgebra.Matrix.ConjTranspose\npublic import Mathlib.Tactic\n"),
        ]
        defs_mutations = [
            ("def IsButsonHadamard {n : ℕ} (k : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=\n"
             "  0 < k ∧ (∀ i j, M i j ^ k = 1) ∧ M * M.conjTranspose = (n : ℂ) • 1\n",
             "/- def IsButsonHadamard {n : ℕ} (k : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=\n"
             "  0 < k ∧ (∀ i j, M i j ^ k = 1) ∧ M * M.conjTranspose = (n : ℂ) • 1 -/\n"
             "def IsButsonHadamard {n : ℕ} (k : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop := True\n"),
        ]
        total = len(challenge_mutations) + len(defs_mutations)
        caught = 0
        for old, new in challenge_mutations:
            assert challenge.replace("\r\n", "\n").count(old) == 1, old
            if check(challenge.replace("\r\n", "\n").replace(old, new), defs, expected):
                caught += 1
            else:
                print("error: mutation not caught:", new)
        for old, new in defs_mutations:
            assert defs.replace("\r\n", "\n").count(old) == 1, old
            if check(challenge, defs.replace("\r\n", "\n").replace(old, new), expected):
                caught += 1
            else:
                print("error: Defs mutation not caught")
        print(f"self-test: {caught} of {total} mutations caught")
        if caught != total:
            raise SystemExit(1)


if __name__ == "__main__":
    main()
