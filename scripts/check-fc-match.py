#!/usr/bin/env python3
"""Check that Challenge.lean states Formal Conjectures' Butson theorem, with FC's definition.

Palomar's Comparator checks that Solution proves the statement of Challenge.lean, with the same
definitions. This script checks the other link: that the code of Challenge.lean is Formal
Conjectures' text.

It reads `FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at FC_COMMIT (downloaded from
GitHub, or from a local file given with --fc-file), requires its SHA-256 to be FC_SHA256, and
extracts two blocks verbatim:

* the definition `IsButsonHadamard`, from its docstring to the end of its body;
* the theorem `butson_prime_divisibility`, from its docstring to `sorry`, with FC's attribute line
  `@[category research solved, AMS 5 15]` removed (Formal Conjectures defines those attributes).

Challenge.lean's code, after its header comment, `module`, its two `public import Mathlib.…` lines
and its module docstring, must then be exactly:

    @[expose] public section
    <blank>
    namespace ButsonHadamardMatrix
    <blank>
    <the definition>
    <blank>
    <the theorem>
    <blank>
    end ButsonHadamardMatrix

`ButsonHadamard/Defs.lean` must contain the definition block verbatim too.

`--self-test` runs the check on the real files and on mutated copies of Challenge.lean (a changed
exponent, a dropped hypothesis, a changed constant, an extra declaration, a changed definition),
each of which must be rejected.
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


def expected_code(definition, theorem):
    return ("@[expose] public section\n\nnamespace ButsonHadamardMatrix\n\n" + definition + "\n"
            + theorem + "\nend ButsonHadamardMatrix\n")


def challenge_code(text):
    text = text.replace("\r\n", "\n")
    m = re.match(r"/-.*?-/\nmodule\n\n(public import Mathlib\.[A-Za-z.]+\n)+\n/-!.*?-/\n\n", text, re.S)
    if not m:
        raise ValueError("Challenge.lean preamble is not header, module, Mathlib imports, docstring")
    if "/-" in m.group(0)[2:].split("-/", 1)[1].split("/-!", 1)[0]:
        raise ValueError("unexpected comment between header and docstring")
    return text[m.end():]


def check(challenge_text, defs_text, definition, theorem):
    errors = []
    try:
        if challenge_code(challenge_text) != expected_code(definition, theorem):
            errors.append("Challenge.lean code differs from Formal Conjectures' text")
    except ValueError as error:
        errors.append(str(error))
    if definition not in defs_text.replace("\r\n", "\n"):
        errors.append("ButsonHadamard/Defs.lean does not contain FC's definition verbatim")
    return errors


def main():
    args = sys.argv[1:]
    local = None
    if "--fc-file" in args:
        local = args[args.index("--fc-file") + 1]
    definition, theorem = blocks(fc_source(local))
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    defs = (ROOT / "ButsonHadamard" / "Defs.lean").read_text(encoding="utf-8")
    errors = check(challenge, defs, definition, theorem)
    for e in errors:
        print("error:", e)
    if errors:
        raise SystemExit(1)
    print("Challenge.lean matches Formal Conjectures at", FC_COMMIT[:8])
    if "--self-test" in args:
        mutations = [
            ("(n : ℂ) • 1", "(n : ℂ) • 2"),
            ("(hn : 2 ≤ n)", "(hn : 1 ≤ n)"),
            ("    p ∣ n := by", "    p ∣ 2 * n := by"),
            ("(∀ i j, M i j ^ k = 1)", "(∀ i j, M i j ^ (k + 1) = 1)"),
            ("end ButsonHadamardMatrix", "theorem extra : True := trivial\n\nend ButsonHadamardMatrix"),
        ]
        caught = 0
        for old, new in mutations:
            assert challenge.count(old) == 1, old
            if check(challenge.replace(old, new), defs, definition, theorem):
                caught += 1
            else:
                print("error: mutation not caught:", new)
        bad_defs = defs.replace("0 < k ∧", "0 ≤ k ∧")
        if check(challenge, bad_defs, definition, theorem):
            caught += 1
        else:
            print("error: Defs mutation not caught")
        print(f"self-test: {caught} of {len(mutations) + 1} mutations caught")
        if caught != len(mutations) + 1:
            raise SystemExit(1)


if __name__ == "__main__":
    main()
