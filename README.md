# Consecutive powerful numbers need not contain a square (Lean 4)

A complete Lean 4 / Mathlib proof that the answer to the following question is **no**:

> If two consecutive positive integers are powerful, must at least one be a perfect square?

This is the first question of [Erdős Problem #365](https://www.erdosproblems.com/365) and is
recorded as **JSP-000301** in the
[Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301).
The separate counting question in Erdős #365 is open and is **not** addressed here.

## Result

File: [`JSP000301/Basic.lean`](JSP000301/Basic.lean)

```lean
def Powerful (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

theorem jsp_000301 :
    ¬ ∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)
```

The proof formalizes Golomb's counterexample: `12167 = 23 ^ 3` and
`12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2` are both powerful, and both lie strictly between
`110 ^ 2 = 12100` and `111 ^ 2 = 12321`, so neither is a square.
The existential form is `exists_consecutive_powerful_nonsquare`.

## Statement fidelity

- `Powerful` is the same definition as `Nat.Powerful` (`Nat.Full 2`) in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjecturesForMathlib/Data/Nat/Full.lean).
  It is restated here so the project depends on Mathlib only.
- `powerful_iff` shows that for `n ≠ 0` it is the textbook definition:
  every prime dividing `n` divides it at least twice.
- `IsSquare` is Mathlib's: `IsSquare a ↔ ∃ r, a = r * r`.
- "Positive integers" is the hypothesis `0 < n`.

## Build

```sh
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.34.0`, Mathlib tag `v4.34.0`
(commit `5ed2965256430c3649e86755f9576b54eca72435`).

## Axiom audit

`#print axioms JSP000301.jsp_000301` reports only the three standard axioms:

```
'JSP000301.jsp_000301' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, or additional axioms are used; CI rejects these tokens.

## Verification status

- 2026-09-17: checked with zero errors and zero warnings on
  [live.lean-lang.org](https://live.lean-lang.org) against Mathlib stable (Lean v4.34.0) and
  latest Mathlib (Lean v4.35.0-rc2).
- A `lake build` from this repository (see the `build` workflow) is the reference check.

## Attribution

- Mathematical result: Solomon W. Golomb, *Powerful numbers*, Amer. Math. Monthly 77 (1970),
  848–852, <https://doi.org/10.2307/2317020>. Infinitely many counterexamples: D. T. Walker,
  Fibonacci Quart. 14 (1976), 111–116.
- Lean formalization: the owner of this repository. The Lean sources were produced with AI
  assistance (Anthropic's Claude, via Claude Code) under the repository owner's direction, and
  are published here under the owner's responsibility. Contact: <info@aurorisma.com>.
