import Mathlib

/-!
# JSP-000301 · Consecutive powerful numbers need not contain a square

Problem (first question of Erdős Problem #365, <https://www.erdosproblems.com/365>):
if `n` and `n + 1` are both powerful, must `n` or `n + 1` be a perfect square?

Answer: **no**. Golomb's counterexample (Amer. Math. Monthly 77 (1970), 848–852):
`12167 = 23 ^ 3` and `12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2` are both powerful, and both lie
strictly between `110 ^ 2 = 12100` and `111 ^ 2 = 12321`, so neither is a square.
-/

namespace JSP000301

/-- `n` is *powerful* (2-full) if `p ^ 2 ∣ n` for every prime factor `p` of `n`.
This is the definition of `Nat.Powerful` (`Nat.Full 2`) used in
google-deepmind/formal-conjectures (`FormalConjecturesForMathlib/Data/Nat/Full.lean`). -/
def Powerful (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

/-- For `n ≠ 0` the definition is the textbook one: every prime dividing `n` divides it twice. -/
theorem powerful_iff {n : ℕ} (hn : n ≠ 0) :
    Powerful n ↔ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n := by
  constructor
  · intro h p hp hd
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)
  · intro h p hp
    obtain ⟨hp', hd, -⟩ := Nat.mem_primeFactors.mp hp
    exact h p hp' hd

/-- Sanity check of the definition: `12 = 2 ^ 2 * 3` is not powerful. -/
example : ¬ Powerful 12 := by
  rw [powerful_iff (by norm_num)]
  intro h
  exact absurd (h 3 Nat.prime_three (by decide)) (by decide)

/-- `12167 = 23 ^ 3` is powerful. -/
theorem powerful_12167 : Powerful 12167 := by
  rw [powerful_iff (by norm_num)]
  intro p hp hd
  have e : (12167 : ℕ) = 23 ^ 3 := by norm_num
  rw [e] at hd
  have h23 : p = 23 :=
    (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow hd)
  subst h23
  decide

/-- `12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2` is powerful. -/
theorem powerful_12168 : Powerful 12168 := by
  rw [powerful_iff (by norm_num)]
  intro p hp hd
  have e : (12168 : ℕ) = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num
  rw [e] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h | h13
  · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
    · have hp2 : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
      subst hp2
      decide
    · have hp3 : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)
      subst hp3
      decide
  · have hp13 : p = 13 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h13)
    subst hp13
    decide

/-- No perfect square lies strictly between `110 ^ 2` and `111 ^ 2`. -/
theorem not_isSquare_of_between {m : ℕ} (h1 : 110 * 110 < m) (h2 : m < 111 * 111) :
    ¬ IsSquare m := by
  rintro ⟨r, rfl⟩
  have hr1 : 110 < r := by
    by_contra hle
    have : r * r ≤ 110 * 110 :=
      Nat.mul_le_mul (Nat.le_of_not_lt hle) (Nat.le_of_not_lt hle)
    omega
  have hr2 : r < 111 := by
    by_contra hge
    have : 111 * 111 ≤ r * r :=
      Nat.mul_le_mul (Nat.le_of_not_lt hge) (Nat.le_of_not_lt hge)
    omega
  omega

theorem not_isSquare_12167 : ¬ IsSquare (12167 : ℕ) :=
  not_isSquare_of_between (by norm_num) (by norm_num)

theorem not_isSquare_12168 : ¬ IsSquare (12168 : ℕ) :=
  not_isSquare_of_between (by norm_num) (by norm_num)

/-- Golomb's counterexample, in existential form. -/
theorem exists_consecutive_powerful_nonsquare :
    ∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) :=
  ⟨12167, by norm_num, powerful_12167, powerful_12168, not_isSquare_12167, not_isSquare_12168⟩

/-- **JSP-000301** (first question of Erdős Problem #365): it is *not* true that whenever two
consecutive positive integers are both powerful, one of them is a perfect square. -/
theorem jsp_000301 :
    ¬ ∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  obtain ⟨n, hn, h1, h2, h3, h4⟩ := exists_consecutive_powerful_nonsquare
  rcases h n hn h1 h2 with hs | hs
  · exact h3 hs
  · exact h4 hs

end JSP000301

#print axioms JSP000301.jsp_000301
