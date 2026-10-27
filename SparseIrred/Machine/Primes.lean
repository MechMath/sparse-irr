import Mathlib
import SparseIrred.Construction.Defs

/-!
# The first `n` odd primes by trial division (data level)

The notes (p. 7) place all `q_i` below `O(n log n)`, so that a sieve finds them in polynomial time.
We use the cruder but elementary bound `q_i = nth Prime (i+1) ≤ 64 (i+2)^2` (`oddPrime_le`),
derived from Chebyshev's bound `2^x ≤ (x+1) · lcm(1, …, x)` (`Chebyshev.two_pow_le_mul_lcmUpto`);
it is enough for a candidate range of polynomial size.

* `oddPrimesBelow T`: the odd primes `< T`, increasing (a filter of `List.range T`);
* `firstOddPrimes T n`: its first `n` entries;
* `primeBound L = 64 (L+2)^2 + 1`: the candidate range used on an input of length `L`;
* `firstOddPrimes_eq`: if every `oddPrime i` (`i < n`) is `< T`, the list is exactly
  `oddPrimeList n = [oddPrime 0, …, oddPrime (n-1)]`;
* `firstOddPrimes_primeBound`: the range `primeBound L` suffices when `n ≤ L + 1`.

The string implementation is in `Machine/StrPrimes.lean` (candidates in unary, trial division by
every `d < c`).
-/

namespace SparseIrred.Machine

open SparseIrred

/-- The odd primes below `T`, in increasing order. -/
def oddPrimesBelow (T : ℕ) : List ℕ :=
  (List.range T).filter fun c => decide (3 ≤ c ∧ c.Prime)

/-- The first `n` odd primes below `T`. -/
def firstOddPrimes (T n : ℕ) : List ℕ := (oddPrimesBelow T).take n

/-- The candidate range used by the machine on an input of length `L`. -/
def primeBound (L : ℕ) : ℕ := 64 * (L + 2) ^ 2 + 1

/-- The mathematical prime list `[q_0, …, q_{n-1}]` of the notes (noncomputable: `Nat.nth`). -/
noncomputable def oddPrimeList (n : ℕ) : List ℕ := (List.range n).map oddPrime

/-! ### An explicit polynomial bound on the `k`-th prime -/

/-- Chebyshev's bound in the form `2^x ≤ (x + 1) x^{π(x)}`. -/
theorem two_pow_le_pow_primeCounting (x : ℕ) :
    2 ^ x ≤ (x + 1) * x ^ (Nat.primeCounting x) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  calc 2 ^ x ≤ (x + 1) * Nat.lcmUpto x := Chebyshev.two_pow_le_mul_lcmUpto x
    _ ≤ (x + 1) * x ^ (Nat.primeCounting x) := by
      gcongr
      rw [Nat.lcmUpto_eq_prod_pow_log, ← Nat.primesLE_card_eq_primeCounting]
      exact Finset.prod_le_pow_card _ _ _ fun p _ => Nat.pow_log_le_self p hx.ne'

/-- The `k`-th prime (counting from `0`) is at most `64 (k + 1)^2`. -/
theorem nth_prime_le (k : ℕ) : Nat.nth Nat.Prime k ≤ 64 * (k + 1) ^ 2 := by
  set L := Nat.log 2 (k + 1)
  have hL1 : 2 ^ L ≤ k + 1 := Nat.pow_log_le_self 2 (by omega)
  have hL2 : k + 1 < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hL3 : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
  set s := 2 * L + 6
  set x := 2 ^ s
  have hxs : s * (k + 1) + 1 < x := by
    have h1 : 2 ^ s = 2 ^ (L + 5) * 2 ^ (L + 1) := by rw [← pow_add]; congr 1; omega
    have h2 : 2 ^ (L + 5) = 32 * 2 ^ L := by rw [pow_add]; norm_num; ring
    have h3 : 0 < 2 ^ (L + 1) := by positivity
    show s * (k + 1) + 1 < 2 ^ s
    rw [h1]
    calc s * (k + 1) + 1 < s * 2 ^ (L + 1) + 2 ^ (L + 1) := by
            have := Nat.mul_lt_mul_of_pos_left hL2 (show 0 < s by omega); omega
      _ = (s + 1) * 2 ^ (L + 1) := by ring
      _ ≤ 2 ^ (L + 5) * 2 ^ (L + 1) := by gcongr; omega
  have hpi : k < Nat.primeCounting x := by
    by_contra hcon
    push Not at hcon
    have h := two_pow_le_pow_primeCounting x
    have hx1 : x + 1 ≤ 2 ^ (s + 1) := by rw [pow_succ]; have : 1 ≤ x := Nat.one_le_two_pow; omega
    have hxk : x ^ Nat.primeCounting x ≤ x ^ k := Nat.pow_le_pow_right Nat.one_le_two_pow hcon
    have : 2 ^ x ≤ 2 ^ (s + 1 + s * k) := by
      calc 2 ^ x ≤ (x + 1) * x ^ Nat.primeCounting x := h
        _ ≤ 2 ^ (s + 1) * x ^ k := Nat.mul_le_mul hx1 hxk
        _ = 2 ^ (s + 1 + s * k) := by simp only [x]; rw [← pow_mul, ← pow_add]
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
    nlinarith
  have hlt : Nat.nth Nat.Prime k < x + 1 := Nat.nth_lt_of_lt_count hpi
  have hx : x ≤ 64 * (k + 1) ^ 2 := by
    calc x = 64 * (2 ^ L) ^ 2 := by rw [← pow_mul]; simp only [x, s]; rw [pow_add]; norm_num; ring
      _ ≤ 64 * (k + 1) ^ 2 := by gcongr
  omega

/-- The `i`-th odd prime is at most `64 (i+2)^2`. -/
theorem oddPrime_le (i : ℕ) : oddPrime i ≤ 64 * (i + 2) ^ 2 := by
  simpa [oddPrime] using nth_prime_le (i + 1)

/-- Every `q_i` with `i < n` is below the machine's candidate range when `n ≤ L + 1`. -/
theorem oddPrime_lt_primeBound {n L i : ℕ} (hn : n ≤ L + 1) (hi : i < n) :
    oddPrime i < primeBound L := by
  have h1 := oddPrime_le i
  have h2 : (i + 2) ^ 2 ≤ (L + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  unfold primeBound
  omega

/-! ### The filtered list is the list of the first odd primes -/

theorem mem_oddPrimesBelow {T c : ℕ} : c ∈ oddPrimesBelow T ↔ c < T ∧ 3 ≤ c ∧ c.Prime := by
  simp [oddPrimesBelow]

/-- The predicate "odd prime". -/
def IsOddPrime (c : ℕ) : Prop := 3 ≤ c ∧ c.Prime

instance : DecidablePred IsOddPrime := fun c => by unfold IsOddPrime; infer_instance

theorem oddPrimesBelow_succ (T : ℕ) :
    oddPrimesBelow (T + 1) = oddPrimesBelow T ++ if IsOddPrime T then [T] else [] := by
  unfold oddPrimesBelow IsOddPrime
  rw [List.range_succ, List.filter_append]
  split_ifs with h <;> simp [h]

theorem length_oddPrimesBelow (T : ℕ) : (oddPrimesBelow T).length = Nat.count IsOddPrime T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [oddPrimesBelow_succ, Nat.count_succ, List.length_append, ih]
    split_ifs <;> simp

/-- The odd prime `c < T` sits at position `count IsOddPrime c`. -/
theorem getElem?_oddPrimesBelow_count {T c : ℕ} (hc : c < T) (hp : IsOddPrime c) :
    (oddPrimesBelow T)[Nat.count IsOddPrime c]? = some c := by
  induction T with
  | zero => omega
  | succ T ih =>
    rw [oddPrimesBelow_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | rfl
    · rw [List.getElem?_append_left (by
        rw [length_oddPrimesBelow]; exact Nat.count_strict_mono hp h)]
      exact ih h
    · rw [List.getElem?_append_right (by rw [length_oddPrimesBelow]), length_oddPrimesBelow,
        Nat.sub_self]
      simp only [hp, ↓reduceIte]
      rfl

/-- The primes below `n` are the odd primes below `n` together with `2` (when `3 ≤ n`). -/
theorem count_isOddPrime_add (n : ℕ) :
    Nat.count IsOddPrime n + (if 3 ≤ n then 1 else 0) = Nat.count Nat.Prime n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, Nat.count_succ, ← ih]
    by_cases h3 : 3 ≤ n
    · have : 3 ≤ n + 1 := by omega
      simp only [h3, this, ↓reduceIte, IsOddPrime, true_and]
      split_ifs <;> omega
    · by_cases h2 : n = 2
      · subst h2
        simp [IsOddPrime, Nat.prime_two]
      · have hn : n < 2 := by omega
        have hnp : ¬ n.Prime := fun hp => by have := hp.two_le; omega
        have : ¬ 3 ≤ n + 1 := by omega
        simp [IsOddPrime, hnp, h3, this]

theorem isOddPrime_oddPrime (i : ℕ) : IsOddPrime (oddPrime i) := by
  refine ⟨?_, Nat.prime_nth_prime _⟩
  have h := Nat.nth_monotone Nat.infinite_setOfPred_prime (show 1 ≤ i + 1 by omega)
  rw [Nat.nth_prime_one_eq_three] at h
  exact h

/-- `oddPrime i` is the `i`-th odd prime: exactly `i` odd primes lie below it. -/
theorem count_isOddPrime_oddPrime (i : ℕ) : Nat.count IsOddPrime (oddPrime i) = i := by
  have h := count_isOddPrime_add (oddPrime i)
  simp only [(isOddPrime_oddPrime i).1, ↓reduceIte] at h
  rw [oddPrime, Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at h
  unfold oddPrime
  omega

/-- `oddPrimesBelow T` is an initial segment of the sequence of odd primes: its `i`-th entry is
`oddPrime i` whenever `oddPrime i < T`, because `oddPrime i` sits at position
`count IsOddPrime (oddPrime i) = i`. -/
theorem getElem?_oddPrimesBelow {T i : ℕ} (hi : oddPrime i < T) :
    (oddPrimesBelow T)[i]? = some (oddPrime i) := by
  have h := getElem?_oddPrimesBelow_count hi (isOddPrime_oddPrime i)
  rwa [count_isOddPrime_oddPrime] at h

/-- The first `n` odd primes below `T` are `oddPrimeList n` once all of them are `< T`. -/
theorem firstOddPrimes_eq {T n : ℕ} (hT : ∀ i < n, oddPrime i < T) :
    firstOddPrimes T n = oddPrimeList n := by
  refine List.ext_getElem? fun i => ?_
  rw [firstOddPrimes, List.getElem?_take, oddPrimeList, List.getElem?_map]
  by_cases h : i < n
  · simp only [h, ↓reduceIte]
    rw [getElem?_oddPrimesBelow (hT i h), List.getElem?_range h]
    rfl
  · simp only [h, ↓reduceIte]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

/-- The machine's candidate range suffices whenever `n ≤ L + 1`. -/
theorem firstOddPrimes_primeBound {n L : ℕ} (hn : n ≤ L + 1) :
    firstOddPrimes (primeBound L) n = oddPrimeList n :=
  firstOddPrimes_eq fun _ hi => oddPrime_lt_primeBound hn hi

end SparseIrred.Machine
