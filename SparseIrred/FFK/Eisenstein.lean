import Mathlib

/-!
# Eisenstein's criterion at the prime `(x - 1)` of `ℤ[x]` for the lifted binomial

In the Filaseta–Ford–Konyagin argument (Illinois J. Math. 44 (2000), proof of the Corollary), the
lift of the reciprocal polynomial of `F = A + x^M B` has, up to a power of `x`, the shape
`x^i A(x) y^ℓ - x^j B(x)` (see `Lift.lean` and `Ljunggren.lean`), here with `B = x^N - 1`.  At
this point FFK invoke Capelli's theorem.  For our pair `(A, B)`, Eisenstein's criterion at the
prime ideal `(x - 1) ⊂ ℤ[x]`, applied to the polynomial in `y` over `ℤ[x]`, suffices instead:

* the leading coefficient `x^i A(x)` is not in `(x - 1)` because `A(1) ≠ 0` (`A` is prime to `B`
  and `B(1) = 0`);
* the constant coefficient `-x^j B(x) = (x - 1) · (-x^j (1 + x + ⋯ + x^{N-1}))` is in `(x - 1)` but
  not in `(x - 1)²`, because the cofactor takes the value `-N ≠ 0` at `1`;
* all middle coefficients vanish;
* the content condition is `IsRelPrime (x^i A) (x^j B)`, which holds when `min(i, j) = 0`.

## Main results

* `irreducible_C_mul_X_pow_add_C`: Eisenstein's criterion at `(x - 1)` for a binomial
  `a y^ℓ + b ∈ ℤ[x][y]`.
* `irreducible_gapLift`: `x^i A(x) y^ℓ - x^j (x^N - 1)` is irreducible in `ℤ[x][y]` when `N > 0`,
  `ℓ > 0`, `min(i, j) = 0`, `A(0) ≠ 0` and `A` is prime to `x^N - 1`.

## Implementation notes

The ring `ℤ[x][y]` is `ℤ[X][X]`: the outer variable `X` is `y`, and `C X` is `x`.
-/

open Polynomial

namespace SparseIrred.FFK

/-- Eisenstein's criterion at `(X - 1) ⊂ ℤ[X]` for a binomial `a y^ℓ + b ∈ ℤ[X][y]`. -/
theorem irreducible_C_mul_X_pow_add_C {a b b₁ : ℤ[X]} {ℓ : ℕ} (hℓ : 0 < ℓ) (ha : a.eval 1 ≠ 0)
    (hb : b = (X - 1) * b₁) (hb₁ : b₁.eval 1 ≠ 0) (hab : IsRelPrime a b) :
    Irreducible (C a * X ^ ℓ + C b : ℤ[X][X]) := by
  classical
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hX1 : (X - 1 : ℤ[X]) = X - C 1 := by rw [map_one]
  set P : Ideal ℤ[X] := Ideal.span {X - C 1} with hP
  have hPprime : P.IsPrime :=
    (Ideal.span_singleton_prime (X_sub_C_ne_zero 1)).mpr (prime_X_sub_C 1)
  have hmemP : ∀ q : ℤ[X], q ∈ P ↔ q.eval 1 = 0 := by
    intro q; rw [hP, Ideal.mem_span_singleton, dvd_iff_isRoot]; rfl
  have hdeg1 : (C a * X ^ ℓ : ℤ[X][X]).degree = ℓ := degree_C_mul_X_pow ℓ ha0
  have hdegb : (C b : ℤ[X][X]).degree < (C a * X ^ ℓ : ℤ[X][X]).degree := by
    rw [hdeg1]; exact degree_C_le.trans_lt (by exact_mod_cast hℓ)
  have hdeg : (C a * X ^ ℓ + C b : ℤ[X][X]).degree = ℓ := by
    rw [degree_add_eq_left_of_degree_lt hdegb, hdeg1]
  have hlead : (C a * X ^ ℓ + C b : ℤ[X][X]).leadingCoeff = a := by
    rw [leadingCoeff_add_of_degree_lt' hdegb, leadingCoeff_C_mul_X_pow]
  have hcoeff : ∀ n, (C a * X ^ ℓ + C b : ℤ[X][X]).coeff n =
      (if n = ℓ then a else 0) + (if n = 0 then b else 0) := by
    intro n; rw [coeff_add, coeff_C_mul_X_pow, coeff_C]
  have hbP : b ∈ P := by rw [hmemP, hb]; simp
  apply irreducible_of_eisenstein_criterion hPprime
  · rw [hlead, hmemP]; exact ha
  · intro n hn
    rw [hdeg] at hn
    have hn' : n < ℓ := by exact_mod_cast hn
    rw [hcoeff]
    simp only [hn'.ne, ↓reduceIte, zero_add]
    split_ifs
    · exact hbP
    · exact P.zero_mem
  · rw [hdeg]; exact_mod_cast hℓ
  · rw [hcoeff]
    simp only [hℓ.ne, ↓reduceIte, zero_add]
    rw [hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    rw [hb, ← hX1, pow_two] at hdvd
    have hne : (X - 1 : ℤ[X]) ≠ 0 := by rw [hX1]; exact X_sub_C_ne_zero 1
    have h1 : (X - 1 : ℤ[X]) ∣ b₁ := (mul_dvd_mul_iff_left hne).mp hdvd
    rw [hX1, dvd_iff_isRoot] at h1
    exact hb₁ h1
  · intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have h1 := hr ℓ
    have h2 := hr 0
    rw [hcoeff] at h1 h2
    simp only [hℓ.ne', hℓ.ne, ↓reduceIte, add_zero, zero_add] at h1 h2
    exact hab h1 h2

/-- A polynomial relatively prime to `X^N - 1` does not vanish at `1`. -/
theorem eval_one_ne_zero_of_isRelPrime {A : ℤ[X]} {N : ℕ}
    (hAB : IsRelPrime A (X ^ N - 1)) : A.eval 1 ≠ 0 := by
  intro h1
  have hdA : (X - C 1 : ℤ[X]) ∣ A := dvd_iff_isRoot.mpr h1
  have hdB : (X - C 1 : ℤ[X]) ∣ X ^ N - 1 := dvd_iff_isRoot.mpr (by simp)
  exact (prime_X_sub_C (1 : ℤ)).not_isUnit (hAB hdA hdB)

/-- Removing a power of `x` from only one of two relatively prime polynomials not divisible by
`x` keeps them relatively prime. -/
theorem isRelPrime_X_pow_mul {A B : ℤ[X]} (hAB : IsRelPrime A B) (hA : A.coeff 0 ≠ 0)
    (hB : B.coeff 0 ≠ 0) {i j : ℕ} (hij : i = 0 ∨ j = 0) : IsRelPrime (X ^ i * A) (X ^ j * B) := by
  have hXA : IsRelPrime (X : ℤ[X]) A :=
    irreducible_X.isRelPrime_iff_not_dvd.mpr (by rw [X_dvd_iff]; exact hA)
  have hXB : IsRelPrime (X : ℤ[X]) B :=
    irreducible_X.isRelPrime_iff_not_dvd.mpr (by rw [X_dvd_iff]; exact hB)
  rcases hij with rfl | rfl
  · rw [pow_zero, one_mul]
    exact hXA.symm.pow_right.mul_right hAB
  · rw [pow_zero, one_mul]
    exact hXB.pow_left.mul_left hAB

/-- `X^N - 1 = (X - 1) (1 + X + ⋯ + X^{N-1})` and the cofactor is `N` at `1`. -/
theorem X_pow_sub_one_eq_mul_geom (N : ℕ) :
    (X ^ N - 1 : ℤ[X]) = (X - 1) * ∑ k ∈ Finset.range N, X ^ k := by
  rw [mul_comm, geom_sum_mul]

/-- The bivariate polynomial `x^i A(x) y^ℓ - x^j (x^N - 1)` is irreducible in `ℤ[x][y]` when
`N > 0`, `ℓ > 0`, `min(i, j) = 0`, `A(0) ≠ 0` and `A` is relatively prime to `x^N - 1`. -/
theorem irreducible_gapLift {A : ℤ[X]} {N ℓ i j : ℕ} (hN : 0 < N) (hℓ : 0 < ℓ)
    (hA0 : A.coeff 0 ≠ 0) (hAB : IsRelPrime A (X ^ N - 1)) (hij : i = 0 ∨ j = 0) :
    Irreducible (C (X ^ i * A) * X ^ ℓ + C (X ^ j * -(X ^ N - 1)) : ℤ[X][X]) := by
  have hB0 : (-(X ^ N - 1) : ℤ[X]).coeff 0 ≠ 0 := by
    simp [coeff_X_pow, hN.ne]
  apply irreducible_C_mul_X_pow_add_C hℓ (b₁ := X ^ j * -(∑ k ∈ Finset.range N, X ^ k))
  · simpa using eval_one_ne_zero_of_isRelPrime hAB
  · rw [X_pow_sub_one_eq_mul_geom]; ring
  · simp [hN.ne']
  · exact isRelPrime_X_pow_mul hAB.neg_right hA0 hB0 hij

end SparseIrred.FFK
