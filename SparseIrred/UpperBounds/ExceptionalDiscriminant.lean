import SparseIrred.UpperBounds.PolynomialDiscriminantBounds

/-!
# The exceptional discriminant integer

For a positive-degree separable integer divisor `F` of the input `f`, this file bounds the
actual integer `lc(F) * Disc(F)` and its distinct prime divisors by `2 * deg(f) * inputDelta f`.
The Vandermonde discriminant identity is kept as an explicit standard algebraic input;
all size estimates, logarithmic rounding, and exceptional-prime counting are proved here.
-/

namespace SparseIrred.UpperBounds

open Polynomial

/-- The integer whose prime divisors are excluded in the good-reduction argument. -/
noncomputable def exceptionalInteger (F : ℤ[X]) : ℤ := F.leadingCoeff * F.discr

/-- A separable complex polynomial has nonzero discriminant, including degree zero. -/
theorem complex_discr_ne_zero_of_separable (f : ℂ[X]) (hf : f.Separable) :
    f.discr ≠ 0 := by
  by_cases hd : f.natDegree = 0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hd
    simp
  have hr := Polynomial.resultant_ne_zero f f.derivative hf
  rw [natDegree_derivative, resultant_deriv (natDegree_pos_iff_degree_pos.mp (by omega))] at hr
  exact right_ne_zero_of_mul hr

/-- Separability after embedding in `ℂ` makes the actual exceptional integer nonzero. -/
theorem exceptionalInteger_ne_zero (F : ℤ[X])
    (hF : (F.map (Int.castRingHom ℂ)).Separable) : exceptionalInteger F ≠ 0 := by
  have hF0 : F ≠ 0 := by
    intro h
    exact hF.ne_zero (by simp [h])
  apply mul_ne_zero (leadingCoeff_ne_zero.mpr hF0)
  intro h
  have hd := complex_discr_ne_zero_of_separable _ hF
  rw [← integer_discr_map_complex, h, Int.cast_zero] at hd
  exact hd rfl

/-- The real Mahler estimate gives the corresponding natural-number size inequality. -/
theorem exceptionalInteger_natAbs_le (F : ℤ[X]) (S : ℕ) (hdegree : 1 ≤ F.natDegree)
    (r : Fin (F.map (Int.castRingHom ℂ)).natDegree → ℂ)
    (hroots : (List.ofFn r : Multiset ℂ) = (F.map (Int.castRingHom ℂ)).roots)
    (hformula : (F.map (Int.castRingHom ℂ)).discr =
      (F.map (Int.castRingHom ℂ)).leadingCoeff ^ (2 * F.natDegree - 2) *
        (Matrix.vandermonde r).det ^ 2)
    (hM : F.mapMahlerMeasure (Int.castRingHom ℂ) ≤ S) :
    (exceptionalInteger F).natAbs ≤ F.natDegree ^ F.natDegree * S ^ (2 * F.natDegree - 1) := by
  exact_mod_cast integer_exceptional_norm_le F S hdegree r hroots hformula hM

/-- Rounding the degree and coefficient logarithms up gives the claimed binary size bound. -/
theorem exceptional_size_le_inputDelta (f : ℤ[X]) (N Z : ℕ) (hN : N ≤ f.natDegree)
    (hZ : Z ≤ N ^ N * integerL1 f ^ (2 * N - 1)) :
    Z ≤ 2 ^ (2 * f.natDegree * inputDelta f) := by
  let u := Nat.clog 2 (f.natDegree + 2)
  let v := Nat.clog 2 (integerL1 f + 2)
  have hn : N ≤ 2 ^ u := hN.trans
    ((Nat.le_add_right _ 2).trans (Nat.le_pow_clog (by decide) _))
  have hS : integerL1 f ≤ 2 ^ v :=
    (Nat.le_add_right _ 2).trans (Nat.le_pow_clog (by decide) _)
  have he : u * N + v * (2 * N - 1) ≤ 2 * f.natDegree * inputDelta f := by
    have h₁ := Nat.mul_le_mul_left u hN
    have h₂ := Nat.mul_le_mul_left v
      (show 2 * N - 1 ≤ 2 * f.natDegree by omega)
    change _ ≤ 2 * f.natDegree * (u + v + 2)
    nlinarith
  calc
    Z ≤ N ^ N * integerL1 f ^ (2 * N - 1) := hZ
    _ ≤ (2 ^ u) ^ N * (2 ^ v) ^ (2 * N - 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hn _) (Nat.pow_le_pow_left hS _)
    _ = 2 ^ (u * N + v * (2 * N - 1)) := by rw [← pow_mul, ← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

/-- The exceptional integer of an integer divisor has the required binary size. -/
theorem exceptionalInteger_le_pow_inputDelta (f F : ℤ[X]) (hf : f ≠ 0) (hFf : F ∣ f)
    (hdegree : 1 ≤ F.natDegree)
    (r : Fin (F.map (Int.castRingHom ℂ)).natDegree → ℂ)
    (hroots : (List.ofFn r : Multiset ℂ) = (F.map (Int.castRingHom ℂ)).roots)
    (hformula : (F.map (Int.castRingHom ℂ)).discr =
      (F.map (Int.castRingHom ℂ)).leadingCoeff ^ (2 * F.natDegree - 2) *
        (Matrix.vandermonde r).det ^ 2) :
    (exceptionalInteger F).natAbs ≤ 2 ^ (2 * f.natDegree * inputDelta f) := by
  apply exceptional_size_le_inputDelta f F.natDegree _ (natDegree_le_of_dvd hFf hf)
  apply exceptionalInteger_natAbs_le F (integerL1 f) hdegree r hroots hformula
  exact (integerMahler_le_of_dvd f F hf hFf).trans (integerMahler_le_integerL1 f)

/-- A separable integer divisor has at most `2 * deg(f) * Δ` exceptional primes. -/
theorem exceptionalInteger_primeFactors_card_le (f F : ℤ[X]) (hf : f ≠ 0) (hFf : F ∣ f)
    (hdegree : 1 ≤ F.natDegree) (hsep : (F.map (Int.castRingHom ℂ)).Separable)
    (r : Fin (F.map (Int.castRingHom ℂ)).natDegree → ℂ)
    (hroots : (List.ofFn r : Multiset ℂ) = (F.map (Int.castRingHom ℂ)).roots)
    (hformula : (F.map (Int.castRingHom ℂ)).discr =
      (F.map (Int.castRingHom ℂ)).leadingCoeff ^ (2 * F.natDegree - 2) *
        (Matrix.vandermonde r).det ^ 2) :
    (exceptionalInteger F).natAbs.primeFactors.card ≤ 2 * f.natDegree * inputDelta f := by
  apply exceptional_prime_card_bound _ (exceptionalInteger_ne_zero F hsep)
  exact exceptionalInteger_le_pow_inputDelta f F hf hFf hdegree r hroots hformula

end SparseIrred.UpperBounds
