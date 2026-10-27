import SparseIrred.UpperBounds.PrimeIdealComparison
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-!
# Rational prime ideals and rational primes

The specialization of the external prime-ideal estimate to `ℚ` uses the actual
norm-preserving correspondence between nonzero prime ideals of `𝓞 ℚ` and natural
prime numbers. This file proves that correspondence from the ideal APIs.
-/

namespace SparseIrred.UpperBounds

open IsDedekindDomain NumberField

/-- A ring isomorphism preserves the absolute ideal norm, defined by the quotient size. -/
theorem absNorm_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Free ℤ R] [Module.Free ℤ S]
    (e : R ≃+* S) (I : Ideal R) : Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv.symm

/-- The nonzero prime ideals of the integers are exactly the ideals `(p)`, for prime `p`. -/
noncomputable def integerPrimeIdealEquiv : HeightOneSpectrum ℤ ≃ Nat.Primes where
  toFun P := ⟨Ideal.absNorm P.asIdeal, (Int.prime_absNorm P.asIdeal).mpr P.prime⟩
  invFun p := by
    letI : Fact p.val.Prime := ⟨p.property⟩
    exact ⟨Ideal.span {(p.val : ℤ)}, inferInstance,
      by simpa [Ideal.span_singleton_eq_bot] using p.property.ne_zero⟩
  left_inv P := by
    apply HeightOneSpectrum.ext
    exact Int.ideal_span_absNorm_eq_self P.asIdeal
  right_inv p := by
    apply Subtype.ext
    simp

/-- The rational prime corresponding to an integer prime ideal is its absolute norm. -/
theorem integerPrimeIdealEquiv_norm (P : HeightOneSpectrum ℤ) :
    (integerPrimeIdealEquiv P).val = Ideal.absNorm P.asIdeal := rfl

/-- The nonzero prime ideals of the ring of integers of `ℚ`, identified with natural primes. -/
noncomputable def rationalPrimeIdealEquiv : HeightOneSpectrum (𝓞 ℚ) ≃ Nat.Primes :=
  (HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv).trans integerPrimeIdealEquiv

/-- The preceding correspondence preserves the norm, so it also preserves any cutoff. -/
theorem rationalPrimeIdealEquiv_norm (P : HeightOneSpectrum (𝓞 ℚ)) :
    (rationalPrimeIdealEquiv P).val = Ideal.absNorm P.asIdeal := by
  change Ideal.absNorm (P.asIdeal.comap Rat.ringOfIntegersEquiv.symm) = _
  rw [← Ideal.map_comap_of_equiv Rat.ringOfIntegersEquiv]
  exact absNorm_map_ringEquiv Rat.ringOfIntegersEquiv P.asIdeal

/-- The bounded subtype of natural primes is counted by the inclusive prime-counting function. -/
theorem natCard_bounded_primes (X : ℕ) :
    Nat.card {p : Nat.Primes // p.val ≤ X} = X.primeCounting := by
  classical
  let e : {p : Nat.Primes // p.val ≤ X} ≃ {p // p ∈ X.primesLE} :=
    { toFun := fun p ↦ ⟨p.val.val, Nat.mem_primesLE.mpr ⟨p.property, p.val.property⟩⟩
      invFun := fun p ↦ ⟨⟨p.val, (Nat.mem_primesLE.mp p.property).2⟩,
        (Nat.mem_primesLE.mp p.property).1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    _ = Nat.card {p // p ∈ X.primesLE} := Nat.card_congr e
    _ = X.primeCounting := by simp [Nat.primesLE_card_eq_primeCounting]

/-- The rational specialization uses genuine prime ideals, not a postulated count equality. -/
theorem natCard_bounded_rational_primeIdeals (X : ℕ) :
    Nat.card {P : HeightOneSpectrum (𝓞 ℚ) // Ideal.absNorm P.asIdeal ≤ X} =
      X.primeCounting := by
  let e := rationalPrimeIdealEquiv.subtypeEquiv
    (p := fun P ↦ Ideal.absNorm P.asIdeal ≤ X) (q := fun p ↦ p.val ≤ X)
    (fun P ↦ by rw [rationalPrimeIdealEquiv_norm])
  exact (Nat.card_congr e).trans (natCard_bounded_primes X)

/-- Specializing the actual number-field counting function to `ℚ` gives `π(X)`. -/
theorem rational_primeIdealCountLE (X : ℕ) : primeIdealCountLE ℚ X = X.primeCounting := by
  rw [primeIdealCountLE_eq_natCard_heightOne]
  exact natCard_bounded_rational_primeIdeals X

end SparseIrred.UpperBounds
