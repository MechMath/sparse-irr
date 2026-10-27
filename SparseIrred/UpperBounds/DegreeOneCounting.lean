import SparseIrred.UpperBounds.PrimeIdealComparison

/-!
# Decomposing degree-one prime ideals by rational primes

The residue-degree-one count below a norm cutoff is the sum of the actual local
counts above the rational primes below that cutoff. This supplies the finite-sum
identity used when passing from good-prime root counts to number-field counts.
-/

namespace SparseIrred.UpperBounds

open NumberField Ideal
open scoped BigOperators

/-- The local degree-one count above a rational prime; it is zero at nonprimes. -/
noncomputable def degreeOnePrimesOverCount (K : Type*) [Field K] [NumberField K]
    (p : ℕ) : ℕ := by
  classical
  exact ((rationalPrimeIdealsOver K p).filter fun P ↦ P.inertiaDeg ℤ = 1).card

/-- The local degree-one count is at most the degree of the field. -/
theorem degreeOnePrimesOverCount_le (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    degreeOnePrimesOverCount K p ≤ Module.finrank ℚ K := by
  classical
  exact (Finset.card_filter_le _ _).trans (rationalPrimeIdealsOver_card_le K p)

/-- The finite local count agrees with the degree-one subtype used by Kummer-Dedekind. -/
theorem degreeOnePrimesOverCount_eq_natCard (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    degreeOnePrimesOverCount K p =
      Nat.card {P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) // P.val.inertiaDeg ℤ = 1} := by
  classical
  let s := (rationalPrimeIdealsOver K p).filter fun P ↦ P.inertiaDeg ℤ = 1
  let e : ↥s ≃
      {P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) // P.val.inertiaDeg ℤ = 1} :=
    { toFun := fun P ↦ ⟨⟨P.val, (mem_rationalPrimeIdealsOver K p hp P.val).mp
          (Finset.mem_filter.mp P.prop).1⟩, (Finset.mem_filter.mp P.prop).2⟩
      invFun := fun P ↦ ⟨P.val.val, Finset.mem_filter.mpr
        ⟨(mem_rationalPrimeIdealsOver K p hp P.val.val).mpr P.val.prop, P.prop⟩⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl) }
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, s,
    degreeOnePrimesOverCount] using Nat.card_congr e

/-- For residue degree one, the ideal norm equals the rational prime below it. -/
theorem degreeOne_absNorm_eq (K : Type*) [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) [P.IsPrime] (hdeg : P.inertiaDeg ℤ = 1) :
    P.absNorm = (P.under ℤ).absNorm := by
  simpa only [hdeg, pow_one] using (Ideal.pow_inertiaDeg (P.under ℤ).absNorm P).symm

/-- Every degree-one ideal belongs to exactly the fiber indexed by its norm. -/
theorem degreeOnePrimeIdealCountLE_eq_sum (K : Type*) [Field K] [NumberField K]
    (X : ℕ) :
    degreeOnePrimeIdealCountLE K X = ∑ p ∈ X.primesLE, degreeOnePrimesOverCount K p := by
  classical
  let s := (primeIdealsLE K X).filter fun P ↦ P.inertiaDeg ℤ = 1
  have hmap : (s : Set (Ideal (𝓞 K))).MapsTo (fun P ↦ P.absNorm) X.primesLE := by
    intro P hP
    obtain ⟨hPX, hd⟩ := Finset.mem_filter.mp hP
    obtain ⟨hX, hprime, hne⟩ := (mem_primeIdealsLE K X P).mp hPX
    have : P.IsPrime := hprime
    have : NeZero P := ⟨hne⟩
    refine Nat.mem_primesLE.mpr ⟨hX, ?_⟩
    change P.absNorm.Prime
    rw [degreeOne_absNorm_eq K P hd]
    exact Nat.absNorm_under_prime P
  change s.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpX, hprime⟩ := Nat.mem_primesLE.mp hp
  unfold degreeOnePrimesOverCount
  congr 1
  ext P
  simp only [s, Finset.mem_filter, mem_primeIdealsLE,
    mem_rationalPrimeIdealsOver K p hprime]
  constructor
  · rintro ⟨⟨⟨hX, hPprime, hne⟩, hd⟩, hnorm⟩
    have : P.IsPrime := hPprime
    refine ⟨⟨hPprime, ?_⟩, hd⟩
    have hunder : (P.under ℤ).absNorm = p := (degreeOne_absNorm_eq K P hd).symm.trans hnorm
    rw [← hunder]
    infer_instance
  · rintro ⟨⟨hPprime, hover⟩, hd⟩
    have : P.IsPrime := hPprime
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := hover
    have hunder : P.under ℤ = Ideal.span {(p : ℤ)} :=
      ((Ideal.liesOver_iff P _).mp hover).symm
    have hnorm : P.absNorm = p := by
      rw [degreeOne_absNorm_eq K P hd, hunder, Ideal.absNorm_span_natCast]
      simp
    have hne : P ≠ ⊥ := by
      intro he
      rw [he, Ideal.absNorm_bot] at hnorm
      exact hprime.ne_zero hnorm.symm
    exact ⟨⟨⟨hnorm ▸ hpX, hPprime, hne⟩, hd⟩, hnorm⟩

end SparseIrred.UpperBounds
