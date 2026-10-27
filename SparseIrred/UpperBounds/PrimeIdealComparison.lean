import Mathlib
import SparseIrred.UpperBounds.ModularRoots

/-!
# Higher-residue-degree prime ideals

These counts concern actual ideals in the ring of integers of a number field. The
fundamental ramification-inertia identity bounds the number above a rational prime;
the ideal norm formula then confines every higher-degree contribution to primes
below the square root of the norm cutoff. No analytic prime-ideal estimate is assumed.
-/

open NumberField Ideal
open scoped BigOperators

namespace SparseIrred.UpperBounds

open Polynomial UniqueFactorizationMonoid

/-- Actual nonzero prime ideals whose absolute norm is at most the cutoff. -/
noncomputable def primeIdealsLE (K : Type*) [Field K] [NumberField K] (X : ℕ) :
    Finset (Ideal (𝓞 K)) := by
  classical
  exact ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) X).toFinset).filter
    (fun P ↦ P.IsPrime ∧ P ≠ ⊥)

/-- The number-field prime-ideal counting function at an integer cutoff. -/
noncomputable def primeIdealCountLE (K : Type*) [Field K] [NumberField K] (X : ℕ) : ℕ :=
  (primeIdealsLE K X).card

/-- The part of the prime-ideal count having residue degree one over `ℚ`. -/
noncomputable def degreeOnePrimeIdealCountLE (K : Type*) [Field K] [NumberField K]
    (X : ℕ) : ℕ := by
  classical
  exact ((primeIdealsLE K X).filter (fun P ↦ P.inertiaDeg ℤ = 1)).card

/-- The prime ideals above a rational prime, with an empty value at nonprimes. -/
noncomputable def rationalPrimeIdealsOver (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    Finset (Ideal (𝓞 K)) := by
  classical
  exact if hp : p.Prime then
    let _ : Fact p.Prime := ⟨hp⟩
    (IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) (𝓞 K)).toFinset
  else ∅

theorem mem_primeIdealsLE (K : Type*) [Field K] [NumberField K]
    (X : ℕ) (P : Ideal (𝓞 K)) :
    P ∈ primeIdealsLE K X ↔ P.absNorm ≤ X ∧ P.IsPrime ∧ P ≠ ⊥ := by
  classical
  simp [primeIdealsLE]

/-- The prime-over set has its usual interpretation at a rational prime. -/
theorem mem_rationalPrimeIdealsOver (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K)) :
    P ∈ rationalPrimeIdealsOver K p ↔
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  classical
  simp [rationalPrimeIdealsOver, hp, Ideal.primesOver]

/-- The fundamental identity bounds the number of prime ideals above every rational prime. -/
theorem rationalPrimeIdealsOver_card_le (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    (rationalPrimeIdealsOver K p).card ≤ Module.finrank ℚ K := by
  classical
  unfold rationalPrimeIdealsOver
  split_ifs with hp
  · have : Fact p.Prime := ⟨hp⟩
    dsimp only
    rw [Set.Finite.card_toFinset]
    calc
      Fintype.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) =
          ∑ _P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), 1 := by simp
      _ ≤ ∑ P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
          P.val.ramificationIdx ℤ * P.val.inertiaDeg ℤ := by
        apply Finset.sum_le_sum
        intro P _
        have : P.val.IsPrime := P.prop.1
        exact Nat.mul_pos (Ideal.ramificationIdx_pos P.val ℤ) (Ideal.inertiaDeg_pos P.val ℤ)
      _ = Module.finrank ℚ K :=
        (Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)).trans
          (NumberField.RingOfIntegers.rank K)
  · simp

/-- A higher-residue-degree ideal below `X` lies above a rational prime at most `sqrt X`. -/
theorem higherResidue_under_le_sqrt (K : Type*) [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (X : ℕ) (hP : P ∈ primeIdealsLE K X)
    (hdeg : P.inertiaDeg ℤ ≠ 1) :
    let p := (P.under ℤ).absNorm
    p.Prime ∧ p ≤ X.sqrt ∧ P ∈ rationalPrimeIdealsOver K p := by
  classical
  obtain ⟨hX, hprime, hne⟩ := (mem_primeIdealsLE K X P).mp hP
  have : P.IsPrime := hprime
  have : NeZero P := ⟨hne⟩
  let p := (P.under ℤ).absNorm
  have hp : p.Prime := Nat.absNorm_under_prime P
  have hpos := Ideal.inertiaDeg_pos P ℤ
  have htwo : 2 ≤ P.inertiaDeg ℤ := by omega
  have hsquare : p ^ 2 ≤ X := by
    calc
      p ^ 2 ≤ p ^ P.inertiaDeg ℤ := Nat.pow_le_pow_right hp.pos htwo
      _ = P.absNorm := Ideal.pow_inertiaDeg p P
      _ ≤ X := hX
  refine ⟨hp, Nat.le_sqrt'.mpr hsquare, ?_⟩
  exact (mem_rationalPrimeIdealsOver K p hp P).mpr ⟨hprime, inferInstance⟩

/-- The higher-residue part of the actual prime-ideal count has the square-root error bound. -/
theorem primeIdealCountLE_sub_degreeOne_le_sqrt (K : Type*) [Field K] [NumberField K]
    (X : ℕ) :
    primeIdealCountLE K X - degreeOnePrimeIdealCountLE K X ≤ Module.finrank ℚ K * X.sqrt := by
  classical
  have hsplit : ((primeIdealsLE K X).filter (fun P ↦ P.inertiaDeg ℤ = 1)).card +
      ((primeIdealsLE K X).filter (fun P ↦ P.inertiaDeg ℤ ≠ 1)).card =
      (primeIdealsLE K X).card :=
    Finset.card_filter_add_card_filter_not (s := primeIdealsLE K X)
      (fun P ↦ P.inertiaDeg ℤ = 1)
  have hdiff : primeIdealCountLE K X - degreeOnePrimeIdealCountLE K X =
      ((primeIdealsLE K X).filter (fun P ↦ P.inertiaDeg ℤ ≠ 1)).card := by
    unfold primeIdealCountLE degreeOnePrimeIdealCountLE
    omega
  rw [hdiff]
  calc
    _ ≤ ((Finset.Icc 1 X.sqrt).biUnion (rationalPrimeIdealsOver K)).card := by
      apply Finset.card_le_card
      intro P hP
      obtain ⟨hPX, hdeg⟩ := Finset.mem_filter.mp hP
      obtain ⟨hp, hpsqrt, hmem⟩ := higherResidue_under_le_sqrt K P X hPX hdeg
      exact Finset.mem_biUnion.mpr
        ⟨(P.under ℤ).absNorm, Finset.mem_Icc.mpr ⟨hp.pos, hpsqrt⟩, hmem⟩
    _ ≤ ∑ p ∈ Finset.Icc 1 X.sqrt, (rationalPrimeIdealsOver K p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ Finset.Icc 1 X.sqrt, Module.finrank ℚ K := by
      exact Finset.sum_le_sum (fun p _ ↦ rationalPrimeIdealsOver_card_le K p)
    _ = _ := by simp [Nat.mul_comm]

/-- The degree-one count is a subcount of the complete prime-ideal count. -/
theorem degreeOnePrimeIdealCountLE_le (K : Type*) [Field K] [NumberField K] (X : ℕ) :
    degreeOnePrimeIdealCountLE K X ≤ primeIdealCountLE K X := by
  classical
  exact Finset.card_filter_le _ _

/-- The bounded-ideal finset and the customary bounded height-one spectrum are equivalent. -/
noncomputable def primeIdealsLEEquivHeightOne (K : Type*) [Field K] [NumberField K] (X : ℕ) :
    ↥(primeIdealsLE K X) ≃
      {P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // P.asIdeal.absNorm ≤ X} where
  toFun P :=
    let h := (mem_primeIdealsLE K X P.val).mp P.prop
    ⟨⟨P.val, h.2.1, h.2.2⟩, h.1⟩
  invFun P := ⟨P.val.asIdeal,
    (mem_primeIdealsLE K X P.val.asIdeal).mpr ⟨P.prop, P.val.isPrime, P.val.ne_bot⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext rfl)

/-- Agreement with the usual counting function expressed using `HeightOneSpectrum`. -/
theorem primeIdealCountLE_eq_natCard_heightOne (K : Type*) [Field K] [NumberField K]
    (X : ℕ) : primeIdealCountLE K X =
      Nat.card {P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // P.asIdeal.absNorm ≤ X} := by
  classical
  calc
    _ = Nat.card ↥(primeIdealsLE K X) := by
      simp [primeIdealCountLE, Nat.card_eq_fintype_card]
    _ = _ := Nat.card_congr (primeIdealsLEEquivHeightOne K X)

/-- Finiteness needed for cardinal manipulations in the customary counting-function type. -/
theorem finite_heightOne_normLE (K : Type*) [Field K] [NumberField K] (X : ℕ) :
    Finite {P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // P.asIdeal.absNorm ≤ X} :=
  Finite.of_equiv ↥(primeIdealsLE K X) (primeIdealsLEEquivHeightOne K X)

/-- The square-root comparison in the real-valued form used by the analytic estimate. -/
theorem primeIdealCountLE_sub_degreeOne_le_real_sqrt (K : Type*) [Field K] [NumberField K]
    (X : ℕ) : (primeIdealCountLE K X : ℝ) - degreeOnePrimeIdealCountLE K X ≤
      (Module.finrank ℚ K : ℝ) * Real.sqrt X := by
  have hnat := primeIdealCountLE_sub_degreeOne_le_sqrt K X
  have hcast : ((primeIdealCountLE K X - degreeOnePrimeIdealCountLE K X : ℕ) : ℝ) ≤
      (Module.finrank ℚ K : ℝ) * (X.sqrt : ℝ) := by exact_mod_cast hnat
  rw [Nat.cast_sub (degreeOnePrimeIdealCountLE_le K X)] at hcast
  have hsqrt : (X.sqrt : ℝ) ≤ Real.sqrt X := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    have hsq : X.sqrt ^ 2 ≤ X := by simpa [pow_two] using Nat.sqrt_le X
    exact_mod_cast hsq
  exact hcast.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))

/-- Distinct roots are exactly the distinct monic irreducible factors of degree one. -/
theorem rootCount_eq_linearFactor_card {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    (g : k[X]) (hg : g ≠ 0) :
    rootCount g = ((normalizedFactors g).toFinset.filter (fun Q ↦ Q.natDegree = 1)).card := by
  classical
  unfold rootCount
  refine Finset.card_bij (fun a _ ↦ X - C a) ?_ ?_ ?_
  · intro a ha
    have hr : g.eval a = 0 := (Finset.mem_filter.mp ha).2
    refine Finset.mem_filter.mpr ⟨?_, natDegree_X_sub_C a⟩
    apply Multiset.mem_toFinset.mpr
    exact (Polynomial.mem_normalizedFactors_iff hg).mpr
      ⟨irreducible_X_sub_C a, monic_X_sub_C a, dvd_iff_isRoot.mpr hr⟩
  · intro a _ b _ hab
    have h := congrArg (fun Q : k[X] ↦ Q.coeff 0) hab
    simpa using h
  · intro Q hQ
    obtain ⟨hfactor, hdegree⟩ := Finset.mem_filter.mp hQ
    have hdata := (Polynomial.mem_normalizedFactors_iff hg).mp
      (Multiset.mem_toFinset.mp hfactor)
    have heq : Q = X - C (-Q.coeff 0) := by
      simpa using hdata.2.1.eq_X_add_C hdegree
    refine ⟨-Q.coeff 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq.symm⟩
    exact dvd_iff_isRoot.mp (heq ▸ hdata.2.2)

/-- Kummer-Dedekind restricts to degree-one prime ideals and linear polynomial factors. -/
noncomputable def degreeOnePrimesOverEquivLinearFactors (K : Type*) [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact p.Prime] (hp : ¬p ∣ RingOfIntegers.exponent θ) :
    {P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) // P.val.inertiaDeg ℤ = 1} ≃
      {Q : RingOfIntegers.monicFactorsMod θ p // Q.val.natDegree = 1} := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  refine e.subtypeEquiv (fun P ↦ ?_)
  have hd := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    hp (e P).prop
  change (e.symm (e P)).val.inertiaDeg ℤ = (e P).val.natDegree at hd
  have heq : P.val.inertiaDeg ℤ = (e P).val.natDegree := by
    simpa only [Equiv.symm_apply_apply] using hd
  rw [heq]

private theorem card_finset_subtype_filter {α : Type*} (s : Finset α) (R : α → Prop)
    [DecidablePred R] :
    Nat.card {a : ↥s // R a.val} = (s.filter R).card := by
  classical
  let e : {a : ↥s // R a.val} ≃ ↥(s.filter R) :=
    { toFun := fun a ↦ ⟨a.val.val, Finset.mem_filter.mpr ⟨a.val.prop, a.prop⟩⟩
      invFun := fun a ↦ ⟨⟨a.val, (Finset.mem_filter.mp a.prop).1⟩,
        (Finset.mem_filter.mp a.prop).2⟩
      left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ ↦ Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The actual minpoly root count equals the number of degree-one prime ideals above `p`.
The hypothesis is precisely the standard Kummer-Dedekind index condition. -/
theorem rootCount_minpoly_eq_degreeOnePrimesOver (K : Type*) [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact p.Prime] (hp : ¬p ∣ RingOfIntegers.exponent θ) :
    rootCount ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) =
      Nat.card {P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) // P.val.inertiaDeg ℤ = 1} := by
  classical
  rw [Nat.card_congr (degreeOnePrimesOverEquivLinearFactors K θ p hp)]
  rw [card_finset_subtype_filter (RingOfIntegers.monicFactorsMod θ p)
    (fun Q ↦ Q.natDegree = 1)]
  exact rootCount_eq_linearFactor_card _ ((minpoly.monic θ.isIntegral).map _).ne_zero

end SparseIrred.UpperBounds
