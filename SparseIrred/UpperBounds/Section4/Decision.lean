import SparseIrred.UpperBounds.Section4.FactorRankOracle
import SparseIrred.UpperBounds.Section4.Encoding
import SparseIrred.UpperBounds.Section4.BerkowitzIndexed

/-!
# Sequential coefficient-oracle decision procedure

The finite test enumerates deleted rows and columns with two counters. It does not
factor the input polynomial or decide `Irreducible` as an oracle. Normalization,
zero derivative, vanishing resultant, degree zero, and degree one are included.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Matrix

/-- A tail-recursive search through `count` consecutive natural indices. -/
def scanAny (test : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | n + 1, start => if test start then true else scanAny test n (start + 1)

theorem scanAny_eq_true_iff (test : ℕ → Bool) (count start : ℕ) :
    scanAny test count start = true ↔
      ∃ i, start ≤ i ∧ i < start + count ∧ test i = true := by
  induction count generalizing start with
  | zero => simp only [scanAny, Bool.false_eq_true, Nat.add_zero, false_iff]; omega
  | succ n ih =>
      rw [scanAny]
      by_cases hs : test start = true
      · simp only [hs, ↓reduceIte, true_iff]
        exact ⟨start, le_rfl, by omega, hs⟩
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, ih]
        constructor
        · rintro ⟨i, h₁, h₂, hi⟩
          exact ⟨i, by omega, by omega, hi⟩
        · rintro ⟨i, h₁, h₂, hi⟩
          have : i ≠ start := by rintro rfl; exact hs hi
          exact ⟨i, by omega, by omega, hi⟩

theorem scanAny_zero_eq_true_iff (test : ℕ → Bool) (count : ℕ) :
    scanAny test count 0 = true ↔ ∃ i < count, test i = true := by
  simp [scanAny_eq_true_iff]

/-- Search a square grid, retaining only the current row and column counters. -/
def scanSquare (n : ℕ) (test : ℕ → ℕ → Bool) : Bool :=
  scanAny (fun i ↦ scanAny (test i) n 0) n 0

theorem scanSquare_eq_true_iff (n : ℕ) (test : ℕ → ℕ → Bool) :
    scanSquare n test = true ↔ ∃ i < n, ∃ j < n, test i j = true := by
  simp [scanSquare, scanAny_zero_eq_true_iff]

/-- The paper's coefficient criterion with the verified indexed Berkowitz evaluator. -/
theorem irreducible_iff_indexed_oracle_tests {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) :
    Irreducible f ↔
      indexedBerkowitzDeterminant (fun i j : Fin (f.natDegree + f.derivative.natDegree) ↦
        coefficientSylvesterEntry f i.val j.val) ≠ 0 ∧
      ∃ i j : Fin (f.natDegree - 1 + 1),
        indexedBerkowitzDeterminant ((positiveCoefficientFrobenius f hf - 1).submatrix
          i.succAbove j.succAbove) ≠ 0 := by
  let A : Matrix (Fin (f.natDegree + f.derivative.natDegree))
      (Fin (f.natDegree + f.derivative.natDegree)) K :=
    fun i j ↦ coefficientSylvesterEntry f i.val j.val
  have h := irreducible_iff_coefficient_oracle_tests f hf
  change Irreducible f ↔ determinantEntry A ≠ 0 ∧ _ at h
  change Irreducible f ↔ indexedBerkowitzDeterminant A ≠ 0 ∧ _
  simpa only [indexedBerkowitzDeterminant_eq_det, determinantEntry_eq_det] using h

/-- One deleted-row/deleted-column determinant request. Out-of-range addresses are
rejected; the search below only uses in-range addresses. -/
noncomputable def deletedMinorFlag {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : 0 < f.natDegree) (i j : ℕ) : Bool :=
  if hi : i < f.natDegree - 1 + 1 then
    if hj : j < f.natDegree - 1 + 1 then
      decide (indexedBerkowitzDeterminant ((positiveCoefficientFrobenius f hf - 1).submatrix
        (⟨i, hi⟩ : Fin _).succAbove (⟨j, hj⟩ : Fin _).succAbove) ≠ 0)
    else false
  else false

theorem deletedMinorFlag_eq_true_iff {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : 0 < f.natDegree) (i j : ℕ)
    (hi : i < f.natDegree - 1 + 1) (hj : j < f.natDegree - 1 + 1) :
    deletedMinorFlag f hf i j = true ↔
      indexedBerkowitzDeterminant ((positiveCoefficientFrobenius f hf - 1).submatrix
        (⟨i, hi⟩ : Fin _).succAbove (⟨j, hj⟩ : Fin _).succAbove) ≠ 0 := by
  simp [deletedMinorFlag, hi, hj]

noncomputable def searchDeletedMinor {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : 0 < f.natDegree) : Bool :=
  scanSquare (f.natDegree - 1 + 1) (deletedMinorFlag f hf)

theorem searchDeletedMinor_eq_true_iff {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : 0 < f.natDegree) :
    searchDeletedMinor f hf = true ↔ ∃ i j : Fin (f.natDegree - 1 + 1),
      indexedBerkowitzDeterminant ((positiveCoefficientFrobenius f hf - 1).submatrix
        i.succAbove j.succAbove) ≠ 0 := by
  rw [searchDeletedMinor, scanSquare_eq_true_iff]
  constructor
  · rintro ⟨i, hi, j, hj, h⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩, (deletedMinorFlag_eq_true_iff f hf i j hi hj).mp h⟩
  · rintro ⟨i, j, h⟩
    exact ⟨i.val, i.isLt, j.val, j.isLt,
      (deletedMinorFlag_eq_true_iff f hf i.val j.val i.isLt j.isLt).mpr h⟩

/-- The positive-degree test: a zero derivative or zero Sylvester determinant
rejects; otherwise the two-counter minor search decides acceptance. -/
noncomputable def positiveOracleDecision {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : 0 < f.natDegree) : Bool :=
  if f.derivative = 0 then false
  else if indexedBerkowitzDeterminant (fun i j : Fin (f.natDegree + f.derivative.natDegree) ↦
    coefficientSylvesterEntry f i.val j.val) = 0 then false
  else searchDeletedMinor f hf

theorem positiveOracleDecision_correct {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : 0 < f.natDegree) :
    positiveOracleDecision f hf = true ↔ Irreducible f := by
  unfold positiveOracleDecision
  split_ifs with hd hr
  · simp only [false_iff]
    exact not_irreducible_of_derivative_eq_zero f hf hd
  · rw [irreducible_iff_indexed_oracle_tests f hf]
    simp [hr]
  · rw [searchDeletedMinor_eq_true_iff, irreducible_iff_indexed_oracle_tests f hf]
    simp [hr]

/-- The complete input-polynomial test, including explicit monic normalization. -/
noncomputable def coefficientOracleDecision {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (f : K[X]) : Bool :=
  let g := monicRepresentative f
  if hg : 0 < g.natDegree then positiveOracleDecision g hg else false

theorem coefficientOracleDecision_correct {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (f : K[X]) :
    coefficientOracleDecision f = true ↔ Irreducible f := by
  rw [← monicRepresentative_irreducible_iff f]
  unfold coefficientOracleDecision
  dsimp only
  split_ifs with hg
  · exact positiveOracleDecision_correct _ hg
  · simp only [false_iff]
    exact fun hi ↦ hg hi.natDegree_pos

theorem coefficientOracleDecision_degree_zero {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (f : K[X]) (hf : f.natDegree = 0) :
    coefficientOracleDecision f = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have := ((coefficientOracleDecision_correct f).mp h).natDegree_pos
  omega

theorem coefficientOracleDecision_degree_one {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (f : K[X]) (hf : f.natDegree = 1) :
    coefficientOracleDecision f = true := by
  apply (coefficientOracleDecision_correct f).mpr
  apply Polynomial.irreducible_of_degree_eq_one
  have hf0 : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (show 0 < f.natDegree by omega)
  rw [Polynomial.degree_eq_natDegree hf0, hf]
  rfl

theorem coefficientOracleDecision_not_squarefree {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (f : K[X]) (hf : ¬Squarefree f) :
    coefficientOracleDecision f = false := by
  apply Bool.eq_false_iff.mpr
  exact fun h ↦ hf ((coefficientOracleDecision_correct f).mp h).squarefree

theorem coefficientOracleDecision_zero_derivative {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (f : K[X]) (hf : 0 < f.natDegree) (hd : f.derivative = 0) :
    coefficientOracleDecision f = false := by
  apply Bool.eq_false_iff.mpr
  exact fun h ↦ not_irreducible_of_derivative_eq_zero f hf hd
    ((coefficientOracleDecision_correct f).mp h)

/-- Trial division using one natural-number counter; no primality oracle is used. -/
def trialPrimeFlag (p : ℕ) : Bool :=
  if p < 2 then false else !(scanAny (fun d ↦ decide (p % d = 0)) (p - 2) 2)

theorem trialPrimeFlag_correct (p : ℕ) : trialPrimeFlag p = true ↔ p.Prime := by
  rw [Nat.prime_def_lt']
  unfold trialPrimeFlag
  split_ifs with hp
  · simp only [false_iff]
    omega
  · rw [Bool.not_eq_true', Bool.eq_false_iff]
    constructor
    · intro h
      refine ⟨by omega, ?_⟩
      intro d hd hdp hdvd
      apply h
      apply (scanAny_eq_true_iff _ _ _).mpr
      exact ⟨d, hd, by omega, by simpa [Nat.dvd_iff_mod_eq_zero] using hdvd⟩
    · rintro ⟨hp, h⟩ hs
      obtain ⟨d, hd, hdp, hdvd⟩ := (scanAny_eq_true_iff _ _ _).mp hs
      exact h d hd (by omega) (Nat.dvd_of_mod_eq_zero (of_decide_eq_true hdvd))

/-- Validate a field header using the same irreducibility test over the prime field.
The prime check precedes installation of the `ZMod p` field instance. -/
noncomputable def FieldCode.headerDecision (c : FieldCode) : Bool := by
  classical
  exact if hp : trialPrimeFlag c.characteristic = true then
    letI : Fact c.characteristic.Prime := ⟨(trialPrimeFlag_correct _).mp hp⟩
    decide (c.polynomial.Monic ∧ (∀ a ∈ c.modulus, a < c.characteristic) ∧
      c.modulus.getLast? = some 1) && coefficientOracleDecision c.polynomial
  else false

theorem FieldCode.headerDecision_correct (c : FieldCode) :
    c.headerDecision = true ↔ c.Valid := by
  classical
  by_cases hflag : trialPrimeFlag c.characteristic = true
  · have hp := (trialPrimeFlag_correct _).mp hflag
    have : Fact c.characteristic.Prime := ⟨hp⟩
    simp only [headerDecision, dite_eq_left hflag, Bool.and_eq_true, decide_eq_true_eq]
    rw [coefficientOracleDecision_correct]
    constructor
    · rintro ⟨⟨hm, hc, ht⟩, hi⟩
      exact ⟨hp, hm, hi, hc, ht⟩
    · intro h
      exact ⟨⟨h.monic, h.coefficients, h.trailing⟩, h.irreducible⟩
  · simp only [headerDecision, dite_eq_right hflag, Bool.false_eq_true, false_iff]
    exact fun h ↦ hflag ((trialPrimeFlag_correct _).mpr h.prime)

end SparseIrred.UpperBounds.Section4
