import SparseIrred.Theorem8
import SparseIrred.Machine.Bounds
import Complexitylib.Models.TuringMachine.OutputBounds

/-!
# Sparse polynomial irreducibility: algebraic criteria and complexity hardness

This module collects the unconditional hardness of sparse integer polynomial irreducibility
and its supporting algebraic statements. The gap criterion uses coprimality over `ℚ[X]` and
the reciprocal polynomial `reverse`. The module also records the simultaneous-approximation
modulus, prime bounds, and polynomial bounds on reduction time and output length.

See `docs/IRREDUCIBILITY_AUDIT.md` for the correspondence with the paper's numbered results.
-/

open Polynomial Complexity

namespace SparseIrred.Irreducibility

/-- Lemma 3, including its assertion for every gap `M`, with no size assumption. -/
theorem satisfiability_encoding (Φ : SAT.CNF) (hΦ : Φ ≠ []) :
    Spoly Φ ≠ 0 ∧ (Apoly Φ).coeff 0 ≠ 0 ∧
      (Apoly Φ).natDegree = 2 * Dexp Φ ∧ (Apoly Φ).reverse = Apoly Φ ∧
      (Φ.Satisfiable ↔
        ¬IsCoprime ((Apoly Φ).map (Int.castRingHom ℚ))
          ((Bpoly Φ).map (Int.castRingHom ℚ))) ∧
      (∀ M : ℕ, (∃ z : ℂ, (∃ n, 0 < n ∧ z ^ n = 1) ∧
        aeval z (Hpoly Φ M) = 0) ↔ Φ.Satisfiable) :=
  ⟨Spoly_ne_zero Φ hΦ, Apoly_coeff_zero_ne_zero Φ hΦ, natDegree_Apoly Φ hΦ,
    reverse_Apoly Φ, satisfiable_iff_not_isCoprime Φ, exists_rootOfUnity_root_iff Φ⟩

/-- The rational coprimality hypothesis of Theorem 4 implies relative primality over
`ℤ[X]`: the constant coefficient `-1` of `X^N - 1` also excludes integer factors. -/
theorem isRelPrime_of_rational_coprime {A : ℤ[X]} {N : ℕ} (hN : 0 < N)
    (hAB : IsCoprime (A.map (Int.castRingHom ℚ))
      ((X ^ N - 1 : ℤ[X]).map (Int.castRingHom ℚ))) :
    IsRelPrime A (X ^ N - 1) := by
  intro g hgA hgB
  have hu : IsUnit (g.map (Int.castRingHom ℚ)) :=
    hAB.isRelPrime (Polynomial.map_dvd _ hgA) (Polynomial.map_dvd _ hgB)
  have hd : g.natDegree = 0 := by
    have := natDegree_eq_zero_of_isUnit hu
    rwa [natDegree_map_eq_of_injective (RingHom.injective_int _)] at this
  rw [eq_C_of_natDegree_eq_zero hd] at hgB ⊢
  apply Polynomial.isUnit_C.2
  have hc := (C_dvd_iff_dvd_coeff _ _).1 hgB 0
  have hB0 : (X ^ N - 1 : ℤ[X]).coeff 0 = -1 := by
    simp [coeff_X_pow, hN.ne]
  rw [hB0] at hc
  exact isUnit_of_dvd_unit hc (by simp)

private theorem mirror_eq_reverse_of_coeff_zero_ne_zero {f : ℤ[X]} (hf : f.coeff 0 ≠ 0) :
    f.mirror = f.reverse := by
  rw [mirror, natTrailingDegree_eq_zero.mpr (Or.inr hf), pow_zero, mul_one]

/-- Theorem 4, equation (2), with the paper's `P* = reverse P` for arbitrary `K`.
The nonzero constant term of `K` is a consequence, rather than an extra hypothesis. -/
theorem ljunggren_gapPoly {A : ℤ[X]} {N M : ℕ}
    (hA0 : A.coeff 0 ≠ 0) (hA : A.reverse = A) (hN : 0 < N)
    (hAB : IsCoprime (A.map (Int.castRingHom ℚ))
      ((X ^ N - 1 : ℤ[X]).map (Int.castRingHom ℚ)))
    (hM : FFK.FFKThreshold A N M) (K : ℤ[X])
    (hK : FFK.gapPoly A N M * (FFK.gapPoly A N M).reverse = K * K.reverse) :
    K = FFK.gapPoly A N M ∨ K = -FFK.gapPoly A N M ∨
      K = (FFK.gapPoly A N M).reverse ∨ K = -(FFK.gapPoly A N M).reverse := by
  have hM' := FFK.natDegree_lt_of_FFKThreshold hM
  have hF0 : (FFK.gapPoly A N M).coeff 0 ≠ 0 := by
    rwa [FFK.coeff_zero_gapPoly (by omega)]
  have hF := mirror_eq_reverse_of_coeff_zero_ne_zero hF0
  have hprod := congrArg (fun p : ℤ[X] => p.coeff 0) hK
  simp only [mul_coeff_zero, coeff_zero_reverse] at hprod
  have hK0 : K.coeff 0 ≠ 0 := by
    intro hz
    rw [hz, zero_mul, (FFK.monic_gapPoly hM' hN).leadingCoeff, mul_one] at hprod
    exact hF0 hprod
  have hKm := mirror_eq_reverse_of_coeff_zero_ne_zero hK0
  have result := FFK.ljunggren_gapPoly hA hA0 hN
    (isRelPrime_of_rational_coprime hN hAB) hM K (by rwa [hF, hKm])
  rwa [hF] at result

/-- Theorem 4, the irreducibility conclusion with exactly the paper's coprimality
and root-of-unity hypotheses. `FFKThreshold` is the numerical inequality (G1). -/
theorem irreducible_gapPoly {A : ℤ[X]} {N M : ℕ}
    (hA0 : A.coeff 0 ≠ 0) (hA : A.reverse = A) (hN : 0 < N)
    (hAB : IsCoprime (A.map (Int.castRingHom ℚ))
      ((X ^ N - 1 : ℤ[X]).map (Int.castRingHom ℚ)))
    (hM : FFK.FFKThreshold A N M)
    (hroot : ∀ z : ℂ, (∃ n, 0 < n ∧ z ^ n = 1) →
      aeval z (FFK.gapPoly A N M) ≠ 0) :
    Irreducible (FFK.gapPoly A N M) :=
  FFK.irreducible_gapPoly hA hA0 hN (isRelPrime_of_rational_coprime hN hAB) hM hroot

set_option maxHeartbeats 800000 in
/-- Lemma 5 with the paper's strict inequalities and unique integer quotient.
Here `L = M + N` in the application and `m ≥ 1` follows from `N ≥ 1`.
The size hypothesis on `L` follows immediately from (G1). -/
theorem exists_shifted_residue_modulus (T : Finset ℕ) (L m s₀ : ℕ) (hm : 1 ≤ m)
    (hT : T.Nonempty) (hTL : ∀ t ∈ T, t ≤ L) (hs : T.card ≤ s₀)
    (hL : (10 + 2 * m) * 64 ^ s₀ ≤ L) :
    ∃ d κ : ℕ, 1 ≤ d ∧ d ≤ 8 ^ T.card ∧ κ = L / d ∧ 2 * m < κ ∧
      ∀ t ∈ T, ∃! q : ℤ,
        0 < (t : ℤ) + (κ / 4 : ℕ) - q * κ ∧
          2 * ((t : ℤ) + (κ / 4 : ℕ) - q * κ) < κ := by
  set R := 8 ^ T.card with hRdef
  have hR : 8 ≤ R := by
    have hc : 1 ≤ T.card := Finset.card_pos.mpr hT
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (8 : ℕ)) hc
  have h64 : 64 ^ T.card = R * R := by
    rw [hRdef, ← mul_pow]
    norm_num
  have hbound : (10 + 2 * m) * (R * R) ≤ L := by
    rw [← h64]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hs)).trans hL
  have hLpos : 0 < L := by nlinarith
  obtain ⟨d, hd1, hdR, happrox⟩ := FFK.exists_simultaneous_approx T hLpos
  have hdpos : 0 < d := by omega
  set κ := L / d with hκdef
  have hκR : (10 + 2 * m) * R ≤ κ := by
    apply (Nat.le_div_iff_mul_le hdpos).2
    exact (Nat.mul_le_mul_left ((10 + 2 * m) * R) hdR).trans
      (by simpa [mul_assoc] using hbound)
  have hκd : 12 * d ≤ κ := by nlinarith
  have hκm : 2 * m < κ := by nlinarith
  refine ⟨d, κ, hd1, hdR, rfl, hκm, fun t ht => ?_⟩
  obtain ⟨q, hq⟩ := happrox t ht
  set ρ := L % d with hρdef
  set δ : ℤ := (d : ℤ) * t - q * L with hδdef
  have hdiv : (d : ℤ) * κ + ρ = L := by exact_mod_cast Nat.div_add_mod L d
  have hρd : (ρ : ℤ) + 1 ≤ d := by exact_mod_cast Nat.mod_lt L hdpos
  have hρ0 : (0 : ℤ) ≤ ρ := by positivity
  have hd1Z : (1 : ℤ) ≤ d := by exact_mod_cast hd1
  have hdposZ : (0 : ℤ) < d := by exact_mod_cast hdpos
  have hLposZ : (0 : ℤ) < L := by exact_mod_cast hLpos
  have htL : (t : ℤ) ≤ L := by exact_mod_cast hTL t ht
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have hδlo : -(L : ℤ) < 8 * δ := by have := neg_abs_le δ; linarith
  have hδhi : 8 * δ < L := by have := le_abs_self δ; linarith
  have hq0 : 0 ≤ q := by
    by_contra hn
    have hqL : q * (L : ℤ) ≤ -L := by nlinarith
    have hdt : (0 : ℤ) ≤ d * t := by positivity
    linarith
  have hqd : q ≤ d := by
    by_contra hn
    have hqL : ((d : ℤ) + 1) * L ≤ q * L := by nlinarith
    have hdt : (d : ℤ) * t ≤ d * L := mul_le_mul_of_nonneg_left htL hdposZ.le
    linarith
  have hqρ0 : 0 ≤ q * (ρ : ℤ) := mul_nonneg hq0 hρ0
  have hqρ : q * (ρ : ℤ) ≤ (d : ℤ) ^ 2 - d := by nlinarith
  have hκdZ : 12 * (d : ℤ) ≤ κ := by exact_mod_cast hκd
  have hdκ : 12 * (d : ℤ) ^ 2 ≤ (d : ℤ) * κ := by
    nlinarith [mul_le_mul_of_nonneg_left hκdZ hdposZ.le]
  set h := κ / 4 with hhdef
  have hhlo : 4 * (h : ℤ) ≤ κ := by
    exact_mod_cast (show 4 * h ≤ κ by omega)
  have hhhi : (κ : ℤ) ≤ 4 * h + 3 := by omega
  have hdhlo := mul_le_mul_of_nonneg_left hhlo hdposZ.le
  have hdhhi := mul_le_mul_of_nonneg_left hhhi hdposZ.le
  set u : ℤ := (t : ℤ) - q * κ with hudef
  have hkey : (d : ℤ) * u = δ + q * ρ := by
    rw [hudef, hδdef, ← hdiv]
    ring
  clear_value δ u h κ ρ R
  have hdsq : (d : ℤ) ≤ (d : ℤ) ^ 2 := by
    nlinarith only [hd1Z, sq_nonneg ((d : ℤ) - 1)]
  have hu0 : -(h : ℤ) < u := by
    have hmul : (d : ℤ) * (-h) < d * u := by
      nlinarith only [hd1Z, hρd, hqρ0, hδlo, hdiv, hkey, hdhhi, hdκ, hdsq]
    exact lt_of_mul_lt_mul_left hmul hdposZ.le
  have huκ : 2 * (u + h) < κ := by
    have hmul : (d : ℤ) * (2 * (u + h)) < d * κ := by
      nlinarith only [hd1Z, hρd, hqρ, hδhi, hdiv, hkey, hdhlo, hdκ, hdsq]
    exact lt_of_mul_lt_mul_left hmul hdposZ.le
  have hres : 0 < (t : ℤ) + h - q * κ ∧
      2 * ((t : ℤ) + h - q * κ) < κ := by
    rw [hudef] at hu0 huκ
    constructor <;> linarith only [hu0, huκ]
  refine ⟨q, hres, fun q' hq' => ?_⟩
  have hκpos : (0 : ℤ) < κ := by exact_mod_cast (show 0 < κ by omega)
  rcases lt_trichotomy q' q with hlt | heq | hgt
  · have hmul : (q' + 1) * (κ : ℤ) ≤ q * κ :=
      mul_le_mul_of_nonneg_right (by omega) hκpos.le
    nlinarith only [hκpos, hmul, hres.1, hres.2, hq'.1, hq'.2]
  · exact heq
  · have hmul : (q + 1) * (κ : ℤ) ≤ q' * κ :=
      mul_le_mul_of_nonneg_right (by omega) hκpos.le
    nlinarith only [hκpos, hmul, hres.1, hres.2, hq'.1, hq'.2]

/-- Lemma 6, the complete pair of inequalities (PB1), also at `x = 0`. -/
theorem lcm_primeCounting_bounds (x : ℕ) :
    2 ^ x ≤ (x + 1) * Nat.lcmUpto x ∧
      (x + 1) * Nat.lcmUpto x ≤ (x + 1) * x ^ Nat.primeCounting x := by
  refine ⟨Chebyshev.two_pow_le_mul_lcmUpto x, ?_⟩
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · norm_num [Nat.lcmUpto]
  · gcongr
    rw [Nat.lcmUpto_eq_prod_pow_log, ← Nat.primesLE_card_eq_primeCounting]
    exact Finset.prod_le_pow_card _ _ _ fun p _ => Nat.pow_log_le_self p hx.ne'

/-- Lemma 6, the zero-indexed prime bounds. -/
theorem prime_index_bounds :
    (∀ k : ℕ, Nat.nth Nat.Prime k ≤ 64 * (k + 1) ^ 2) ∧
      (∀ i : ℕ, oddPrime i ≤ 64 * (i + 2) ^ 2) :=
  ⟨Machine.nth_prime_le, Machine.oddPrime_le⟩

/-- Lemma 7: one deterministic machine and one natural-coefficient polynomial
bound both its running time and the canonical output's binary length, on all inputs.
On the main branch the output is exactly `encPoly (Hfinal Φ)`, and (5) satisfies (G1). -/
theorem polynomial_time_sparse_reduction :
    ∃ (k : ℕ) (tm : TM k) (p : ℕ[X]),
      tm.ComputesInTime reduce p.eval ∧
      (∀ x, (encPoly (reducePoly x)).length ≤ p.eval x.length) ∧
      (∀ Φ : SAT.CNF, Φ.Is3CNF → Φ ≠ [] →
        reduce Φ.encode = encPoly (Hfinal Φ) ∧
          (encPoly (Hfinal Φ)).length ≤ p.eval Φ.encode.length) ∧
      (∀ Φ : SAT.CNF, FFK.FFKThreshold (Apoly Φ) (bigN Φ) (Mval Φ)) := by
  obtain ⟨k, tm, p, hp⟩ := mem_FP_iff_computesInTime_polynomial.1 reduce_mem_FP
  refine ⟨k, tm, p, hp, hp.output_length_le, ?_, FFK.FFKThreshold_Mval⟩
  intro Φ h3 hΦ
  have he : reduce Φ.encode = encPoly (Hfinal Φ) := by
    simp [reduce, reducePoly, SAT.CNF.decode3?_encode h3, hΦ,
      Machine.numVars_ne_zero_of_is3CNF h3 hΦ]
  exact ⟨he, he ▸ hp.output_length_le Φ.encode⟩

/-- Theorem 2: all four complexity conclusions, without an SSS hypothesis. -/
theorem irreducibility_hardness :
    coNPHard IrredLang ∧ NPHard RedLang ∧
      (∀ L ∈ NP, OneQueryReducesPoly L IrredLang) ∧
      (IrredLang ∈ P → P = NP) :=
  ⟨irreducibility_coNPHard, reducibility_NPHard, irreducibility_NPHard_oneQuery,
    P_eq_NP_of_irreducibility_mem_P⟩

end SparseIrred.Irreducibility
