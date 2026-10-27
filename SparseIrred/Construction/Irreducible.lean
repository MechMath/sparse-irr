import SparseIrred.LargeGap.Verify
import SparseIrred.Sparse.Canonical

/-!
# ④ Irreducible and reducible branches in `ℤ[X]` (notes p. 8)

"The source theorem makes the noncyclotomic part of `H_M` irreducible; the root-of-unity argument
makes that part all of `H_M`.  Moreover the coefficient of `X^M` is `-1`, so `H_M` is primitive.
Thus `H_M` is irreducible in `ℤ[X]` by Gauss's lemma.  If `Φ` is satisfiable, (2) gives a
nonconstant common divisor of `A, B`, hence of `H_M`.  Its degree is at most `N < M + N = deg H_M`,
and primitivity again transfers the proper factorization to `ℤ[X]`."

In the satisfiable branch the common divisor is taken to be a cyclotomic polynomial `Φ_k` with
`k ∣ N`, which is monic in `ℤ[X]`, so the proper factorization is exhibited directly in `ℤ[X]`.
-/

open Polynomial

namespace SparseIrred

open Complexity.SAT

private theorem monic_Bpoly (Φ : CNF) : (Bpoly Φ).Monic := by
  have h := monic_X_pow_sub_C (1 : ℤ) (bigN_pos Φ).ne'
  rwa [map_one] at h

private theorem natDegree_Bpoly (Φ : CNF) : (Bpoly Φ).natDegree = bigN Φ := by
  unfold Bpoly
  rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [bigN_pos Φ]

private theorem monic_X_pow_mul_Bpoly (Φ : CNF) (M : ℕ) : (X ^ M * Bpoly Φ).Monic :=
  (monic_X_pow M).mul (monic_Bpoly Φ)

private theorem natDegree_X_pow_mul_Bpoly (Φ : CNF) (M : ℕ) :
    (X ^ M * Bpoly Φ).natDegree = M + bigN Φ := by
  rw [(monic_X_pow M).natDegree_mul (monic_Bpoly Φ), natDegree_X_pow, natDegree_Bpoly]

private theorem degree_Apoly_lt (Φ : CNF) {M : ℕ} (hM : (Apoly Φ).natDegree < M) :
    (Apoly Φ).degree < (X ^ M * Bpoly Φ).degree := by
  refine lt_of_le_of_lt degree_le_natDegree ?_
  rw [degree_eq_natDegree (monic_X_pow_mul_Bpoly Φ M).ne_zero, natDegree_X_pow_mul_Bpoly]
  exact_mod_cast (show (Apoly Φ).natDegree < M + bigN Φ by omega)

/-- For `M > deg A`, the coefficient of `X^M` in `H_M` is `-1`. -/
theorem Hpoly_coeff_M (Φ : CNF) {M : ℕ} (hM : (Apoly Φ).natDegree < M) :
    (Hpoly Φ M).coeff M = -1 := by
  unfold Hpoly
  rw [coeff_add, coeff_eq_zero_of_natDegree_lt hM, coeff_X_pow_mul', ite_eq_left_of_eq_true _ _
    (eq_true le_rfl), Nat.sub_self]
  simp [Bpoly, (bigN_pos Φ).ne]

/-- For `M > deg A`, `deg H_M = M + N`. -/
theorem natDegree_Hpoly (Φ : CNF) {M : ℕ} (hM : (Apoly Φ).natDegree < M) :
    (Hpoly Φ M).natDegree = M + bigN Φ := by
  unfold Hpoly
  rw [natDegree_add_eq_right_of_natDegree_lt, natDegree_X_pow_mul_Bpoly]
  rw [natDegree_X_pow_mul_Bpoly]
  omega

/-- For `M > deg A`, `H_M` is monic (its leading term is that of `X^M B`). -/
theorem monic_Hpoly (Φ : CNF) {M : ℕ} (hM : (Apoly Φ).natDegree < M) : (Hpoly Φ M).Monic :=
  (monic_X_pow_mul_Bpoly Φ M).add_of_right (degree_Apoly_lt Φ hM)

/-- For `M > deg A`, `H_M` is primitive. -/
theorem isPrimitive_Hpoly (Φ : CNF) {M : ℕ} (hM : (Apoly Φ).natDegree < M) :
    (Hpoly Φ M).IsPrimitive :=
  (monic_Hpoly Φ hM).isPrimitive

/-- `deg H_M = M + N` for `M = Mval Φ`. -/
theorem natDegree_Hfinal (Φ : CNF) : (Hfinal Φ).natDegree = Mval Φ + bigN Φ :=
  natDegree_Hpoly Φ (natDegree_Apoly_lt_Mval Φ)

/-- `H_M` has positive degree. -/
theorem natDegree_Hfinal_pos (Φ : CNF) : 0 < (Hfinal Φ).natDegree := by
  rw [natDegree_Hfinal]
  have := bigN_pos Φ
  omega

/-- `H_M` is primitive. -/
theorem isPrimitive_Hfinal (Φ : CNF) : (Hfinal Φ).IsPrimitive :=
  isPrimitive_Hpoly Φ (natDegree_Apoly_lt_Mval Φ)

/-- If a primitive `k`-th root of unity is a root of `A`, then `Φ_k` divides `A` in `ℤ[X]`. -/
private theorem cyclotomic_dvd_of_aeval_eq_zero {k : ℕ} (hk : 0 < k) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ k) (A : ℤ[X]) (hA : aeval ζ A = 0) : cyclotomic k ℤ ∣ A := by
  rw [cyclotomic_eq_minpoly hζ hk]
  exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hk) hA

/-- Satisfiable branch: a cyclotomic common factor of `A` and `B`. -/
theorem exists_cyclotomic_dvd_of_satisfiable (Φ : CNF) (hsat : Φ.Satisfiable) :
    ∃ k, 0 < k ∧ k ∣ bigN Φ ∧ cyclotomic k ℤ ∣ Apoly Φ ∧ cyclotomic k ℤ ∣ Bpoly Φ := by
  obtain ⟨ζ, hA, hB⟩ := (satisfiable_iff_exists_common_root Φ).1 hsat
  have hN : ζ ^ bigN Φ = 1 := by simpa [Bpoly, sub_eq_zero] using hB
  have hk : 0 < orderOf ζ :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨bigN Φ, bigN_pos Φ, hN⟩)
  have hζ : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
  exact ⟨orderOf ζ, hk, orderOf_dvd_of_pow_eq_one hN,
    cyclotomic_dvd_of_aeval_eq_zero hk hζ _ hA, cyclotomic_dvd_of_aeval_eq_zero hk hζ _ hB⟩

/-- A common divisor of `A` and `B` divides every `H_M`. -/
private theorem dvd_Hpoly_of_dvd (Φ : CNF) {p : ℤ[X]} (hA : p ∣ Apoly Φ) (hB : p ∣ Bpoly Φ)
    (M : ℕ) : p ∣ Hpoly Φ M :=
  dvd_add hA (dvd_mul_of_dvd_right hB _)

/-- Satisfiable branch: a proper factorization of `H_M` in `ℤ[X]`, with a factor of strictly
positive degree smaller than `deg H_M`. -/
theorem Hfinal_factorization_of_satisfiable (Φ : CNF) (hsat : Φ.Satisfiable) :
    ∃ k, 0 < k ∧ k ∣ bigN Φ ∧ ∃ g : ℤ[X], Hfinal Φ = cyclotomic k ℤ * g ∧
      0 < (cyclotomic k ℤ).natDegree ∧ (cyclotomic k ℤ).natDegree < (Hfinal Φ).natDegree ∧
      0 < g.natDegree := by
  obtain ⟨k, hk, hkN, hA, hB⟩ := exists_cyclotomic_dvd_of_satisfiable Φ hsat
  have hH : cyclotomic k ℤ ∣ Hfinal Φ := by
    unfold Hfinal
    exact dvd_Hpoly_of_dvd Φ hA hB _
  obtain ⟨g, hg⟩ := hH
  have hMA := natDegree_Apoly_lt_Mval Φ
  have hdeg := natDegree_Hfinal Φ
  have hcyc : (cyclotomic k ℤ).natDegree = k.totient := natDegree_cyclotomic k ℤ
  have htot_pos : 0 < k.totient := Nat.totient_pos.2 hk
  have htot_le : k.totient ≤ k := Nat.totient_le k
  have hkle : k ≤ bigN Φ := Nat.le_of_dvd (bigN_pos Φ) hkN
  have hH0 : Hfinal Φ ≠ 0 := (monic_Hpoly Φ hMA).ne_zero
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hg
    exact hH0 hg
  have hmul : (Hfinal Φ).natDegree = (cyclotomic k ℤ).natDegree + g.natDegree := by
    rw [hg, natDegree_mul (cyclotomic_ne_zero k ℤ) hg0]
  refine ⟨k, hk, hkN, g, hg, ?_, ?_, ?_⟩
  · rw [hcyc]; exact htot_pos
  · rw [hcyc, hdeg]; omega
  · omega

/-- Satisfiable branch: `H_M` is reducible in `ℤ[X]`. -/
theorem Hfinal_reducible_of_satisfiable (Φ : CNF) (hsat : Φ.Satisfiable) :
    Reducible (Hfinal Φ) := by
  obtain ⟨k, -, -, g, hg, hc, -, hg0⟩ := Hfinal_factorization_of_satisfiable Φ hsat
  exact ⟨(monic_Hpoly Φ (natDegree_Apoly_lt_Mval Φ)).ne_zero, cyclotomic k ℤ, g,
    not_isUnit_of_natDegree_pos _ hc, not_isUnit_of_natDegree_pos _ hg0, hg⟩

/-- Satisfiable branch: `H_M` is not irreducible in `ℤ[X]`. -/
theorem Hfinal_not_irreducible_of_satisfiable (Φ : CNF) (hsat : Φ.Satisfiable) :
    ¬Irreducible (Hfinal Φ) :=
  ((reducible_iff _).1 (Hfinal_reducible_of_satisfiable Φ hsat)).2.2

/-- Unsatisfiable branch: `H_M` is irreducible in `ℤ[X]`, assuming the large-gap theorem
(`SSSLargeGap`, an explicit hypothesis) and using Gauss's lemma. -/
theorem Hfinal_irreducible_of_SSS (hSSS : SSSLargeGap) (Φ : CNF) (hΦ : Φ ≠ [])
    (hunsat : ¬Φ.Satisfiable) : Irreducible (Hfinal Φ) := by
  have hnc := noncyclotomicPartIrreducible_Hfinal hSSS Φ hΦ hunsat
  have hQ : Irreducible ((Hfinal Φ).map (Int.castRingHom ℚ)) := by
    refine hnc 0 _ (by simp) (by simp) ?_
    intro n hn
    exact not_cyclotomic_dvd_Hpoly Φ (Mval Φ) hunsat hn
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (isPrimitive_Hfinal Φ)).2 hQ

/-- The correctness of the construction, conditional on the large-gap theorem: for a nonempty
formula `Φ`, `H_M` is irreducible in `ℤ[X]` iff `Φ` is unsatisfiable. -/
theorem Hfinal_irreducible_iff_of_SSS (hSSS : SSSLargeGap) (Φ : CNF) (hΦ : Φ ≠ []) :
    Irreducible (Hfinal Φ) ↔ ¬Φ.Satisfiable :=
  ⟨fun hi hsat => Hfinal_not_irreducible_of_satisfiable Φ hsat hi,
    Hfinal_irreducible_of_SSS hSSS Φ hΦ⟩

end SparseIrred
