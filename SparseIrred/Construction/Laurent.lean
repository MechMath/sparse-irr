import SparseIrred.Construction.Defs

/-!
# Basic facts on the construction: primes, `S`, `D`, and `A = 3 X^D S`

Notes p. 7: "These definitions are valid because `S ≠ 0`: at `X = -1`, each `m_i, q_i` is odd, so
`P⁺_i(-1) = -2` and `P⁻_i(-1) = 1`, whence `S(-1) = ∑_j C_j(-1)^2 > 0`.  Since `S(X⁻¹) = S(X)`, its
coefficients at `-D, D` agree and are nonzero.  Thus `A ∈ ℤ[X]` and `A(0) ≠ 0`."
-/

open Polynomial LaurentPolynomial

namespace SparseIrred

open Complexity.SAT

/-! ### Primes -/

/-- `q_i` is prime. -/
theorem oddPrime_prime (i : ℕ) : (oddPrime i).Prime := Nat.prime_nth_prime (i + 1)

/-- `q_i` is odd. -/
theorem oddPrime_odd (i : ℕ) : Odd (oddPrime i) := by
  apply (oddPrime_prime i).odd_of_ne_two
  intro h
  have := Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 0 < i + 1 by omega)
  rw [← oddPrime, h, Nat.nth_prime_zero_eq_two] at this
  exact lt_irrefl _ this

/-- `q_i ≥ 3`. -/
theorem three_le_oddPrime (i : ℕ) : 3 ≤ oddPrime i := by
  have h := Nat.nth_monotone Nat.infinite_setOfPred_prime (show 1 ≤ i + 1 by omega)
  rw [Nat.nth_prime_one_eq_three] at h
  exact h

/-- `i ↦ q_i` is strictly increasing. -/
theorem oddPrime_strictMono : StrictMono oddPrime := fun i j hij =>
  Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega : i + 1 < j + 1)

/-- Distinct `q_i` are coprime. -/
theorem oddPrime_coprime {i j : ℕ} (hij : i ≠ j) : Nat.Coprime (oddPrime i) (oddPrime j) :=
  (Nat.coprime_primes (oddPrime_prime i) (oddPrime_prime j)).2
    (oddPrime_strictMono.injective.ne hij)

/-- `N > 0`. -/
theorem bigN_pos (Φ : CNF) : 0 < bigN Φ :=
  Finset.prod_pos fun i _ => (oddPrime_prime i).pos

/-- `N` is odd. -/
theorem bigN_odd (Φ : CNF) : Odd (bigN Φ) :=
  Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun i _ => oddPrime_odd i

/-- `m_i q_i = N` for `i < n`. -/
theorem mExp_mul_oddPrime (Φ : CNF) {i : ℕ} (hi : i < numVars Φ) :
    mExp Φ i * oddPrime i = bigN Φ :=
  Nat.div_mul_cancel (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi))

/-- `m_i` is odd for `i < n`. -/
theorem mExp_odd (Φ : CNF) {i : ℕ} (hi : i < numVars Φ) : Odd (mExp Φ i) := by
  have h := bigN_odd Φ
  rw [← mExp_mul_oddPrime Φ hi] at h
  exact (Nat.odd_mul.1 h).1

/-- `varIdx Φ v` is `Nat.count (Occurs Φ) v`. -/
private theorem varIdx_eq_count (Φ : CNF) (v : ℕ) : varIdx Φ v = Nat.count (Occurs Φ) v := by
  rw [varIdx, Nat.count, List.countP_eq_length_filter]

/-- `numVars Φ` is `Nat.count (Occurs Φ) (Φ.maxVar + 1)`. -/
private theorem numVars_eq_count (Φ : CNF) :
    numVars Φ = Nat.count (Occurs Φ) (Φ.maxVar + 1) := by
  rw [numVars, varList, Nat.count, List.countP_eq_length_filter]

/-- An occurring variable is at most `Φ.maxVar`. -/
theorem Occurs.le_maxVar {Φ : CNF} {v : ℕ} (hv : Occurs Φ v) : v ≤ Φ.maxVar := by
  obtain ⟨c, hc, l, hl, rfl⟩ := hv
  exact le_trans (Clause.var_le_maxVar hl) (CNF.clause_maxVar_le_maxVar hc)

/-- The index of an occurring variable is less than `n`. -/
theorem varIdx_lt_numVars (Φ : CNF) {v : ℕ} (hv : Occurs Φ v) : varIdx Φ v < numVars Φ := by
  rw [varIdx_eq_count, numVars_eq_count]
  exact Nat.count_strict_mono hv (Nat.lt_succ_of_le hv.le_maxVar)

/-- Distinct occurring variables have distinct indices. -/
theorem varIdx_injOn (Φ : CNF) {u v : ℕ} (hu : Occurs Φ u) (hv : Occurs Φ v)
    (h : varIdx Φ u = varIdx Φ v) : u = v := by
  rw [varIdx_eq_count, varIdx_eq_count] at h
  exact Nat.count_injective hu hv h

/-! ### Laurent polynomial helpers -/

/-- Nonnegative coefficients of `toLaurent p`. -/
private theorem toLaurent_coeff_natCast {R : Type*} [Semiring R] (p : R[X]) (k : ℕ) :
    (toLaurent p).coeff (k : ℤ) = p.coeff k := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.cast_injective _ k

/-- Negative coefficients of `toLaurent p` vanish. -/
private theorem toLaurent_coeff_of_neg {R : Type*} [Semiring R] (p : R[X]) {k : ℤ} (hk : k < 0) :
    (toLaurent p).coeff k = 0 := by
  rw [coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨n, rfl⟩
  simp at hk
  omega

/-- Coefficients of `trunc f`. -/
private theorem trunc_coeff {R : Type*} [Semiring R] (f : R[T;T⁻¹]) (k : ℕ) :
    (trunc f).coeff k = f.coeff (k : ℤ) := rfl

/-- A Laurent polynomial without negative exponents is recovered from its truncation. -/
private theorem toLaurent_trunc_of_coeff_neg {R : Type*} [Semiring R] {f : R[T;T⁻¹]}
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0) : toLaurent (trunc f) = f := by
  ext k
  rcases lt_or_ge k 0 with hk | hk
  · rw [toLaurent_coeff_of_neg _ hk, hf k hk]
  · lift k to ℕ using hk
    rw [toLaurent_coeff_natCast, trunc_coeff]

/-- Evaluating `f(X⁻¹)` at `x` is evaluating `f` at `x⁻¹`. -/
theorem eval₂_invert {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : Sˣ)
    (p : R[T;T⁻¹]) : LaurentPolynomial.eval₂ f x (invert p) = LaurentPolynomial.eval₂ f x⁻¹ p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T n a => simp [zpow_neg]

/-- Laurent evaluation of an ordinary integer polynomial at a unit is `aeval`. -/
theorem eval₂_toLaurent_int {K : Type*} [CommRing K] (p : ℤ[X]) (u : Kˣ) :
    LaurentPolynomial.eval₂ (Int.castRingHom K) u (toLaurent p) = aeval (u : K) p := by
  rw [eval₂_toLaurent, aeval_def, algebraMap_int_eq]

/-- Coefficients of `3 T^D f`. -/
private theorem coeff_three_mul_T_mul (D : ℤ) (f : ℤ[T;T⁻¹]) (k : ℤ) :
    ((3 : ℤ[T;T⁻¹]) * T D * f).coeff k = 3 * f.coeff (k - D) := by
  have h : (3 : ℤ[T;T⁻¹]) * T D * f = f * AddMonoidAlgebra.single D 3 := by
    rw [single_eq_C_mul_T, map_ofNat LaurentPolynomial.C 3]
    ring
  rw [h, AddMonoidAlgebra.coeff_mul_single_apply, sub_eq_add_neg, mul_comm]

/-! ### `S` is nonzero and symmetric -/

/-- `S(-1) = ∑_j C_j(-1)^2`. -/
theorem evalS_neg_one (Φ : CNF) :
    evalS Φ (-1 : ℤˣ) = (Φ.map fun c => (clausePoly Φ c).eval (-1) ^ 2).sum := by
  rw [evalS, Spoly, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply, map_mul, eval₂_invert, eval₂_toLaurent, inv_neg, inv_one,
    Units.val_neg, Units.val_one, Int.castRingHom_int, eval₂_id, sq]

/-- A literal polynomial of an occurring variable does not vanish at `-1`. -/
private theorem litPoly_eval_neg_one_ne_zero (Φ : CNF) {l : Lit} (hl : Occurs Φ l.var) :
    (litPoly Φ l).eval (-1) ≠ 0 := by
  have hi := varIdx_lt_numVars Φ hl
  have hm := mExp_odd Φ hi
  have hq := oddPrime_odd (varIdx Φ l.var)
  unfold litPoly
  split
  · simp [posLitPoly, hm.neg_one_pow]
  · simp only [negLitPoly, eval_finsetSum, eval_pow, eval_X]
    simp_rw [pow_mul', hm.neg_one_pow]
    rw [neg_one_geom_sum]
    simp [Nat.not_even_iff_odd.2 hq]

/-- `C_j(-1) ≠ 0` for every clause of `Φ`. -/
theorem clausePoly_eval_neg_one_ne_zero (Φ : CNF) {c : Clause} (hc : c ∈ Φ) :
    (clausePoly Φ c).eval (-1) ≠ 0 := by
  rw [clausePoly, eval_list_prod, List.map_map]
  apply List.prod_ne_zero
  intro h
  obtain ⟨l, hl, h0⟩ := List.mem_map.1 h
  exact litPoly_eval_neg_one_ne_zero Φ ⟨c, hc, l, hl, rfl⟩ h0

/-- `S(-1) > 0` for a nonempty formula. -/
theorem evalS_neg_one_pos (Φ : CNF) (hΦ : Φ ≠ []) : 0 < evalS Φ (-1 : ℤˣ) := by
  rw [evalS_neg_one]
  apply List.sum_pos
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    exact sq_pos_iff.2 (clausePoly_eval_neg_one_ne_zero Φ hc)
  · simpa using hΦ

/-- `S ≠ 0` for a nonempty formula. -/
theorem Spoly_ne_zero (Φ : CNF) (hΦ : Φ ≠ []) : Spoly Φ ≠ 0 := by
  intro h
  have := evalS_neg_one_pos Φ hΦ
  rw [evalS, h, map_zero] at this
  exact lt_irrefl _ this

/-- `S(X⁻¹) = S(X)`. -/
theorem invert_Spoly (Φ : CNF) : invert (Spoly Φ) = Spoly Φ := by
  rw [Spoly, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply, map_mul]
  rw [involutive_invert, mul_comm]

/-- The coefficients of `S` at `-e` and `e` agree. -/
theorem Spoly_coeff_neg (Φ : CNF) (e : ℤ) : (Spoly Φ).coeff (-e) = (Spoly Φ).coeff e := by
  conv_rhs => rw [← invert_Spoly]
  rw [invert_apply]

/-- `[X^e] S = 0` for `|e| > D`. -/
theorem Spoly_coeff_eq_zero_of_lt (Φ : CNF) {e : ℤ} (he : (Dexp Φ : ℤ) < |e|) :
    (Spoly Φ).coeff e = 0 := by
  by_contra h
  have hmem : e ∈ (Spoly Φ).coeff.support := Finsupp.mem_support_iff.2 h
  have hle : e.natAbs ≤ Dexp Φ := Finset.le_sup (f := Int.natAbs) hmem
  rw [← Int.natCast_natAbs] at he
  omega

/-- For a nonempty formula, the coefficients of `S` at `D` and `-D` are nonzero. -/
theorem Spoly_coeff_Dexp_ne_zero (Φ : CNF) (hΦ : Φ ≠ []) :
    (Spoly Φ).coeff (Dexp Φ : ℤ) ≠ 0 ∧ (Spoly Φ).coeff (-(Dexp Φ : ℤ)) ≠ 0 := by
  have hne : (Spoly Φ).coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    apply Spoly_ne_zero Φ hΦ
    ext a
    rw [h]
    rfl
  obtain ⟨e, he, hD⟩ := Finset.exists_mem_eq_sup _ hne Int.natAbs
  rw [Finsupp.mem_support_iff] at he
  have hDe : (Dexp Φ : ℤ) = |e| := by
    rw [Dexp, hD, Int.natCast_natAbs]
  have key : (Spoly Φ).coeff (Dexp Φ : ℤ) ≠ 0 := by
    rw [hDe]
    rcases abs_choice e with h | h
    · rw [h]; exact he
    · rw [h, Spoly_coeff_neg]; exact he
  exact ⟨key, by rw [Spoly_coeff_neg]; exact key⟩

/-! ### `A = 3 X^D S` -/

/-- Negative exponent elimination: `3 T^D S` has no negative exponents, so `A` loses nothing. -/
theorem toLaurent_Apoly (Φ : CNF) :
    toLaurent (Apoly Φ) = (3 : ℤ[T;T⁻¹]) * T (Dexp Φ : ℤ) * Spoly Φ := by
  apply toLaurent_trunc_of_coeff_neg
  intro k hk
  rw [coeff_three_mul_T_mul, Spoly_coeff_eq_zero_of_lt, mul_zero]
  rw [abs_of_neg (by omega)]
  omega

/-- `[X^k] A = 3 [X^{k-D}] S`. -/
theorem Apoly_coeff (Φ : CNF) (k : ℕ) :
    (Apoly Φ).coeff k = 3 * (Spoly Φ).coeff ((k : ℤ) - Dexp Φ) := by
  rw [← toLaurent_coeff_natCast, toLaurent_Apoly, coeff_three_mul_T_mul]

/-- Every coefficient of `A` is divisible by `3`. -/
theorem three_dvd_Apoly_coeff (Φ : CNF) (k : ℕ) : 3 ∣ (Apoly Φ).coeff k := by
  rw [Apoly_coeff]
  exact dvd_mul_right _ _

/-- For a nonempty formula, `A(0) = 3 [X^{-D}] S ≠ 0`. -/
theorem Apoly_coeff_zero_ne_zero (Φ : CNF) (hΦ : Φ ≠ []) : (Apoly Φ).coeff 0 ≠ 0 := by
  rw [Apoly_coeff, Nat.cast_zero, zero_sub]
  exact mul_ne_zero three_ne_zero (Spoly_coeff_Dexp_ne_zero Φ hΦ).2

/-- `A ≠ 0` for a nonempty formula. -/
theorem Apoly_ne_zero (Φ : CNF) (hΦ : Φ ≠ []) : Apoly Φ ≠ 0 := by
  intro h
  apply Apoly_coeff_zero_ne_zero Φ hΦ
  rw [h, coeff_zero]

/-- `deg A ≤ 2D`. -/
theorem natDegree_Apoly_le (Φ : CNF) : (Apoly Φ).natDegree ≤ 2 * Dexp Φ := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [Apoly_coeff, Spoly_coeff_eq_zero_of_lt, mul_zero]
  rw [abs_of_pos (by omega)]
  omega

/-- `deg A = 2D` for a nonempty formula. -/
theorem natDegree_Apoly (Φ : CNF) (hΦ : Φ ≠ []) : (Apoly Φ).natDegree = 2 * Dexp Φ := by
  apply le_antisymm (natDegree_Apoly_le Φ)
  apply le_natDegree_of_ne_zero
  rw [Apoly_coeff, show ((2 * Dexp Φ : ℕ) : ℤ) - Dexp Φ = Dexp Φ by push_cast; ring]
  exact mul_ne_zero three_ne_zero (Spoly_coeff_Dexp_ne_zero Φ hΦ).1

/-- `A` is palindromic. -/
theorem reverse_Apoly (Φ : CNF) : (Apoly Φ).reverse = Apoly Φ := by
  rcases eq_or_ne Φ [] with rfl | hΦ
  · have : Apoly [] = 0 := by simp [Apoly, Spoly]
    rw [this, reverse_zero]
  · ext k
    rw [coeff_reverse, natDegree_Apoly Φ hΦ]
    rcases le_or_gt k (2 * Dexp Φ) with hk | hk
    · rw [revAt_le hk, Apoly_coeff, Apoly_coeff, ← Spoly_coeff_neg]
      congr 2
      push_cast [Nat.cast_sub hk]
      ring
    · rw [revAt_eq_self_of_lt hk]

/-- `A(u) = 3 u^D S(u)` at every unit `u`. -/
theorem aeval_Apoly {K : Type*} [CommRing K] (Φ : CNF) (u : Kˣ) :
    aeval (u : K) (Apoly Φ) = 3 * (u : K) ^ Dexp Φ * evalS Φ u := by
  rw [← eval₂_toLaurent_int, toLaurent_Apoly, map_mul, map_mul, eval₂_T, evalS, map_ofNat,
    zpow_natCast, Units.val_pow_eq_pow_val]

end SparseIrred
