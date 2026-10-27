import SparseIrred.Construction.Laurent

/-!
# ① Boolean encoding at `N`-th roots of unity (notes p. 7, equation (2))

"At an `N`-th root `ζ`, write `z_i = ζ^{m_i}`.  The two literal polynomials vanish exactly when
`z_i = 1` and `z_i ≠ 1`, respectively … Declare variable `i` true when `z_i = 1`.  Each clause is
satisfied exactly when its `C_j(ζ)` vanishes, and `S(ζ) = ∑_j |C_j(ζ)|²`.  Every Boolean assignment
arises: choose the exponent of `ζ` modulo `q_i` to be `0` for true and `1` for false, then use the
Chinese remainder theorem.  Therefore
`Φ satisfiable ⟺ ∃ ζ^N = 1 : S(ζ) = 0 ⟺ gcd_{ℚ[X]}(A, B) ≠ 1`."
-/

open Polynomial LaurentPolynomial ComplexConjugate

namespace SparseIrred

open Complexity.SAT

/-- `P⁺_i(ζ) = 0` iff `ζ^{m_i} = 1`. -/
theorem aeval_posLitPoly_eq_zero_iff (Φ : CNF) (ζ : ℂ) (i : ℕ) :
    aeval ζ (posLitPoly Φ i) = 0 ↔ ζ ^ mExp Φ i = 1 := by
  simp [posLitPoly, sub_eq_zero]

/-- At an `N`-th root of unity, `P⁻_i(ζ) = 0` iff `ζ^{m_i} ≠ 1`. -/
theorem aeval_negLitPoly_eq_zero_iff (Φ : CNF) {ζ : ℂ} (hζ : ζ ^ bigN Φ = 1) {i : ℕ}
    (hi : i < numVars Φ) : aeval ζ (negLitPoly Φ i) = 0 ↔ ζ ^ mExp Φ i ≠ 1 := by
  have hsum : aeval ζ (negLitPoly Φ i) = ∑ r ∈ Finset.range (oddPrime i), (ζ ^ mExp Φ i) ^ r := by
    simp [negLitPoly, map_sum, ← pow_mul, mul_comm]
  rw [hsum]
  have hz : (ζ ^ mExp Φ i) ^ oddPrime i = 1 := by rw [← pow_mul, mExp_mul_oddPrime Φ hi, hζ]
  constructor
  · intro h h1
    rw [h1] at h
    simp at h
    have := three_le_oddPrime i
    omega
  · intro h1
    have := geom_sum_mul (ζ ^ mExp Φ i) (oddPrime i)
    rw [hz, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h1)

/-! ### Evaluating `S` on the unit circle -/

/-- Evaluation of an integer polynomial commutes with complex conjugation. -/
private theorem aeval_conj_int (C : ℤ[X]) (z : ℂ) : aeval (conj z) C = conj (aeval z C) :=
  aeval_algHom_apply (starRingEnd ℂ).toIntAlgHom z C

/-- `S(ζ) = ∑_j |C_j(ζ)|²` on the unit circle (negative exponents are evaluated as powers of
`ζ⁻¹ = conj ζ`). -/
theorem evalS_eq_sum_normSq (Φ : CNF) (ζ : ℂˣ) (hζ : ‖(ζ : ℂ)‖ = 1) :
    evalS Φ ζ = ((Φ.map fun c => ‖aeval (ζ : ℂ) (clausePoly Φ c)‖ ^ 2).sum : ℝ) := by
  have key : ∀ C : ℤ[X], LaurentPolynomial.eval₂ (Int.castRingHom ℂ) ζ
      (toLaurent C * invert (toLaurent C)) = ((‖aeval (ζ : ℂ) C‖ ^ 2 : ℝ) : ℂ) := by
    intro C
    rw [map_mul, eval₂_toLaurent_int, eval₂_invert, eval₂_toLaurent_int,
      Units.val_inv_eq_inv_val, Complex.inv_eq_conj hζ, aeval_conj_int, Complex.mul_conj']
    push_cast; ring
  unfold evalS Spoly
  rw [show (((Φ.map fun c => ‖aeval (ζ : ℂ) (clausePoly Φ c)‖ ^ 2).sum : ℝ) : ℂ) =
      Complex.ofRealHom ((Φ.map fun c => ‖aeval (ζ : ℂ) (clausePoly Φ c)‖ ^ 2).sum) from rfl,
    map_list_sum, map_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  exact key _

/-! ### Clauses at `N`-th roots of unity -/

/-- A clause polynomial vanishes iff one of its literal polynomials does. -/
private theorem aeval_clausePoly_eq_zero_iff (Φ : CNF) (c : Clause) (ζ : ℂ) :
    aeval ζ (clausePoly Φ c) = 0 ↔ ∃ l ∈ c, aeval ζ (litPoly Φ l) = 0 := by
  rw [clausePoly, map_list_prod, List.prod_eq_zero_iff, List.map_map, List.mem_map]
  simp [eq_comm]

/-- A literal polynomial vanishes at an `N`-th root `ζ` iff the literal is true under the
assignment "`v` is true iff `ζ^{m_{idx v}} = 1`". -/
private theorem aeval_litPoly_eq_zero_iff (Φ : CNF) {ζ : ℂ} (hζ : ζ ^ bigN Φ = 1) {l : Lit}
    (hl : Occurs Φ l.var) :
    aeval ζ (litPoly Φ l) = 0 ↔ decide (ζ ^ mExp Φ (varIdx Φ l.var) = 1) = l.sign := by
  have hi := varIdx_lt_numVars Φ hl
  unfold litPoly
  cases hs : l.sign <;>
    simp [aeval_posLitPoly_eq_zero_iff Φ ζ, aeval_negLitPoly_eq_zero_iff Φ hζ hi]

/-- At an `N`-th root of unity, `S(ζ) = 0` iff every clause polynomial vanishes. -/
private theorem evalS_eq_zero_iff (Φ : CNF) (ζ : ℂˣ) (hN : (ζ : ℂ) ^ bigN Φ = 1) :
    evalS Φ ζ = 0 ↔ ∀ c ∈ Φ, aeval (ζ : ℂ) (clausePoly Φ c) = 0 := by
  have hnorm : ‖(ζ : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hN (bigN_pos Φ).ne'
  rw [evalS_eq_sum_normSq Φ ζ hnorm, Complex.ofReal_eq_zero]
  constructor
  · intro h c hc
    have hnn : ∀ x ∈ Φ.map (fun c => ‖aeval (ζ : ℂ) (clausePoly Φ c)‖ ^ 2), (0 : ℝ) ≤ x := by
      intro x hx
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hx
      positivity
    have := List.all_zero_of_le_zero_le_of_sum_eq_zero hnn h (List.mem_map_of_mem hc)
    simpa using this
  · intro h
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    simp [h c hc]

/-- The CRT step: for `k ≡ a_i (mod q_i)`, a primitive `N`-th root `ω` gives
`(ω^k)^{m_i} = 1 ⟺ q_i ∣ a_i`. -/
private theorem pow_mExp_eq_one_iff (Φ : CNF) {ω : ℂ} (hω : IsPrimitiveRoot ω (bigN Φ))
    {k a i : ℕ} (hi : i < numVars Φ) (hk : k ≡ a [MOD oddPrime i]) :
    (ω ^ k) ^ mExp Φ i = 1 ↔ oddPrime i ∣ a := by
  have hmq := mExp_mul_oddPrime Φ hi
  have hm : 0 < mExp Φ i := by
    rcases Nat.eq_zero_or_pos (mExp Φ i) with h | h
    · rw [h, zero_mul] at hmq; exact absurd hmq.symm (bigN_pos Φ).ne'
    · exact h
  rw [← pow_mul, hω.pow_eq_one_iff_dvd, ← hmq, mul_comm (mExp Φ i),
    Nat.mul_dvd_mul_iff_right hm]
  exact hk.dvd_iff dvd_rfl

/-- Every assignment is realised by an `N`-th root of unity: there is `ζ` with `ζ^N = 1` such
that, for every occurring variable `v`, `ζ^{m_i} = 1` (with `i` the index of `v`) exactly when `v`
is true.  Take `ζ = ω^k` for a primitive `N`-th root of unity `ω`, where `k ≡ 0 (mod q_i)` for true
and `k ≡ 1 (mod q_i)` for false variables (Chinese remainder theorem). -/
theorem exists_root_realizing (Φ : CNF) (α : Assignment) :
    ∃ ζ : ℂˣ, (ζ : ℂ) ^ bigN Φ = 1 ∧
      ∀ v, Occurs Φ v → ((ζ : ℂ) ^ mExp Φ (varIdx Φ v) = 1 ↔ α.get v = true) := by
  classical
  -- residue of the exponent modulo `q_i`: `0` for true, `1` for false
  let a : ℕ → ℕ := fun i =>
    if ∃ v, Occurs Φ v ∧ varIdx Φ v = i ∧ α.get v = false then 1 else 0
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset a oddPrime (Finset.range (numVars Φ))
    (fun i _ => (oddPrime_prime i).ne_zero) (fun i _ j _ hij => oddPrime_coprime hij)
  have hN0 : bigN Φ ≠ 0 := (bigN_pos Φ).ne'
  have hω := Complex.isPrimitiveRoot_exp (bigN Φ) hN0
  set ω := Complex.exp (2 * ↑Real.pi * Complex.I / ↑(bigN Φ))
  refine ⟨Units.mk0 (ω ^ k) (pow_ne_zero _ (hω.ne_zero hN0)), ?_, fun v hv => ?_⟩
  · rw [Units.val_mk0, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hi := varIdx_lt_numVars Φ hv
  have hq3 := three_le_oddPrime (varIdx Φ v)
  rw [Units.val_mk0, pow_mExp_eq_one_iff Φ hω hi (hk _ (Finset.mem_range.2 hi))]
  by_cases hf : α.get v = false
  · have ha : a (varIdx Φ v) = 1 := ite_eq_left ⟨v, hv, rfl, hf⟩
    rw [ha, hf]
    simp only [Bool.false_eq_true, iff_false]
    intro hd
    have := Nat.le_of_dvd one_pos hd
    omega
  · have ha : a (varIdx Φ v) = 0 := by
      refine ite_eq_right ?_
      rintro ⟨u, hu, hidx, hu'⟩
      rw [varIdx_injOn Φ hu hv hidx] at hu'
      exact hf hu'
    rw [ha]
    simpa using hf

/-- A satisfying assignment gives an `N`-th root of unity at which `S` vanishes. -/
theorem exists_root_of_satisfiable (Φ : CNF) (h : Φ.Satisfiable) :
    ∃ ζ : ℂˣ, (ζ : ℂ) ^ bigN Φ = 1 ∧ evalS Φ ζ = 0 := by
  obtain ⟨α, hα⟩ := h
  obtain ⟨ζ, hζN, hreal⟩ := exists_root_realizing Φ α
  refine ⟨ζ, hζN, (evalS_eq_zero_iff Φ ζ hζN).2 ?_⟩
  intro c hc
  rw [aeval_clausePoly_eq_zero_iff]
  unfold CNF.eval at hα
  have hcl := List.all_eq_true.1 hα c hc
  unfold Clause.eval at hcl
  obtain ⟨l, hl, hle⟩ := List.any_eq_true.1 hcl
  have hocc : Occurs Φ l.var := ⟨c, hc, l, hl, rfl⟩
  refine ⟨l, hl, (aeval_litPoly_eq_zero_iff Φ hζN hocc).2 ?_⟩
  simp only [hreal l.var hocc]
  simpa [Lit.eval] using hle

/-- An `N`-th root of unity at which `S` vanishes gives a satisfying assignment: `v` is true iff
`ζ^{m_i} = 1`, with `i` the index of `v`. -/
theorem satisfiable_of_root (Φ : CNF) (ζ : ℂˣ) (hN : (ζ : ℂ) ^ bigN Φ = 1)
    (hS : evalS Φ ζ = 0) : Φ.Satisfiable := by
  rw [evalS_eq_zero_iff Φ ζ hN] at hS
  let α : Assignment :=
    (List.range (Φ.maxVar + 1)).map fun v => decide ((ζ : ℂ) ^ mExp Φ (varIdx Φ v) = 1)
  have hα : ∀ v, Occurs Φ v → α.get v = decide ((ζ : ℂ) ^ mExp Φ (varIdx Φ v) = 1) := by
    intro v hv
    have hlt : v < Φ.maxVar + 1 := Nat.lt_succ_of_le hv.le_maxVar
    simp [α, Assignment.get, List.getElem?_range hlt]
  refine ⟨α, ?_⟩
  unfold CNF.eval
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨l, hl, hl0⟩ := (aeval_clausePoly_eq_zero_iff Φ c _).1 (hS c hc)
  have hocc : Occurs Φ l.var := ⟨c, hc, l, hl, rfl⟩
  unfold Clause.eval
  rw [List.any_eq_true]
  refine ⟨l, hl, ?_⟩
  simp only [Lit.eval, hα l.var hocc, (aeval_litPoly_eq_zero_iff Φ hN hocc).1 hl0,
    beq_self_eq_true]

/-- The first equivalence of (2): `Φ` is satisfiable iff `S(ζ) = 0` for some `ζ` with
`ζ^N = 1`. -/
theorem satisfiable_iff_exists_root (Φ : CNF) :
    Φ.Satisfiable ↔ ∃ ζ : ℂˣ, (ζ : ℂ) ^ bigN Φ = 1 ∧ evalS Φ ζ = 0 :=
  ⟨exists_root_of_satisfiable Φ, fun ⟨ζ, hN, hS⟩ => satisfiable_of_root Φ ζ hN hS⟩

/-- `Φ` is satisfiable iff `A` and `B` have a common complex root. -/
theorem satisfiable_iff_exists_common_root (Φ : CNF) :
    Φ.Satisfiable ↔ ∃ ζ : ℂ, aeval ζ (Apoly Φ) = 0 ∧ aeval ζ (Bpoly Φ) = 0 := by
  rw [satisfiable_iff_exists_root]
  constructor
  · rintro ⟨ζ, hN, hS⟩
    refine ⟨ζ, ?_, ?_⟩
    · rw [aeval_Apoly, hS, mul_zero]
    · simp [Bpoly, hN]
  · rintro ⟨ζ, hA, hB⟩
    have hN : ζ ^ bigN Φ = 1 := by simpa [Bpoly, sub_eq_zero] using hB
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (bigN_pos Φ).ne'] at hN
      exact zero_ne_one hN
    refine ⟨Units.mk0 ζ hζ0, by simpa using hN, ?_⟩
    have h := aeval_Apoly Φ (Units.mk0 ζ hζ0)
    rw [Units.val_mk0, hA] at h
    have h3 : (3 : ℂ) * ζ ^ Dexp Φ ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hζ0)
    exact (mul_eq_zero.1 h.symm).resolve_left h3

/-- The second equivalence of (2): `gcd_{ℚ[X]}(A, B) ≠ 1`. -/
theorem satisfiable_iff_not_isCoprime (Φ : CNF) :
    Φ.Satisfiable ↔
      ¬IsCoprime ((Apoly Φ).map (Int.castRingHom ℚ)) ((Bpoly Φ).map (Int.castRingHom ℚ)) := by
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ, satisfiable_iff_exists_common_root,
    ← algebraMap_int_eq]
  simp only [aeval_map_algebraMap ℚ]
  push Not
  rfl

end SparseIrred
