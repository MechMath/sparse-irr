import SparseIrred.UpperBounds.Section4.OracleMachineControl

/-! # A first-return bound for the complete oracle coroutine -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

variable {A R C I : Type*} [Add R] [Mul R]

private theorem simulate_step_bounded (P : EntryProgram A R) (request : A → Option I)
    (answer : I → R) (O : ScalarOracle I R C answer)
    (hrequest : ∀ a i, request a = some i → P.instruction a = .value (answer i))
    (U : ℕ) (hU : ∀ i, O.stop i ≤ U) (c : EntryConfig A R) :
    ∃ t, t ≤ U + 2 ∧ (oracleCoroutineStep P request answer O)^[t] (.outer c) = .outer (P.step c) := by
  cases c with
  | ret v stack => exact ⟨1, by omega, rfl⟩
  | eval a stack =>
    cases hr : request a with
    | none => exact ⟨1, by omega, by simp [oracleCoroutineStep, hr]⟩
    | some i =>
      refine ⟨(O.stop i + 1) + 1, by have := hU i; omega, ?_⟩
      rw [Function.iterate_succ_apply]
      simp only [oracleCoroutineStep, hr]
      rw [oracleCoroutine_query_returns, EntryProgram.step, hrequest a i hr]

theorem oracleCoroutine_simulates_bounded (P : EntryProgram A R) (request : A → Option I)
    (answer : I → R) (O : ScalarOracle I R C answer)
    (hrequest : ∀ a i, request a = some i → P.instruction a = .value (answer i))
    (U : ℕ) (hU : ∀ i, O.stop i ≤ U) (c : EntryConfig A R) (u : ℕ) :
    ∃ t, t ≤ u * (U + 2) ∧
      (oracleCoroutineStep P request answer O)^[t] (.outer c) = .outer (P.step^[u] c) := by
  induction u with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ u ih =>
    obtain ⟨t, ht, he⟩ := ih
    obtain ⟨v, hv, hve⟩ := simulate_step_bounded P request answer O hrequest U hU (P.step^[u] c)
    refine ⟨v + t, by nlinarith, ?_⟩
    rw [Function.iterate_add_apply, he, hve, Function.iterate_succ_apply']

/-- The full coroutine's exponential time bound follows from controller depth and oracle space. -/
theorem oracleCoroutine_terminates_bounded (P : EntryProgram A R) (request : A → Option I)
    (answer : I → R) (O : ScalarOracle I R C answer)
    (hrequest : ∀ a i, request a = some i → P.instruction a = .value (answer i))
    (initial : A) (e : ℕ) (he : ∀ i, O.stop i ≤ 2 ^ e) :
    ∃ t, t ≤ 2 ^ (P.rank initial + e + 5) ∧
      (oracleCoroutineStep P request answer O)^[t] (.outer (.eval initial [])) =
        .outer (.ret (P.value initial) []) := by
  obtain ⟨u, v, hu, huv⟩ := P.terminates_bounded (.eval initial [])
  have hv := P.meaning_iterate (.eval initial []) u
  rw [huv] at hv
  change v = P.value initial at hv
  obtain ⟨t, ht, hte⟩ := oracleCoroutine_simulates_bounded P request answer O hrequest
    (2 ^ e) he (.eval initial []) u
  refine ⟨t, ?_, by rw [huv, hv] at hte; exact hte⟩
  have hs := P.treeSize_le initial
  simp only [EntryProgram.work, List.map_nil, List.sum_nil, add_zero] at hu
  have hup : u ≤ 2 ^ (P.rank initial + 3) := by
    have heq : 2 ^ (P.rank initial + 3) = 4 * 2 ^ (P.rank initial + 1) := by
      rw [show P.rank initial + 3 = (P.rank initial + 1) + 2 by omega, pow_add]
      norm_num; omega
    rw [heq]; omega
  have hep : 2 ^ e + 2 ≤ 2 ^ (e + 2) := by
    have hpos : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by omega)
    rw [pow_add]; norm_num; omega
  calc
    t ≤ u * (2 ^ e + 2) := ht
    _ ≤ 2 ^ (P.rank initial + 3) * 2 ^ (e + 2) := Nat.mul_le_mul hup hep
    _ = 2 ^ (P.rank initial + e + 5) := by rw [← pow_add]; congr 1; omega

def OracleCoroutineConfig.Halted : OracleCoroutineConfig A R C → Prop
  | .outer (.ret _ []) => True
  | _ => False

instance oracleCoroutineHaltedDecidable (c : OracleCoroutineConfig A R C) : Decidable c.Halted := by
  cases c with
  | query a stack c => exact isFalse id
  | outer c => cases c with
    | eval a stack => exact isFalse id
    | ret v stack => cases stack with
      | nil => exact isTrue trivial
      | cons f stack => exact isFalse id

/-- A completed coroutine state is absorbing. -/
theorem oracleCoroutine_halted_fixed (P : EntryProgram A R) (request : A → Option I)
    (answer : I → R) (O : ScalarOracle I R C answer) (c : OracleCoroutineConfig A R C)
    (hc : c.Halted) : oracleCoroutineStep P request answer O c = c := by
  cases c with
  | query a stack c => exact hc.elim
  | outer c => cases c with
    | eval a stack => exact hc.elim
    | ret v stack => cases stack with
      | nil => rfl
      | cons f stack => exact hc.elim

/-- The first completed coroutine state has the proved value and the same exponential bound. -/
theorem oracleCoroutine_firstHalt (P : EntryProgram A R) (request : A → Option I)
    (answer : I → R) (O : ScalarOracle I R C answer)
    (hrequest : ∀ a i, request a = some i → P.instruction a = .value (answer i))
    (initial : A) (e : ℕ) (he : ∀ i, O.stop i ≤ 2 ^ e) :
    ∃ t, t ≤ 2 ^ (P.rank initial + e + 5) ∧
      (oracleCoroutineStep P request answer O)^[t] (.outer (.eval initial [])) =
        .outer (.ret (P.value initial) []) ∧
      ∀ u < t, ¬((oracleCoroutineStep P request answer O)^[u]
        (.outer (.eval initial []))).Halted := by
  let step := oracleCoroutineStep P request answer O
  let start : OracleCoroutineConfig A R C := .outer (.eval initial [])
  obtain ⟨t₀, ht₀, hr₀⟩ := oracleCoroutine_terminates_bounded P request answer O
    hrequest initial e he
  have hex : ∃ t, (step^[t] start).Halted := ⟨t₀, by rw [hr₀]; trivial⟩
  let t := Nat.find hex
  have hh : (step^[t] start).Halted := Nat.find_spec hex
  have ht : t ≤ t₀ := Nat.find_min' hex (by rw [hr₀]; trivial)
  have hfix : ∀ u, step^[u] (step^[t] start) = step^[t] start := by
    intro u
    induction u with
    | zero => rfl
    | succ u ih =>
      rw [Function.iterate_succ_apply', ih]
      exact oracleCoroutine_halted_fixed P request answer O _ hh
  have hsame : step^[t₀] start = step^[t] start := by
    rw [show t₀ = (t₀ - t) + t by omega, Function.iterate_add_apply, hfix]
  exact ⟨t, ht.trans ht₀, hsame.symm.trans hr₀, fun u hu ↦ Nat.find_min hex hu⟩

end SparseIrred.UpperBounds.Section4
