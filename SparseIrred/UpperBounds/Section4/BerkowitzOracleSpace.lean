import SparseIrred.UpperBounds.Section4.BerkowitzProgramOracle
import SparseIrred.UpperBounds.Section4.BerkowitzProgramBounds
import SparseIrred.UpperBounds.Section4.StackFramed

/-!
# Space composition with an arbitrary terminating matrix-entry oracle

An oracle may take arbitrary time. Its configuration is advanced one step at a
time while the determinant continuation is preserved. Its workspace is reused
at the next call. The assumptions below concern the entry oracle alone; no
polynomial-time oracle or correctness of the determinant computation is assumed.
-/

noncomputable section

namespace SparseIrred.UpperBounds.Section4

open Matrix Complexity

/-- A terminating entry computation with its first return time as a proof index.
`stop` is not stored in any runtime state. -/
structure ScalarOracle (I R C : Type*) (answer : I → R) where
  start : I → C
  step : C → C
  read : C → Option R
  stop : I → ℕ
  running : ∀ i t, t < stop i → read (step^[t] (start i)) = none
  returned : ∀ i, read (step^[stop i] (start i)) = some (answer i)

inductive OracleCoroutineConfig (A R C : Type*) where
  | outer (config : EntryConfig A R)
  | query (address : A) (stack : List (EntryFrame A R)) (oracle : C)

section Coroutine

variable {A R C I : Type*} [Add R] [Mul R]
    (P : EntryProgram A R) (request : A → Option I) (answer : I → R)
    (O : ScalarOracle I R C answer)

def oracleCoroutineStep : OracleCoroutineConfig A R C → OracleCoroutineConfig A R C
  | .outer (.eval a stack) => match request a with
    | none => .outer (P.step (.eval a stack))
    | some i => .query a stack (O.start i)
  | .outer (.ret v stack) => .outer (P.step (.ret v stack))
  | .query a stack c => match O.read c with
    | none => .query a stack (O.step c)
    | some r => .outer (.ret r stack)

theorem oracleCoroutine_query_iterate (a : A) (stack : List (EntryFrame A R)) (i : I)
    (t : ℕ) (ht : t ≤ O.stop i) :
    (oracleCoroutineStep P request answer O)^[t] (.query a stack (O.start i)) =
      .query a stack (O.step^[t] (O.start i)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by omega), oracleCoroutineStep,
      O.running i t (by omega), Function.iterate_succ_apply']

theorem oracleCoroutine_query_returns (a : A) (stack : List (EntryFrame A R)) (i : I) :
    (oracleCoroutineStep P request answer O)^[O.stop i + 1] (.query a stack (O.start i)) =
      .outer (.ret (answer i) stack) := by
  rw [Function.iterate_succ_apply', oracleCoroutine_query_iterate _ _ _ _ _ _ _ _ le_rfl,
    oracleCoroutineStep, O.returned]

variable (hrequest : ∀ a i, request a = some i → P.instruction a = .value (answer i))

include hrequest

/-- Each original step is simulated by finitely many coroutine steps. -/
theorem oracleCoroutine_simulates_step (c : EntryConfig A R) :
    ∃ t, (oracleCoroutineStep P request answer O)^[t] (.outer c) = .outer (P.step c) := by
  cases c with
  | ret v stack => exact ⟨1, rfl⟩
  | eval a stack =>
    cases hr : request a with
    | none => exact ⟨1, by simp [oracleCoroutineStep, hr]⟩
    | some i =>
      refine ⟨(O.stop i + 1) + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      simp only [oracleCoroutineStep, hr]
      rw [oracleCoroutine_query_returns, EntryProgram.step, hrequest a i hr]

theorem oracleCoroutine_simulates_iterate (c : EntryConfig A R) (u : ℕ) :
    ∃ t, (oracleCoroutineStep P request answer O)^[t] (.outer c) = .outer (P.step^[u] c) := by
  induction u with
  | zero => exact ⟨0, rfl⟩
  | succ u ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨v, hv⟩ := oracleCoroutine_simulates_step P request answer O hrequest (P.step^[u] c)
    refine ⟨v + t, ?_⟩
    rw [Function.iterate_add_apply, ht, hv, Function.iterate_succ_apply']

/-- The full coroutine terminates with the same scalar as the arithmetic program. -/
theorem oracleCoroutine_correct (initial : A) :
    ∃ t, (oracleCoroutineStep P request answer O)^[t] (.outer (.eval initial [])) =
      .outer (.ret (P.value initial) []) := by
  obtain ⟨u, hu⟩ := P.correct initial
  obtain ⟨t, ht⟩ := oracleCoroutine_simulates_iterate P request answer O hrequest
    (.eval initial []) u
  exact ⟨t, ht.trans (congrArg OracleCoroutineConfig.outer hu)⟩

/-- A suspended oracle retains a reachable determinant configuration and an in-range
prefix of the oracle's own execution. -/
def OracleCoroutineValid (initial : A) : OracleCoroutineConfig A R C → Prop
  | .outer c => ∃ u, P.step^[u] (.eval initial []) = c
  | .query a stack c => ∃ u i t,
      P.step^[u] (.eval initial []) = .eval a stack ∧ request a = some i ∧
      t ≤ O.stop i ∧ c = O.step^[t] (O.start i)

theorem oracleCoroutine_valid_step (initial : A) (c : OracleCoroutineConfig A R C)
    (hc : OracleCoroutineValid P request answer O initial c) :
    OracleCoroutineValid P request answer O initial (oracleCoroutineStep P request answer O c) := by
  cases c with
  | outer c =>
    obtain ⟨u, hu⟩ := hc
    have hs : P.step^[u + 1] (.eval initial []) = P.step c := by
      rw [Function.iterate_succ_apply', hu]
    cases c with
    | ret v stack => exact ⟨u + 1, hs⟩
    | eval a stack =>
      cases hr : request a with
      | none => simpa only [oracleCoroutineStep, hr] using (show
          OracleCoroutineValid P request answer O initial (.outer (P.step (.eval a stack))) from
            ⟨u + 1, hs⟩)
      | some i =>
        simp only [oracleCoroutineStep, hr, OracleCoroutineValid]
        exact ⟨u, i, 0, hu, rfl, Nat.zero_le _, rfl⟩
  | query a stack c =>
    obtain ⟨u, i, t, hu, hr, ht, rfl⟩ := hc
    by_cases hlt : t < O.stop i
    · simp only [oracleCoroutineStep, O.running i t hlt, OracleCoroutineValid]
      exact ⟨u, i, t + 1, hu, hr, by omega, (Function.iterate_succ_apply' _ _ _).symm⟩
    · have heq : t = O.stop i := by omega
      subst t
      simp only [oracleCoroutineStep, O.returned, OracleCoroutineValid]
      refine ⟨u + 1, ?_⟩
      rw [Function.iterate_succ_apply', hu, EntryProgram.step, hrequest a i hr]

theorem oracleCoroutine_valid_iterate (initial : A) (t : ℕ) :
    OracleCoroutineValid P request answer O initial
      ((oracleCoroutineStep P request answer O)^[t] (.outer (.eval initial []))) := by
  induction t with
  | zero => exact ⟨0, rfl⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact oracleCoroutine_valid_step P request answer O hrequest initial _ ih

end Coroutine

/-- The saved continuation is self-delimited; the oracle workspace follows it. -/
def OracleCoroutineConfig.encode {A R C : Type*}
    (encP : EntryConfig A R → List Bool) (encC : C → List Bool) :
    OracleCoroutineConfig A R C → List Bool
  | .outer c => false :: encP c
  | .query a stack c => true :: pair (encP (.eval a stack)) (encC c)

theorem OracleCoroutineConfig.encode_injective {A R C : Type*}
    (encP : EntryConfig A R → List Bool) (encC : C → List Bool)
    (hP : Function.Injective encP) (hC : Function.Injective encC) :
    Function.Injective (OracleCoroutineConfig.encode encP encC) := by
  intro c d h
  cases c <;> cases d <;>
    simp only [encode, List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false,
      false_and, true_and] at h
  · exact congrArg OracleCoroutineConfig.outer (hP h)
  · obtain ⟨ha, hc⟩ := pair_inj h
    have he := hP ha
    cases he
    exact congrArg _ (hC hc)

theorem oracleCoroutine_space {A R C I : Type*} [Add R] [Mul R]
    (P : EntryProgram A R) (request : A → Option I) (answer : I → R)
    (O : ScalarOracle I R C answer)
    (hrequest : ∀ a i, request a = some i → P.instruction a = .value (answer i))
    (initial : A) (encP : EntryConfig A R → List Bool) (encC : C → List Bool)
    (B S : ℕ) (hP : ∀ t, (encP (P.step^[t] (.eval initial []))).length ≤ B)
    (hO : ∀ i t, t ≤ O.stop i → (encC (O.step^[t] (O.start i))).length ≤ S) (t : ℕ) :
    (((oracleCoroutineStep P request answer O)^[t] (.outer (.eval initial []))).encode
      encP encC).length ≤ 2 * B + S + 3 := by
  have hv := oracleCoroutine_valid_iterate P request answer O hrequest initial t
  cases hc : (oracleCoroutineStep P request answer O)^[t] (.outer (.eval initial [])) with
  | outer c =>
    rw [hc] at hv
    obtain ⟨u, rfl⟩ := hv
    have hb := hP u
    simp only [OracleCoroutineConfig.encode, List.length_cons]
    omega
  | query a stack c =>
    rw [hc] at hv
    obtain ⟨u, i, v, hu, hr, ht, rfl⟩ := hv
    have hb := hP u
    rw [hu] at hb
    have hs := hO i v ht
    simp only [OracleCoroutineConfig.encode, List.length_cons, pair_length]
    omega

variable {R C : Type*} [CommRing R] {n : ℕ}

/-- The full content of Lemma 17's oracle-space composition. The oracle may use
space `S` and arbitrary time; the determinant controller contributes only a
polynomial in the binary address and scalar widths and in `log n`. -/
theorem lemma17_space_composition (A : Matrix (Fin n) (Fin n) R)
    (O : ScalarOracle (Fin n × Fin n) R C (fun ij ↦ A ij.1 ij.2))
    (encA : BerkowitzAddress n → List Bool) (encR : R → List Bool) (encC : C → List Bool)
    (w S : ℕ) (hA : ∀ a, a.Bounded → (encA a).length ≤ w)
    (hR : ∀ r, (encR r).length ≤ w)
    (hO : ∀ ij t, t ≤ O.stop ij → (encC (O.step^[t] (O.start ij))).length ≤ S) :
    (∃ t, (oracleCoroutineStep (berkowitzProgram A) berkowitzEntryRequest
      (fun ij ↦ A ij.1 ij.2) O)^[t] (.outer (.eval .initial [])) = .outer (.ret A.det [])) ∧
    ∀ t, (((oracleCoroutineStep (berkowitzProgram A) berkowitzEntryRequest
      (fun ij ↦ A ij.1 ij.2) O)^[t] (.outer (.eval .initial []))).encode
        (EntryConfig.framedEncode encA encR) encC).length ≤
      2 * (2 * w + (2 * w + 7) * berkowitzStackBound n + 4) + S + 3 := by
  constructor
  · simpa only [berkowitzProgram_value] using oracleCoroutine_correct (berkowitzProgram A)
      berkowitzEntryRequest (fun ij ↦ A ij.1 ij.2) O
      (berkowitzEntryRequest_instruction A) .initial
  · intro t
    apply oracleCoroutine_space (berkowitzProgram A) berkowitzEntryRequest
      (fun ij ↦ A ij.1 ij.2) O (berkowitzEntryRequest_instruction A) .initial
      (EntryConfig.framedEncode encA encR) encC
      (2 * w + (2 * w + 7) * berkowitzStackBound n + 4) S
    · intro u
      have had := EntryProgram.addresses_iterate (berkowitzProgram A)
        BerkowitzAddress.Bounded (berkowitzProgram_closed A) .initial
        (by trivial) u
      have hb := EntryConfig.framedEncode_length_le encA encR BerkowitzAddress.Bounded
        w hA hR _ had
      have hs := berkowitzProgram_stack_bound A u
      exact hb.trans (by nlinarith)
    · exact hO

/-- Lemma 17 with a faithful binary representation of the entire coroutine state.
Injectivity rules out artificially short codes that discard oracle or controller state. -/
theorem lemma17_faithful_space_composition (A : Matrix (Fin n) (Fin n) R)
    (O : ScalarOracle (Fin n × Fin n) R C (fun ij ↦ A ij.1 ij.2))
    (encA : BerkowitzAddress n → List Bool) (encR : R → List Bool) (encC : C → List Bool)
    (hinjA : Function.Injective encA) (hinjR : Function.Injective encR)
    (hinjC : Function.Injective encC)
    (w S : ℕ) (hA : ∀ a, a.Bounded → (encA a).length ≤ w)
    (hR : ∀ r, (encR r).length ≤ w)
    (hO : ∀ ij t, t ≤ O.stop ij → (encC (O.step^[t] (O.start ij))).length ≤ S) :
    Function.Injective (OracleCoroutineConfig.encode (EntryConfig.framedEncode encA encR) encC) ∧
    (∃ t, (oracleCoroutineStep (berkowitzProgram A) berkowitzEntryRequest
      (fun ij ↦ A ij.1 ij.2) O)^[t] (.outer (.eval .initial [])) = .outer (.ret A.det [])) ∧
    ∀ t, (((oracleCoroutineStep (berkowitzProgram A) berkowitzEntryRequest
      (fun ij ↦ A ij.1 ij.2) O)^[t] (.outer (.eval .initial []))).encode
        (EntryConfig.framedEncode encA encR) encC).length ≤
      2 * (2 * w + (2 * w + 7) * berkowitzStackBound n + 4) + S + 3 := by
  exact ⟨OracleCoroutineConfig.encode_injective _ _
    (EntryConfig.framedEncode_injective encA encR hinjA hinjR) hinjC,
    lemma17_space_composition A O encA encR encC w S hA hR hO⟩

end SparseIrred.UpperBounds.Section4
