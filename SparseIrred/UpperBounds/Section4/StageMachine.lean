import SparseIrred.UpperBounds.Section4.StackMachine

/-!
# Three-stage execution with validated changes of scalar type

Each stage runs an actual address-stack program. A later stage may use the
proved acceptance of its predecessors to construct its scalar field. The
control transition tests only a scalar that has already been returned; it does
not call the semantic value of an entire stage as an oracle.
-/

namespace SparseIrred.UpperBounds.Section4

structure StageSpec where
  Addr : Type
  Scalar : Type
  add : Add Scalar
  mul : Mul Scalar
  program : EntryProgram Addr Scalar
  initial : Addr
  output : Scalar → Bool

attribute [instance] StageSpec.add StageSpec.mul

namespace StageSpec

def initialConfig (S : StageSpec) : EntryConfig S.Addr S.Scalar := .eval S.initial []

def answer (S : StageSpec) : Bool := S.output (S.program.value S.initial)

/-- Only configurations on the genuine execution trace inhabit a stage state. -/
def ReachableCfg (S : StageSpec) :=
  {c : EntryConfig S.Addr S.Scalar // ∃ t, S.program.step^[t] S.initialConfig = c}

def initialCfg (S : StageSpec) : S.ReachableCfg := ⟨S.initialConfig, 0, rfl⟩

def advance (S : StageSpec) (c : S.ReachableCfg) : S.ReachableCfg :=
  ⟨S.program.step c.val, by
    obtain ⟨t, ht⟩ := c.property
    exact ⟨t + 1, by rw [Function.iterate_succ_apply', ht]⟩⟩

def returnedValue (S : StageSpec) (c : EntryConfig S.Addr S.Scalar)
    (h : c.Halted) : S.Scalar :=
  match c with
  | .eval _ _ => False.elim h
  | .ret v [] => v
  | .ret _ (_ :: _) => False.elim h

theorem returnedValue_eq_value (S : StageSpec) (c : S.ReachableCfg)
    (h : c.val.Halted) : S.returnedValue c.val h = S.program.value S.initial := by
  obtain ⟨t, ht⟩ := c.property
  have hv := S.program.meaning_iterate S.initialConfig t
  rw [ht] at hv
  rcases c with ⟨c, hc⟩
  cases c with
  | eval a stack => exact h.elim
  | ret v stack => cases stack with
    | nil => exact hv
    | cons f stack => exact h.elim

theorem returned_output_eq_answer (S : StageSpec) (c : S.ReachableCfg)
    (h : c.val.Halted) : S.output (S.returnedValue c.val h) = S.answer := by
  rw [S.returnedValue_eq_value]
  rfl

theorem answer_true_of_returned (S : StageSpec) (c : S.ReachableCfg)
    (h : c.val.Halted) (ha : S.output (S.returnedValue c.val h) = true) :
    S.answer = true := (S.returned_output_eq_answer c h).symm.trans ha

theorem work_eq_zero_of_halted (S : StageSpec) (c : S.ReachableCfg)
    (h : c.val.Halted) : S.program.work c.val = 0 := by
  rcases c with ⟨c, hc⟩
  cases c with
  | eval a stack => exact h.elim
  | ret v stack => cases stack with
    | nil => rfl
    | cons f stack => exact h.elim

end StageSpec

structure ThreeStages where
  first : StageSpec
  second : first.answer = true → StageSpec
  third : ∀ h, (second h).answer = true → StageSpec

namespace ThreeStages

inductive State (T : ThreeStages) where
  | first (c : T.first.ReachableCfg)
  | second (h : T.first.answer = true) (c : (T.second h).ReachableCfg)
  | third (h : T.first.answer = true) (h' : (T.second h).answer = true)
      (c : (T.third h h').ReachableCfg)
  | done (answer : Bool)

def initial (T : ThreeStages) : T.State := .first T.first.initialCfg

def step (T : ThreeStages) : T.State → T.State
  | .first c =>
      if hc : c.val.Halted then
        if ha : T.first.output (T.first.returnedValue c.val hc) = true then
          .second (T.first.answer_true_of_returned c hc ha)
            (T.second (T.first.answer_true_of_returned c hc ha)).initialCfg
        else .done false
      else .first (T.first.advance c)
  | .second h c =>
      if hc : c.val.Halted then
        if ha : (T.second h).output ((T.second h).returnedValue c.val hc) = true then
          .third h ((T.second h).answer_true_of_returned c hc ha)
            (T.third h ((T.second h).answer_true_of_returned c hc ha)).initialCfg
        else .done false
      else .second h ((T.second h).advance c)
  | .third h h' c =>
      if hc : c.val.Halted then
        .done ((T.third h h').output ((T.third h h').returnedValue c.val hc))
      else .third h h' ((T.third h h').advance c)
  | .done b => .done b

def answer (T : ThreeStages) : Bool :=
  if h : T.first.answer = true then
    if h' : (T.second h).answer = true then (T.third h h').answer else false
  else false

def meaning (T : ThreeStages) : T.State → Bool
  | .first _ => T.answer
  | .second h _ => if h' : (T.second h).answer = true then (T.third h h').answer else false
  | .third h h' _ => (T.third h h').answer
  | .done b => b

@[simp] theorem meaning_initial (T : ThreeStages) : T.meaning T.initial = T.answer := rfl

theorem meaning_step (T : ThreeStages) (s : T.State) :
    T.meaning (T.step s) = T.meaning s := by
  cases s with
  | first c =>
      simp only [step]
      split_ifs with hc ha
      · have h := T.first.answer_true_of_returned c hc ha
        simp [meaning, answer, h]
      · have h : T.first.answer ≠ true := by
          rwa [T.first.returned_output_eq_answer c hc] at ha
        simp [meaning, answer, h]
      · rfl
  | second h c =>
      simp only [step]
      split_ifs with hc ha
      · have h' := (T.second h).answer_true_of_returned c hc ha
        simp [meaning, h']
      · have h' : (T.second h).answer ≠ true := by
          rwa [(T.second h).returned_output_eq_answer c hc] at ha
        simp [meaning, h']
      · rfl
  | third h h' c =>
      simp only [step]
      split_ifs with hc
      · exact (T.third h h').returned_output_eq_answer c hc
      · rfl
  | done b => rfl

theorem meaning_iterate (T : ThreeStages) (s : T.State) (t : ℕ) :
    T.meaning (T.step^[t] s) = T.meaning s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', T.meaning_step, ih]

def State.Halted {T : ThreeStages} : T.State → Prop
  | .done _ => True
  | _ => False

instance {T : ThreeStages} (s : T.State) : Decidable s.Halted := by
  cases s <;> first | exact isTrue trivial | exact isFalse id

/-- A common bound on the three initial mathematical work measures. -/
structure WorkBound (T : ThreeStages) (B : ℕ) : Prop where
  first : T.first.program.work T.first.initialConfig ≤ B
  second : ∀ h, (T.second h).program.work (T.second h).initialConfig ≤ B
  third : ∀ h h', (T.third h h').program.work (T.third h h').initialConfig ≤ B

/-- Future phases are prepaid; this measure is not stored in the machine state. -/
def work (T : ThreeStages) (B : ℕ) : T.State → ℕ
  | .first c => T.first.program.work c.val + 2 * (B + 1) + 1
  | .second h c => (T.second h).program.work c.val + (B + 1) + 1
  | .third h h' c => (T.third h h').program.work c.val + 1
  | .done _ => 0

theorem work_step_lt (T : ThreeStages) (B : ℕ) (hB : T.WorkBound B)
    (s : T.State) (hs : ¬s.Halted) : T.work B (T.step s) < T.work B s := by
  cases s with
  | first c =>
      simp only [step]
      split_ifs with hc ha
      · have hz := T.first.work_eq_zero_of_halted c hc
        have hb := hB.second (T.first.answer_true_of_returned c hc ha)
        change (T.second _).program.work (T.second _).initialConfig + (B + 1) + 1 < _
        simp only [work]
        omega
      · simp only [work]
        omega
      · have h := T.first.program.work_step_lt c.val hc
        simpa only [work, StageSpec.advance] using Nat.add_lt_add_right
          (Nat.add_lt_add_right h (2 * (B + 1))) 1
  | second h c =>
      simp only [step]
      split_ifs with hc ha
      · have hz := (T.second h).work_eq_zero_of_halted c hc
        have hb := hB.third h ((T.second h).answer_true_of_returned c hc ha)
        change (T.third h _).program.work (T.third h _).initialConfig + 1 < _
        simp only [work]
        omega
      · simp only [work]
        omega
      · have hl := (T.second h).program.work_step_lt c.val hc
        simpa only [work, StageSpec.advance] using Nat.add_lt_add_right
          (Nat.add_lt_add_right hl (B + 1)) 1
  | third h h' c =>
      simp only [step]
      split_ifs with hc
      · simp only [work]
        omega
      · have hl := (T.third h h').program.work_step_lt c.val hc
        simpa only [work, StageSpec.advance] using Nat.add_lt_add_right hl 1
  | done b => exact (hs trivial).elim

theorem terminates_bounded (T : ThreeStages) (B : ℕ) (hB : T.WorkBound B) (s : T.State) :
    ∃ t b, t ≤ T.work B s ∧ T.step^[t] s = .done b := by
  induction hw : T.work B s using Nat.strong_induction_on generalizing s with
  | h w ih =>
      by_cases hs : s.Halted
      · cases s with
        | first c => exact hs.elim
        | second h c => exact hs.elim
        | third h h' c => exact hs.elim
        | done b => exact ⟨0, b, by omega, rfl⟩
      · have hl := T.work_step_lt B hB s hs
        obtain ⟨t, b, ht, he⟩ := ih _ (hw ▸ hl) (T.step s) rfl
        exact ⟨t + 1, b, by omega, by simpa [Function.iterate_succ_apply] using he⟩

theorem initial_work_le (T : ThreeStages) (B : ℕ) (hB : T.WorkBound B) :
    T.work B T.initial ≤ 3 * (B + 1) := by
  have h := hB.first
  change T.first.program.work T.first.initialConfig + 2 * (B + 1) + 1 ≤ _
  omega

/-- The first terminating index is selected from the internally proved termination. -/
noncomputable def stop (T : ThreeStages) (B : ℕ) (hB : T.WorkBound B) : ℕ :=
  Nat.find (show ∃ t, (T.step^[t] T.initial).Halted from by
    obtain ⟨t, b, _, he⟩ := T.terminates_bounded B hB T.initial
    exact ⟨t, by rw [he]; trivial⟩)

theorem halted_stop (T : ThreeStages) (B : ℕ) (hB : T.WorkBound B) :
    (T.step^[T.stop B hB] T.initial).Halted := by
  unfold stop
  exact Nat.find_spec (p := fun t ↦ (T.step^[t] T.initial).Halted) _

theorem not_halted_before (T : ThreeStages) (B : ℕ) (hB : T.WorkBound B)
    (t : ℕ) (ht : t < T.stop B hB) : ¬(T.step^[t] T.initial).Halted := Nat.find_min _ ht

theorem stop_result (T : ThreeStages) (B : ℕ) (hB : T.WorkBound B) :
    T.step^[T.stop B hB] T.initial = .done T.answer := by
  have hh := T.halted_stop B hB
  have hv := T.meaning_iterate T.initial (T.stop B hB)
  cases he : T.step^[T.stop B hB] T.initial with
  | first c => simp only [he, State.Halted] at hh
  | second h c => simp only [he, State.Halted] at hh
  | third h h' c => simp only [he, State.Halted] at hh
  | done b =>
      rw [he] at hv
      change b = T.answer at hv
      exact congrArg State.done hv

theorem stop_bound (T : ThreeStages) (B : ℕ) (hB : T.WorkBound B) :
    T.stop B hB ≤ 3 * (B + 1) := by
  obtain ⟨t, b, ht, he⟩ := T.terminates_bounded B hB T.initial
  have hf : T.stop B hB ≤ t := Nat.find_min' _ (by rw [he]; trivial)
  exact hf.trans (ht.trans (T.initial_work_le B hB))

end ThreeStages

end SparseIrred.UpperBounds.Section4
