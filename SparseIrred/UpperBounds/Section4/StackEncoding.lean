import SparseIrred.UpperBounds.Section4.StackEvaluator

/-!
# Binary space used by address-stack executions

The width calculation counts the control bits, every stored address and every
stored field value. Its invariant covers all intermediate configurations.
-/

namespace SparseIrred.UpperBounds.Section4

variable {A R : Type*}

def EntryFrame.Addresses (B : A → Prop) : EntryFrame A R → Prop
  | .left _ r => B r
  | .right _ _ => True

def EntryConfig.Addresses (B : A → Prop) : EntryConfig A R → Prop
  | .eval a stack => B a ∧ ∀ f ∈ stack, f.Addresses B
  | .ret _ stack => ∀ f ∈ stack, f.Addresses B

variable [Add R] [Mul R]

theorem EntryProgram.addresses_step (P : EntryProgram A R) (B : A → Prop)
    (hB : ∀ a op l r, B a → P.instruction a = .branch op l r → B l ∧ B r)
    (c : EntryConfig A R) (hc : c.Addresses B) : (P.step c).Addresses B := by
  cases c with
  | eval a stack =>
    cases he : P.instruction a with
    | value v => simpa only [step, he, EntryConfig.Addresses] using hc.2
    | branch op l r =>
      have hd := hB _ _ _ _ hc.1 he
      simp only [step, he, EntryConfig.Addresses, List.mem_cons, forall_eq_or_imp,
        EntryFrame.Addresses]
      exact ⟨hd.1, hd.2, hc.2⟩
  | ret v stack =>
    cases stack with
    | nil => exact hc
    | cons f stack =>
      cases f <;> simp only [EntryConfig.Addresses, List.mem_cons, forall_eq_or_imp,
        EntryFrame.Addresses] at hc
      · simpa only [step, EntryConfig.Addresses, List.mem_cons, forall_eq_or_imp,
          EntryFrame.Addresses, true_and] using hc
      · exact hc.2

theorem EntryProgram.addresses_iterate (P : EntryProgram A R) (B : A → Prop)
    (hB : ∀ a op l r, B a → P.instruction a = .branch op l r → B l ∧ B r)
    (a : A) (ha : B a) (t : ℕ) : (P.step^[t] (.eval a [])).Addresses B := by
  induction t with
  | zero => exact ⟨ha, by simp⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact P.addresses_step B hB _ ih

def BinaryOp.code : BinaryOp → Bool
  | .add => false
  | .mul => true

/-- Two control bits distinguish the frame kind and the arithmetic operation. -/
def EntryFrame.encode (encA : A → List Bool) (encR : R → List Bool) :
    EntryFrame A R → List Bool
  | .left op r => [false, op.code] ++ encA r
  | .right op l => [true, op.code] ++ encR l

/-- Each stack entry has a continuation marker; a final zero terminates the stack. -/
def encodeEntryStack (encA : A → List Bool) (encR : R → List Bool) :
    List (EntryFrame A R) → List Bool
  | [] => [false]
  | f :: stack => true :: (f.encode encA encR ++ encodeEntryStack encA encR stack)

/-- The active address and returned scalar share a register distinguished by one bit. -/
def EntryConfig.encode (encA : A → List Bool) (encR : R → List Bool) :
    EntryConfig A R → List Bool
  | .eval a stack => false :: (encA a ++ encodeEntryStack encA encR stack)
  | .ret v stack => true :: (encR v ++ encodeEntryStack encA encR stack)

theorem encodeEntryStack_length_le (encA : A → List Bool) (encR : R → List Bool)
    (B : A → Prop) (w : ℕ) (hA : ∀ a, B a → (encA a).length ≤ w)
    (hR : ∀ r, (encR r).length ≤ w) (stack : List (EntryFrame A R))
    (hs : ∀ f ∈ stack, f.Addresses B) :
    (encodeEntryStack encA encR stack).length ≤ (w + 3) * stack.length + 1 := by
  induction stack with
  | nil => simp [encodeEntryStack]
  | cons f stack ih =>
    have hf := hs f (by simp)
    have hst : ∀ g ∈ stack, g.Addresses B := fun g hg ↦ hs g (by simp [hg])
    have hi := ih hst
    have hlen : (f.encode encA encR).length ≤ w + 2 := by
      cases f with
      | left op a => have := hA a hf; simpa [EntryFrame.encode] using this
      | right op r => have := hR r; simpa [EntryFrame.encode] using this
    simp only [encodeEntryStack, List.length_cons, List.length_append]
    nlinarith

theorem EntryConfig.encode_length_le (encA : A → List Bool) (encR : R → List Bool)
    (B : A → Prop) (w : ℕ) (hA : ∀ a, B a → (encA a).length ≤ w)
    (hR : ∀ r, (encR r).length ≤ w) (c : EntryConfig A R) (hc : c.Addresses B) :
    (c.encode encA encR).length ≤ w + (w + 3) * c.stack.length + 2 := by
  cases c with
  | eval a stack =>
    have hh := encodeEntryStack_length_le encA encR B w hA hR stack hc.2
    have ha := hA a hc.1
    simp only [encode, List.length_cons, List.length_append, EntryConfig.stack]
    omega
  | ret v stack =>
    have hh := encodeEntryStack_length_le encA encR B w hA hR stack hc
    have hv := hR v
    simp only [encode, List.length_cons, List.length_append, EntryConfig.stack]
    omega

/-- Concrete binary width of every intermediate configuration. -/
theorem EntryProgram.encoded_width_iterate (P : EntryProgram A R) (encA : A → List Bool)
    (encR : R → List Bool) (B : A → Prop) (w : ℕ)
    (hA : ∀ a, B a → (encA a).length ≤ w) (hR : ∀ r, (encR r).length ≤ w)
    (hB : ∀ a op l r, B a → P.instruction a = .branch op l r → B l ∧ B r)
    (a : A) (ha : B a) (t : ℕ) :
    ((P.step^[t] (.eval a [])).encode encA encR).length ≤ w + (w + 3) * P.rank a + 2 := by
  have hwidth := EntryConfig.encode_length_le encA encR B w hA hR
    (P.step^[t] (.eval a [])) (P.addresses_iterate B hB a ha t)
  have hdepth := P.stack_length_iterate_le a t
  exact hwidth.trans (by gcongr)

end SparseIrred.UpperBounds.Section4
