import SparseIrred.UpperBounds.Section4.StackEncoding
import Complexitylib.Encoding.Pairing

/-!
# Self-delimiting configuration encoding

Each payload is separated by the library's binary pairing code. Thus address
and scalar representations may have variable length, including out-of-range
addresses, while the representation remains injective on all typed states.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity
variable {A R : Type*}

def encodeFramedStack (encA : A → List Bool) (encR : R → List Bool) :
    List (EntryFrame A R) → List Bool
  | [] => [false]
  | f :: s => true :: pair (f.encode encA encR) (encodeFramedStack encA encR s)

def EntryConfig.framedEncode (encA : A → List Bool) (encR : R → List Bool) :
    EntryConfig A R → List Bool
  | .eval a s => false :: pair (encA a) (encodeFramedStack encA encR s)
  | .ret v s => true :: pair (encR v) (encodeFramedStack encA encR s)

private theorem frameEncode_injective (encA : A → List Bool) (encR : R → List Bool)
    (hA : Function.Injective encA) (hR : Function.Injective encR) :
    Function.Injective (EntryFrame.encode encA encR) := by
  intro f g h
  cases f <;> cases g <;>
    simp only [EntryFrame.encode, List.cons_append, List.nil_append, List.cons.injEq,
      Bool.false_eq_true, Bool.true_eq_false, false_and, and_false, true_and] at h
  all_goals try contradiction
  · rename_i op a op' b
    have hab := hA h.2
    have hop : op = op' := by cases op <;> cases op' <;> simp_all [BinaryOp.code]
    subst_vars; rfl
  · rename_i op a op' b
    have hab := hR h.2
    have hop : op = op' := by cases op <;> cases op' <;> simp_all [BinaryOp.code]
    subst_vars; rfl

theorem encodeFramedStack_injective (encA : A → List Bool) (encR : R → List Bool)
    (hA : Function.Injective encA) (hR : Function.Injective encR) :
    Function.Injective (encodeFramedStack encA encR) := by
  intro s
  induction s with
  | nil => intro t h; cases t <;> simp_all [encodeFramedStack]
  | cons f s ih =>
    intro t h
    cases t with
    | nil => simp [encodeFramedStack] at h
    | cons g t =>
      simp only [encodeFramedStack, List.cons.injEq, true_and] at h
      obtain ⟨hf, ht⟩ := pair_inj h
      exact congrArg₂ List.cons (frameEncode_injective encA encR hA hR hf) (ih ht)

theorem EntryConfig.framedEncode_injective (encA : A → List Bool) (encR : R → List Bool)
    (hA : Function.Injective encA) (hR : Function.Injective encR) :
    Function.Injective (EntryConfig.framedEncode encA encR) := by
  intro c d h
  cases c <;> cases d <;>
    simp only [framedEncode, List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false,
      false_and, true_and] at h
  all_goals try contradiction
  · obtain ⟨ha, hs⟩ := pair_inj h
    exact congrArg₂ EntryConfig.eval (hA ha) (encodeFramedStack_injective encA encR hA hR hs)
  · obtain ⟨hv, hs⟩ := pair_inj h
    exact congrArg₂ EntryConfig.ret (hR hv) (encodeFramedStack_injective encA encR hA hR hs)

theorem encodeFramedStack_length_le (encA : A → List Bool) (encR : R → List Bool)
    (B : A → Prop) (w : ℕ) (hA : ∀ a, B a → (encA a).length ≤ w)
    (hR : ∀ r, (encR r).length ≤ w) (s : List (EntryFrame A R))
    (hs : ∀ f ∈ s, f.Addresses B) :
    (encodeFramedStack encA encR s).length ≤ (2 * w + 7) * s.length + 1 := by
  induction s with
  | nil => simp [encodeFramedStack]
  | cons f s ih =>
    have hi := ih (fun g hg ↦ hs g (by simp [hg]))
    have hf := hs f (by simp)
    have hw : (f.encode encA encR).length ≤ w + 2 := by
      cases f with
      | left op a => have := hA a hf; simpa [EntryFrame.encode] using this
      | right op r => have := hR r; simpa [EntryFrame.encode] using this
    simp only [encodeFramedStack, List.length_cons, pair_length]
    nlinarith

theorem EntryConfig.framedEncode_length_le (encA : A → List Bool) (encR : R → List Bool)
    (B : A → Prop) (w : ℕ) (hA : ∀ a, B a → (encA a).length ≤ w)
    (hR : ∀ r, (encR r).length ≤ w) (c : EntryConfig A R) (hc : c.Addresses B) :
    (c.framedEncode encA encR).length ≤ 2 * w + (2 * w + 7) * c.stack.length + 4 := by
  cases c with
  | eval a s =>
    have hi := encodeFramedStack_length_le encA encR B w hA hR s hc.2
    have ha := hA a hc.1
    simp only [framedEncode, List.length_cons, pair_length, stack]
    omega
  | ret v s =>
    have hi := encodeFramedStack_length_le encA encR B w hA hR s hc
    have hv := hR v
    simp only [framedEncode, List.length_cons, pair_length, stack]
    omega

end SparseIrred.UpperBounds.Section4
