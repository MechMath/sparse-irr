import SparseIrred.UpperBounds.Section4.EntryMachineBounds
import SparseIrred.UpperBounds.Section4.StackFaithful

/-! # Faithful fixed-width address registers -/

namespace SparseIrred.UpperBounds.Section4

private theorem fixedBlocks_injective (w : ℕ) (s t : List ℕ) (hlen : s.length = t.length)
    (hs : ∀ v ∈ s, v < 2 ^ w) (ht : ∀ v ∈ t, v < 2 ^ w)
    (h : (s.map (fixedWord w)).flatten = (t.map (fixedWord w)).flatten) : s = t := by
  induction s generalizing t with
  | nil => simpa using hlen.symm
  | cons a s ih =>
    cases t with
    | nil => simp at hlen
    | cons b t =>
      simp only [List.map_cons, List.flatten_cons] at h
      have hab : a = b := fixedWord_injective w
        (hs a (by simp)) (ht b (by simp))
        (List.append_inj_left h (by simp))
      subst b
      congr 1
      exact ih t (by simpa using hlen) (fun v hv ↦ hs v (by simp [hv]))
        (fun v hv ↦ ht v (by simp [hv])) (List.append_cancel_left h)

/-- No distinct valid address is collapsed by the fixed-width binary code. -/
theorem ProductAddress.encode_injective {n : ℕ} (bound w : ℕ)
    (hb : bound + n < 2 ^ w) (a b : ProductAddress n)
    (ha : a.Bounded bound) (hb' : b.Bounded bound)
    (he : a.encode w = b.encode w) : a = b := by
  have ha' := a.registers_fit bound w ha hb
  have hb'' := b.registers_fit bound w hb' hb
  cases a <;> cases b <;>
    simp only [encode, List.cons_append, List.nil_append, List.cons.injEq,
      Bool.false_eq_true, Bool.true_eq_false, false_and, and_false, true_and] at he
  all_goals try contradiction
  all_goals try rfl
  all_goals
    have hregs := fixedBlocks_injective w _ _ (by simp) ha' hb'' he
    simp only [registers, List.cons.injEq, and_true] at hregs
    congr 1 <;> (try apply Fin.ext) <;> omega

end SparseIrred.UpperBounds.Section4
