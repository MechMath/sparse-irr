import SparseIrred.UpperBounds.Section4.StackEncoding

/-!
# Faithfulness of fixed-width stack encoding

The width theorem alone does not guarantee a usable machine representation.
Here fixed widths and injective address/scalar codes ensure that complete
configurations can be recovered uniquely, including all continuation frames.
-/

namespace SparseIrred.UpperBounds.Section4

variable {A R : Type*}

private theorem BinaryOp.code_injective : Function.Injective BinaryOp.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [BinaryOp.code]

private theorem framePrefix_injective
    (encA : A → List Bool) (encR : R → List Bool) (B : A → Prop)
    (wa wr : ℕ) (hAlen : ∀ a, (encA a).length = wa) (hRlen : ∀ r, (encR r).length = wr)
    (hA : ∀ a b, B a → B b → encA a = encA b → a = b)
    (hR : Function.Injective encR)
    (f g : EntryFrame A R) (s t : List Bool) (hf : f.Addresses B) (hg : g.Addresses B)
    (h : f.encode encA encR ++ s = g.encode encA encR ++ t) : f = g ∧ s = t := by
  cases f with
  | left op a =>
    cases g with
    | left op' b =>
      simp only [EntryFrame.encode, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      have hop := BinaryOp.code_injective h.1
      have hab := hA a b hf hg (List.append_inj_left h.2 (by rw [hAlen, hAlen]))
      subst op'; subst b
      exact ⟨rfl, List.append_cancel_left h.2⟩
    | right op' v => simp [EntryFrame.encode] at h
  | right op v =>
    cases g with
    | left op' a => simp [EntryFrame.encode] at h
    | right op' w =>
      simp only [EntryFrame.encode, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      have hop := BinaryOp.code_injective h.1
      have hvw := hR (List.append_inj_left h.2 (by rw [hRlen, hRlen]))
      subst op'; subst w
      exact ⟨rfl, List.append_cancel_left h.2⟩

/-- The terminating marker and the fixed-width frame payload make the stack code injective. -/
theorem encodeEntryStack_injective
    (encA : A → List Bool) (encR : R → List Bool) (B : A → Prop)
    (wa wr : ℕ) (hAlen : ∀ a, (encA a).length = wa) (hRlen : ∀ r, (encR r).length = wr)
    (hA : ∀ a b, B a → B b → encA a = encA b → a = b)
    (hR : Function.Injective encR)
    (s t : List (EntryFrame A R))
    (hs : ∀ f ∈ s, f.Addresses B) (ht : ∀ f ∈ t, f.Addresses B)
    (h : encodeEntryStack encA encR s = encodeEntryStack encA encR t) : s = t := by
  induction s generalizing t with
  | nil => cases t with
    | nil => rfl
    | cons g t => simp [encodeEntryStack] at h
  | cons f s ih =>
    cases t with
    | nil => simp [encodeEntryStack] at h
    | cons g t =>
      simp only [encodeEntryStack, List.cons.injEq, true_and] at h
      have he := framePrefix_injective encA encR B wa wr hAlen hRlen hA hR f g _ _
        (hs _ (by simp)) (ht _ (by simp)) h
      rw [he.1]
      congr 1
      exact ih t (fun v hv ↦ hs v (by simp [hv]))
        (fun v hv ↦ ht v (by simp [hv])) he.2

/-- Complete configurations have faithful binary encodings on the address invariant. -/
theorem EntryConfig.encode_injective
    (encA : A → List Bool) (encR : R → List Bool) (B : A → Prop)
    (wa wr : ℕ) (hAlen : ∀ a, (encA a).length = wa) (hRlen : ∀ r, (encR r).length = wr)
    (hA : ∀ a b, B a → B b → encA a = encA b → a = b)
    (hR : Function.Injective encR)
    (c d : EntryConfig A R) (hc : c.Addresses B) (hd : d.Addresses B)
    (h : c.encode encA encR = d.encode encA encR) : c = d := by
  cases c with
  | eval a s =>
    cases d with
    | eval b t =>
      simp only [encode, List.cons.injEq, true_and] at h
      have hab := hA a b hc.1 hd.1 (List.append_inj_left h (by rw [hAlen, hAlen]))
      subst b
      have hst := encodeEntryStack_injective encA encR B wa wr hAlen hRlen hA hR
        s t hc.2 hd.2 (List.append_cancel_left h)
      exact hst ▸ rfl
    | ret v t => simp [encode] at h
  | ret v s =>
    cases d with
    | eval a t => simp [encode] at h
    | ret w t =>
      simp only [encode, List.cons.injEq, true_and] at h
      have hvw := hR (List.append_inj_left h (by rw [hRlen, hRlen]))
      subst w
      have hst := encodeEntryStack_injective encA encR B wa wr hAlen hRlen hA hR
        s t hc hd (List.append_cancel_left h)
      exact hst ▸ rfl

end SparseIrred.UpperBounds.Section4
