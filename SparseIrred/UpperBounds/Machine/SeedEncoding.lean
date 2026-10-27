import SparseIrred.UpperBounds.Machine.ExecutableWitness
import SparseDivComplexity.Encoding
import Complexitylib.Classes.EventProb

/-!
# Concrete fixed-width random-seed decoding

The random tape is parsed as three mode bits, `m` prime bits, `m` residue bits,
and two single-bit tags. Numerals are least-significant-bit first. The parser is
explicit; its bijectivity is proved from fixed-width binary decoding injectivity.
Consequently uniform seed counting agrees exactly with the paper's witness domain.
-/

open Complexity SparseDiv SparseDiv.Appendix

namespace SparseIrred.UpperBounds

/-- Binary decoding is injective when the width is fixed, including leading zero bits. -/
theorem decNat_injective_of_length {s t : List Bool} (hlen : s.length = t.length)
    (hval : decNat s = decNat t) : s = t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all
  | cons b s ih =>
    cases t with
    | nil => simp at hlen
    | cons c t =>
      have hlen' : s.length = t.length := by simpa using hlen
      cases b <;> cases c <;> simp only [decNat_cons, Bool.false_eq_true,
        ↓reduceIte, zero_add] at hval
      · exact congrArg (List.cons false) (ih hlen' (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih hlen' (by omega))

private theorem seed_slice_length {n : ℕ} (seed : Fin n → Bool) (start width : ℕ)
    (h : start + width ≤ n) :
    (((List.ofFn seed).drop start).take width).length = width := by
  simp only [List.length_take, List.length_drop, List.length_ofFn]
  omega

private theorem seed_slice_value_lt {n : ℕ} (seed : Fin n → Bool) (start width : ℕ)
    (h : start + width ≤ n) :
    decNat (((List.ofFn seed).drop start).take width) < 2 ^ width := by
  simpa only [seed_slice_length seed start width h] using
    decNat_lt_two_pow_length (((List.ofFn seed).drop start).take width)

/-- The concrete Section 3.7 parser, with bit order `mode,p,a,b,coin`. -/
def seedPrimeChoices (m : ℕ) (seed : Fin (2 * m + 5) → Bool) :
    Fin 8 × PrimeWitness (2 ^ m) × Bool :=
  let s := List.ofFn seed
  (⟨decNat (s.take 3), by
      change decNat ((List.ofFn seed).take 3) < 8
      have h := seed_slice_value_lt seed 0 3 (by omega)
      norm_num only [List.drop_zero] at h
      exact h⟩,
    (⟨decNat ((s.drop 3).take m), seed_slice_value_lt seed 3 m (by omega)⟩,
      ⟨decNat ((s.drop (3 + m)).take m), seed_slice_value_lt seed (3 + m) m (by omega)⟩,
      s.getD (3 + 2 * m) false), s.getD (4 + 2 * m) false)

private theorem seed_slice_eq_at {n : ℕ} {s t : Fin n → Bool}
    {start width i : ℕ} (h : ((List.ofFn s).drop start).take width =
      ((List.ofFn t).drop start).take width)
    (hstart : start ≤ i) (hwidth : i < start + width) (hi : i < n) :
    s ⟨i, hi⟩ = t ⟨i, hi⟩ := by
  have hs : i - start < (((List.ofFn s).drop start).take width).length := by
    simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  have ht : i - start < (((List.ofFn t).drop start).take width).length := by
    simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  have heq := congrArg (fun l : List Bool ↦ l.getD (i - start) false) h
  rw [List.getD_eq_getElem _ _ hs, List.getD_eq_getElem _ _ ht] at heq
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn] at heq
  simpa only [Nat.add_sub_of_le hstart] using heq

private theorem seed_getD_eq {n : ℕ} (seed : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn seed).getD i false = seed ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

/-- Every random bit can be recovered from the five decoded components. -/
theorem seedPrimeChoices_injective (m : ℕ) : Function.Injective (seedPrimeChoices m) := by
  intro s t h
  have hm : decNat ((List.ofFn s).take 3) = decNat ((List.ofFn t).take 3) :=
    congrArg (fun w ↦ w.1.val) h
  have hp : decNat (((List.ofFn s).drop 3).take m) =
      decNat (((List.ofFn t).drop 3).take m) := congrArg (fun w ↦ w.2.1.1.val) h
  have ha : decNat (((List.ofFn s).drop (3 + m)).take m) =
      decNat (((List.ofFn t).drop (3 + m)).take m) := congrArg (fun w ↦ w.2.1.2.1.val) h
  have hb : (List.ofFn s).getD (3 + 2 * m) false =
      (List.ofFn t).getD (3 + 2 * m) false := congrArg (fun w ↦ w.2.1.2.2) h
  have hc : (List.ofFn s).getD (4 + 2 * m) false =
      (List.ofFn t).getD (4 + 2 * m) false := congrArg (fun w ↦ w.2.2) h
  have hm' := decNat_injective_of_length (by simp :
    ((List.ofFn s).take 3).length = ((List.ofFn t).take 3).length) hm
  have hp' := decNat_injective_of_length (by simp :
    (((List.ofFn s).drop 3).take m).length = (((List.ofFn t).drop 3).take m).length) hp
  have ha' := decNat_injective_of_length (by simp :
    (((List.ofFn s).drop (3 + m)).take m).length =
      (((List.ofFn t).drop (3 + m)).take m).length) ha
  funext i
  by_cases h3 : i.val < 3
  · exact seed_slice_eq_at (start := 0) (width := 3)
      (by simpa only [List.drop_zero] using hm') (by omega) (by omega) i.isLt
  by_cases hpm : i.val < 3 + m
  · exact seed_slice_eq_at hp' (by omega) hpm i.isLt
  by_cases ham : i.val < 3 + 2 * m
  · exact seed_slice_eq_at ha' (by omega) (by omega) i.isLt
  by_cases hib : i.val = 3 + 2 * m
  · have hi : i = ⟨3 + 2 * m, by omega⟩ := Fin.ext hib
    rw [hi]
    simpa only [seed_getD_eq s (3 + 2 * m) (by omega),
      seed_getD_eq t (3 + 2 * m) (by omega)] using hb
  · have hic : i.val = 4 + 2 * m := by omega
    have hi : i = ⟨4 + 2 * m, by omega⟩ := Fin.ext hic
    rw [hi]
    simpa only [seed_getD_eq s (4 + 2 * m) (by omega),
      seed_getD_eq t (4 + 2 * m) (by omega)] using hc

theorem seedPrimeChoices_bijective (m : ℕ) : Function.Bijective (seedPrimeChoices m) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨seedPrimeChoices_injective m, ?_⟩
  rw [card_finArrowBool, primeWitness_choice_count]

/-- This equivalence has the explicit bit-slicing parser as its forward function. -/
noncomputable def seedPrimeChoicesEquiv (m : ℕ) :
    (Fin (2 * m + 5) → Bool) ≃ (Fin 8 × PrimeWitness (2 ^ m) × Bool) :=
  Equiv.ofBijective (seedPrimeChoices m) (seedPrimeChoices_bijective m)

@[simp] theorem seedPrimeChoicesEquiv_apply (m : ℕ) (seed : Fin (2 * m + 5) → Bool) :
    seedPrimeChoicesEquiv m seed = seedPrimeChoices m seed := rfl

/-- Exact finite counts are preserved by the concrete random-tape parser. -/
theorem witnessCount_seedPrimeChoices (m : ℕ)
    (R : (Fin 8 × PrimeWitness (2 ^ m) × Bool) → Prop) [DecidablePred R] :
    witnessCount (fun seed ↦ R (seedPrimeChoices m seed)) = witnessCount R := by
  classical
  simp only [witnessCount_eq_sum]
  exact Fintype.sum_equiv (seedPrimeChoicesEquiv m) _ _ (fun _ ↦ rfl)

/-- Uniform seed probability equals the paper's finite accepting-path fraction. -/
theorem eventProb_seedPrimeChoices (m : ℕ)
    (R : (Fin 8 × PrimeWitness (2 ^ m) × Bool) → Prop) [DecidablePred R] :
    eventProb (Finset.univ.filter fun seed ↦ R (seedPrimeChoices m seed)) =
      (witnessCount R : ℚ) / 2 ^ (2 * m + 5) := by
  unfold eventProb
  rw [show (Finset.univ.filter fun seed ↦ R (seedPrimeChoices m seed)).card =
    witnessCount R from witnessCount_seedPrimeChoices m R]

end SparseIrred.UpperBounds
