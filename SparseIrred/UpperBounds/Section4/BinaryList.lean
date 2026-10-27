import SparseDivComplexity.StringArith.Blocks
import SparseDivComplexity.StringArith.DivMod

/-! # Polynomial-time framed-list loops with parameter-dependent output bounds -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith
open scoped BigOperators

theorem pairFst_payload_length : ∀ s : List Bool, 2 * (pairFst s).length ≤ s.length
  | [] => by simp [pairFst]
  | [b] => by cases b <;> simp [pairFst]
  | false :: false :: s => by have := pairFst_payload_length s; simp [pairFst]; omega
  | true :: true :: s => by have := pairFst_payload_length s; simp [pairFst]; omega
  | false :: true :: s => by simp [pairFst]
  | true :: false :: s => by simp [pairFst]

theorem pair_payloads_length (s : List Bool) :
    2 * (pairFst s).length + (pairSnd s).length ≤ s.length := by
  cases h : unpair? s with
  | none => simpa [pairSnd, h] using pairFst_payload_length s
  | some xy =>
    rcases xy with ⟨x, y⟩
    rw [eq_pair_of_unpair?_eq_some h, pairFst_pair, pairSnd_pair, pair_length]
    omega

theorem eq_frame_blocks_or_empty (s : List Bool) : s = frame (blocks s) ∨ blocks s = [] := by
  obtain ⟨bs, rem, hs, hrem⟩ := exists_frame_append s
  by_cases he : rem = []
  · subst rem
    simp only [List.append_nil] at hs
    subst s
    simp [blocks_frame]
  · right
    rw [hs]
    exact blocks_frame_append_of_bad bs he (hrem.resolve_left he)

theorem mapBlocks_length_le_of_nonincreasing (f : List Bool → List Bool)
    (hf : ∀ b, (f b).length ≤ b.length) (s : List Bool) : (mapBlocks f s).length ≤ s.length := by
  have hframe (bs : List (List Bool)) : (frame (bs.map f)).length ≤ (frame bs).length := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons, frame_cons, List.length_append, delimit_length]
      have := hf b
      omega
  rcases eq_frame_blocks_or_empty s with h | h
  · simpa only [mapBlocks, ← h] using hframe (blocks s)
  · simp [mapBlocks, h, frame_nil]

def canonicalNumeralsStr (s : List Bool) : List Bool := mapBlocks canonBits s

theorem canonicalNumeralsStr_length (s : List Bool) :
    (canonicalNumeralsStr s).length ≤ s.length :=
  mapBlocks_length_le_of_nonincreasing canonBits length_canonBits_le s

theorem cobham_canonicalNumeralsStr {n : ℕ} {s : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) : Cobham fun u ↦ canonicalNumeralsStr (s u) := by
  have h := cobham_mapBlocks (n := 0) (cobham_canonBits_comp (.proj 0)) Polynomial.X (by
    intro u
    simpa using length_canonBits_le (u 0))
  exact (Cobham.comp h (fun _ ↦ hs)).of_eq (fun _ ↦ rfl)

theorem canonicalNumeralsStr_eq (s : List Bool) :
    canonicalNumeralsStr s = frame ((blocks s).map (fun b ↦ encNat (decNat b))) := rfl

def blockCountStr (s : List Bool) : List Bool :=
  canonBits (foldBlocks (fun count _ ↦ succBits count) [] s)

theorem decNat_foldl_successor (bs : List (List Bool)) (count : List Bool) :
    decNat (bs.foldl (fun c _ ↦ succBits c) count) = decNat count + bs.length := by
  induction bs generalizing count with
  | nil => simp
  | cons b bs ih => simpa [List.foldl_cons, decNat_succBits, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (succBits count)

@[simp] theorem blockCountStr_frame (bs : List (List Bool)) :
    blockCountStr (frame bs) = encNat bs.length := by
  rw [blockCountStr, foldBlocks_frame, canonBits, decNat_foldl_successor]
  change encNat (0 + bs.length) = encNat bs.length
  rw [Nat.zero_add]

theorem cobham_blockCountStr {n : ℕ} {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ blockCountStr (s u) := by
  have hf := cobham_foldBlocks (n := 0)
    (show Cobham fun u : Fin 2 → List Bool ↦ succBits (u 0) from
      cobham_succBits_comp (.proj 0)) (Cobham.const []) 1 (by
        intro u; have := length_succBits_le (u 0); omega)
  have hc := cobham_canonBits_comp hf
  exact (Cobham.comp hc (fun _ ↦ hs)).of_eq (fun _ ↦ rfl)

def lastBlockStr (s : List Bool) : List Bool := foldBlocks (fun _ b ↦ b) [] s

@[simp] theorem lastBlockStr_frame (bs : List (List Bool)) :
    lastBlockStr (frame bs) = bs.getLast?.getD [] := by
  rw [lastBlockStr, foldBlocks_frame]
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih => simp [List.foldl_append]

theorem cobham_lastBlockStr {n : ℕ} {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ lastBlockStr (s u) := by
  have hf := cobham_foldBlocks (n := 0) (step := fun u ↦ u 1) (.proj 1)
    (Cobham.const []) 1 (by intro u; omega)
  exact (Cobham.comp hf (fun _ ↦ hs)).of_eq (fun _ ↦ rfl)

def blockIndexStep (state block : List Bool) : List Bool :=
  caseBit₀ state state (caseBit₀ (isZeroBits state.tail)
    (true :: block) (false :: canonBits (subBits state.tail [true])))

def blockAtStr (index blocks : List Bool) : List Bool :=
  let result := foldBlocks blockIndexStep (false :: index) blocks
  caseBit₀ result result.tail []

theorem blockIndexStep_length (state block : List Bool) :
    (blockIndexStep state block).length ≤ state.length + 4 * (block.length + 1) := by
  have hsub := length_subBits_le state.tail [true]
  have hcan := length_canonBits_le (subBits state.tail [true])
  have htail : state.tail.length ≤ state.length := by simp
  cases state with
  | nil => simp [blockIndexStep, caseBit₀, isZeroBits]
  | cons b bs =>
    cases b with
    | true => simp [blockIndexStep, caseBit₀]
    | false =>
      rcases isZeroBits_flag bs with h | h <;>
        simp [blockIndexStep, caseBit₀, h] <;> simp_all <;> omega

theorem cobham_blockIndexStep {n : ℕ} {s b : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hb : Cobham b) : Cobham fun u ↦ blockIndexStep (s u) (b u) :=
  Cobham.iteFn hs hs (Cobham.iteFn (cobham_isZeroBits_comp hs.tailFn)
    (cobham_cons true hb)
    (cobham_cons false (cobham_canonBits_comp (cobham_subBits_comp hs.tailFn (.const _)))))

theorem cobham_blockAtStr {n : ℕ} {i s : (Fin n → List Bool) → List Bool}
    (hi : Cobham i) (hs : Cobham s) : Cobham fun u ↦ blockAtStr (i u) (s u) := by
  have hf := cobham_foldBlocks (n := 1)
    (cobham_blockIndexStep (n := 3) (.proj 0) (.proj 1))
    (cobham_cons false (.proj 0)) 4 (fun u ↦ blockIndexStep_length _ _)
  have hc := (Cobham.comp hf (gs := fun j u ↦
    (Fin.cons (s u) (fun _ ↦ i u) : Fin 2 → List Bool) j)
    (fun j ↦ Fin.cases hs (fun _ ↦ hi) j)).of_eq (fun _ ↦ rfl)
  exact Cobham.iteFn hc hc.tailFn (.const [])

theorem blockIndexStep_found (b block : List Bool) :
    blockIndexStep (true :: b) block = true :: b := rfl

theorem foldl_blockIndexStep_found (bs : List (List Bool)) (b : List Bool) :
    bs.foldl blockIndexStep (true :: b) = true :: b := by
  induction bs with
  | nil => rfl
  | cons a bs ih => simpa only [List.foldl_cons, blockIndexStep_found] using ih

theorem foldl_blockIndexStep_pending (bs : List (List Bool)) (i : ℕ) :
    bs.foldl blockIndexStep (false :: encNat i) =
      if h : i < bs.length then true :: bs[i] else false :: encNat (i - bs.length) := by
  induction bs generalizing i with
  | nil => simp
  | cons b bs ih =>
    cases i with
    | zero => simp [List.foldl_cons, blockIndexStep, encNat, isZeroBits, caseBit₀,
        foldl_blockIndexStep_found]
    | succ i =>
      have hzero : isZeroBits (encNat (i + 1)) = [false] := by
        rcases isZeroBits_flag (encNat (i + 1)) with h | h
        · have hz := (isZeroBits_eq_true_iff _).mp h
          simp at hz
        · exact h
      have hpred : canonBits (subBits (encNat (i + 1)) [true]) = encNat i := by
        rw [canonBits, decNat_subBits, decNat_encNat]
        change encNat (i + 1 - 1) = encNat i
        simp
      have hstep : blockIndexStep (false :: encNat (i + 1)) b = false :: encNat i := by
        simp [blockIndexStep, hzero, hpred, caseBit₀]
      rw [List.foldl_cons, hstep, ih]
      simp

@[simp] theorem blockAtStr_frame (i : ℕ) (bs : List (List Bool)) :
    blockAtStr (encNat i) (frame bs) = bs.getD i [] := by
  rw [blockAtStr, foldBlocks_frame, foldl_blockIndexStep_pending]
  split_ifs with h <;> simp [h, caseBit₀, List.getD_eq_getElem, List.getD_eq_default]

/-- A framed fold whose step discards the old accumulator and has a polynomial
output bound in the current block and fixed parameters. The bound may depend on
the field header, which is essential for fixed-degree coefficient vectors. -/
theorem cobham_foldBlocks_bounded {n : ℕ}
    {step : (Fin (n + 2) → List Bool) → List Bool} (hstep : Cobham step)
    {initial : (Fin n → List Bool) → List Bool} (hinit : Cobham initial)
    (q : Polynomial ℕ)
    (hbound : ∀ u, (step u).length ≤ q.eval (∑ i, (Fin.tail u i).length)) :
    Cobham fun v : Fin (n + 1) → List Bool ↦
      foldBlocks (fun acc b ↦ step (Fin.cons acc (Fin.cons b (Fin.tail v))))
        (initial (Fin.tail v)) (v 0) := by
  have hg : Cobham fun x : Fin (n + 3) → List Bool ↦
      step (Fin.cons (x 0) (Fin.cons (x 1) (Fin.tail (Fin.tail (Fin.tail x))))) := by
    refine (Cobham.comp hstep
      (gs := fun i (x : Fin (n + 3) → List Bool) ↦
        (Fin.cons (x 0) (Fin.cons (x 1) (Fin.tail (Fin.tail (Fin.tail x)))) :
          Fin (n + 2) → List Bool) i) ?_).of_eq fun _ ↦ rfl
    intro i
    refine Fin.cases (.proj 0) (fun i ↦ Fin.cases (.proj 1) (fun j ↦ .proj j.succ.succ.succ) i) i
  have hi : Cobham fun u : Fin (n + 1) → List Bool ↦ initial (Fin.tail u) :=
    (Cobham.comp hinit fun i ↦ Cobham.proj i.succ).of_eq fun _ ↦ rfl
  have hbad : Cobham fun u : Fin (n + 1) → List Bool ↦ pair [] (initial (Fin.tail u)) :=
    cobham_pair_comp (.const []) hi
  have hq : Cobham fun u : Fin (n + 1) → List Bool ↦
      Cobham.polyLen q (List.ofFn u).flatten := Cobham.polyLen_mem _ (cobham_flattenOfFn _)
  have hr : Cobham fun u : Fin (n + 1) → List Bool ↦
      [false, false] ++ (u 0 ++ u 0) ++ initial (Fin.tail u) ++
        smash (u 0) (Cobham.polyLen q (List.ofFn u).flatten) :=
    Cobham.appendFn (Cobham.appendFn
      (Cobham.appendFn (.const _) (Cobham.appendFn (.proj 0) (.proj 0))) hi)
      (Cobham.comp₂ Cobham.smash (.proj 0) hq)
  refine (cobham_blockLoop hg hbad hi hr ?_).of_eq fun _ ↦ ?_
  · intro u k
    have htotal : (u 0).length ≤ ∑ i, (u i).length := by
      rw [Fin.sum_univ_succ]; exact Nat.le_add_right _ _
    have hb := blockStep_iterate_length_le
      (fun acc b ↦ step (Fin.cons acc (Fin.cons b (Fin.tail u))))
      (pair [] (initial (Fin.tail u))) (blockStep_pair_nil _ _ _)
      (u 0) (initial (Fin.tail u)) (q.eval (∑ i, (u i).length)) (by
        intro acc b hlen
        have ht := hbound (Fin.cons acc (Fin.cons b (Fin.tail u)))
        have hm : (∑ i : Fin (n + 1),
            ((Fin.cons b (Fin.tail u) : Fin (n + 1) → List Bool) i).length) ≤
            ∑ i, (u i).length := by
          rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
          omega
        simp only [Fin.tail_cons] at ht
        have hqmono := polynomial_eval_mono_nat q hm
        exact (ht.trans hqmono).trans (Nat.le_add_left _ _))
      (by rw [pair_length]; simp only [List.length_nil]; omega) k
    simp only [Fin.cons_zero, Fin.cons_one, Fin.tail_cons, List.length_append,
      List.length_cons, List.length_nil, smash_length, Cobham.polyLen_length,
      length_flatten_ofFn]
    omega
  · rw [foldBlocks_eq_blockLoop]
    rfl

end SparseIrred.UpperBounds.Section4
