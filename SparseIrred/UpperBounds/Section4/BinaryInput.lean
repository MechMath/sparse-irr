import SparseIrred.UpperBounds.Section4.BinaryList
import SparseIrred.UpperBounds.Section4.BinaryAddressBasic
import SparseIrred.UpperBounds.Section4.HeaderBounds

/-!
# Binary input normalization and structural validation

These are actual list/string programs, with Cobham proofs on every bit string.
Malformed framing, noncanonical numerals, and inconsistent vector sizes are
checked without constructing a finite-field structure or deciding irreducibility.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith
open scoped BigOperators

def inputPrimeStr (s : List Bool) : List Bool := canonBits (pairFst s)
def inputModulusStr (s : List Bool) : List Bool := pairFst (pairSnd s)
def inputTermsStr (s : List Bool) : List Bool := pairSnd (pairSnd s)

def canonicalTermStr (s : List Bool) : List Bool :=
  pair (canonicalNumeralsStr (pairFst s)) (canonBits (pairSnd s))

theorem canonicalTermStr_length (s : List Bool) : (canonicalTermStr s).length ≤ s.length + 2 := by
  have h := pair_payloads_length s
  have hc := canonicalNumeralsStr_length (pairFst s)
  have he := length_canonBits_le (pairSnd s)
  rw [canonicalTermStr, pair_length]
  omega

theorem cobham_canonicalTermStr {n : ℕ} {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ canonicalTermStr (s u) :=
  cobham_pair_comp (cobham_canonicalNumeralsStr (cobham_pairFst_comp hs))
    (cobham_canonBits_comp (cobham_pairSnd_comp hs))

theorem canonicalTermStr_eq (s : List Bool) : canonicalTermStr s = encodeTerm (decodeTerm s) := by
  simp only [canonicalTermStr, canonicalNumeralsStr, mapBlocks, canonBits, encodeTerm,
    decodeTerm, encodeNumerals, decodeNumerals, List.map_map, Function.comp_def]
  rfl

def canonicalInputStr (s : List Bool) : List Bool :=
  pair (inputPrimeStr s)
    (pair (canonicalNumeralsStr (inputModulusStr s)) (mapBlocks canonicalTermStr (inputTermsStr s)))

theorem canonicalInputStr_eq (s : List Bool) : canonicalInputStr s = (Input.decode s).encode := by
  simp only [canonicalInputStr, Input.encode, Input.decode, inputPrimeStr, inputModulusStr,
    inputTermsStr, encodeNumerals, decodeNumerals, canonicalNumeralsStr, mapBlocks,
    List.map_map, Function.comp_def, canonBits, canonicalTermStr_eq]
  have hc : (fun x ↦ encodeTerm (decodeTerm x)) = canonicalTermStr :=
    funext fun x ↦ (canonicalTermStr_eq x).symm
  rw [hc]
  rfl

theorem cobham_canonicalInputStr {n : ℕ} {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ canonicalInputStr (s u) := by
  have ht := cobham_mapBlocks (n := 0) (cobham_canonicalTermStr (.proj 0))
    (Polynomial.X + Polynomial.C 2) (by intro u; simpa using canonicalTermStr_length (u 0))
  have hterms := (Cobham.comp ht (fun _ : Fin 1 ↦
    cobham_pairSnd_comp (cobham_pairSnd_comp hs))).of_eq (fun _ ↦ rfl)
  exact cobham_pair_comp (cobham_canonBits_comp (cobham_pairFst_comp hs))
    (cobham_pair_comp
      (cobham_canonicalNumeralsStr (cobham_pairFst_comp (cobham_pairSnd_comp hs))) hterms)

def canonicalInputFlag (s : List Bool) : List Bool := Cobham.eqFlag (canonicalInputStr s) s

theorem canonicalInputFlag_correct (s : List Bool) :
    canonicalInputFlag s = [true] ↔ (Input.decode s).encode = s := by
  rw [canonicalInputFlag, Cobham.eqFlag_eq_true_iff, canonicalInputStr_eq]

theorem cobham_canonicalInputFlag {n : ℕ} {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ canonicalInputFlag (s u) := Cobham.eqFlag_mem (cobham_canonicalInputStr hs) hs

def allDigitsBelowStr (p s : List Bool) : List Bool :=
  foldBlocks (fun acc b ↦ andBit acc (ltBits b p)) [true] s

theorem cobham_allDigitsBelowStr {n : ℕ} {p s : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hs : Cobham s) : Cobham fun u ↦ allDigitsBelowStr (p u) (s u) := by
  have hf := cobham_foldBlocks (n := 1)
    (Cobham.andFn (.proj 0) (cobham_ltBits_comp (.proj 1) (.proj 2)))
    (.const [true]) 1 (by
      intro u
      have hlen : (andBit (u 0) (ltBits (u 1) (u 2))).length = 1 := by
        cases h : u 0 with
        | nil => rfl
        | cons b bs => cases b <;> rcases ltBits_flag (u 1) (u 2) with he | he <;>
          simp [andBit, caseBit₀, he]
      rw [hlen]
      omega)
  exact (Cobham.comp hf (gs := fun j u ↦ (Fin.cons (s u) (fun _ ↦ p u) :
    Fin 2 → List Bool) j) (fun j ↦ Fin.cases hs (fun _ ↦ hp) j)).of_eq (fun _ ↦ rfl)

theorem allDigitsBelowStr_frame (p : ℕ) (as : List ℕ) :
    allDigitsBelowStr (encNat p) (encodeNumerals as) =
      [as.all (fun a ↦ decide (a < p))] := by
  have hfold (bs : List ℕ) (b : Bool) :
      (bs.map encNat).foldl (fun acc a ↦ andBit acc (ltBits a (encNat p))) [b] =
        [b && bs.all (fun a ↦ decide (a < p))] := by
    induction bs generalizing b with
    | nil => simp
    | cons a bs ih =>
      have hlt : ltBits (encNat a) (encNat p) = [decide (a < p)] := by
        rcases ltBits_flag (encNat a) (encNat p) with h | h
        · have hp := (ltBits_eq_true_iff _ _).mp h
          simp only [decNat_encNat] at hp
          simp [hp, h]
        · have hp : ¬a < p := by
            intro hp
            have := (ltBits_eq_true_iff (encNat a) (encNat p)).mpr (by simpa using hp)
            rw [h] at this
            contradiction
          simp [hp, h]
      simp only [List.map_cons, List.foldl_cons, hlt, andBit_single, ih, List.all_cons]
      simp [Bool.and_assoc]
  rw [allDigitsBelowStr, encodeNumerals, foldBlocks_frame, hfold]
  simp

def allBlocksStr (test : List Bool → List Bool) (s : List Bool) : List Bool :=
  foldBlocks (fun acc b ↦ andBit acc (test b)) [true] s

theorem andBit_length_one (a b : List Bool) : (andBit a b).length = 1 := by
  rcases andBit_flag a b with h | h <;> rw [h] <;> rfl

theorem cobham_allBlocksStr {n : ℕ}
    {test : (Fin n → List Bool) → List Bool → List Bool}
    (ht : Cobham fun u : Fin (n + 1) → List Bool ↦ test (Fin.tail u) (u 0))
    {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ allBlocksStr (test u) (s u) := by
  have htest := (Cobham.comp ht (gs := fun i u ↦
    (Fin.tail u : Fin (n + 1) → List Bool) i)
    (fun i ↦ Cobham.proj i.succ)).of_eq (fun _ ↦ rfl)
  have hf := cobham_foldBlocks (n := n) (Cobham.andFn (.proj 0) htest) (.const [true])
    1 (by intro u; rw [andBit_length_one]; omega)
  exact (Cobham.comp hf (gs := fun i u ↦ (Fin.cons (s u) u : Fin (n + 1) → List Bool) i)
    (fun i ↦ Fin.cases hs (fun j ↦ .proj j) i)).of_eq (fun _ ↦ rfl)

theorem allBlocksStr_frame (test : List Bool → List Bool) (bs : List (List Bool)) :
    allBlocksStr test (frame bs) = [bs.all (fun b ↦ (test b).headD false)] := by
  have ha (b : Bool) (s : List Bool) : andBit [b] s = [b && s.headD false] := by
    cases b <;> cases s with
    | nil => rfl
    | cons c cs => cases c <;> rfl
  have hf (xs : List (List Bool)) (b : Bool) :
      xs.foldl (fun acc x ↦ andBit acc (test x)) [b] =
        [b && xs.all (fun x ↦ (test x).headD false)] := by
    induction xs generalizing b with
    | nil => simp
    | cons x xs ih =>
      rw [List.foldl_cons, ha, ih, List.all_cons]
      simp [Bool.and_assoc]
  rw [allBlocksStr, foldBlocks_frame, hf]
  simp

def structuralHeaderStr (p h : List Bool) : List Bool :=
  andBit (leBits (encNat 2) p)
    (andBit (allDigitsBelowStr p h) (binaryEq (lastBlockStr h) (encNat 1) [true] [false]))

theorem cobham_structuralHeaderStr {n : ℕ} {p h : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) : Cobham fun u ↦ structuralHeaderStr (p u) (h u) :=
  Cobham.andFn (cobham_leBits_comp (.const _) hp)
    (Cobham.andFn (cobham_allDigitsBelowStr hp hh)
      (cobham_binaryEq (cobham_lastBlockStr hh) (.const _) (.const _) (.const _)))

theorem structuralHeaderStr_correct (c : FieldCode) :
    structuralHeaderStr (encNat c.characteristic) (encodeNumerals c.modulus) =
      [c.structuralFlag] := by
  have hle : leBits (encNat 2) (encNat c.characteristic) = [decide (2 ≤ c.characteristic)] := by
    rcases leBits_flag (encNat 2) (encNat c.characteristic) with h | h
    · have hp := (leBits_eq_true_iff _ _).mp h
      simp only [decNat_encNat] at hp
      simp [hp, h]
    · have hp : ¬2 ≤ c.characteristic := by
        intro hp
        have := (leBits_eq_true_iff (encNat 2) (encNat c.characteristic)).mpr (by simpa using hp)
        rw [h] at this
        contradiction
      simp [hp, h]
  have hlast : binaryEq (lastBlockStr (encodeNumerals c.modulus)) (encNat 1) [true] [false] =
      [decide (c.modulus.getLast? = some 1)] := by
    cases he : c.modulus using List.reverseRecOn with
    | nil => decide
    | append_singleton as a ih =>
      simp [encodeNumerals, lastBlockStr_frame, List.map_append, binaryEq]
      split_ifs <;> simp_all
  rw [structuralHeaderStr, hle, allDigitsBelowStr_frame, hlast]
  simp [FieldCode.structuralFlag, andBit_single, Bool.and_assoc]

end SparseIrred.UpperBounds.Section4
