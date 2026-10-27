import SparseIrred.UpperBounds.Section4.BinaryAddressCombinators
import SparseIrred.UpperBounds.Section4.EntryMachineUniformEncoding

/-! # Polynomial-time binary instructions for the trial-division preflight machine -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd

def binaryPrimeLeaf (p query : List Bool) : List Bool :=
  let i := pairFst query
  binaryLt i (encNat 2) (binaryValue [true, false, false])
    (binaryLt i p
      (binaryEq (modBits p i) (encNat 0) (binaryValue [true, false, true])
        (binaryValue [true, false, false])) (binaryValue [true, false, false]))

def primeInstructionStr (p addr : List Bool) : List Bool :=
  binaryOrInstruction (binaryPrimeLeaf p) p [] addr

theorem binaryPrimeLeaf_eq (p i : ℕ) :
    binaryPrimeLeaf (encNat p) (pair (encNat i) []) =
      binaryValue [true, false, divisorFlag p i] := by
  simp only [binaryPrimeLeaf, pairFst_pair, binaryLt, decNat_encNat]
  by_cases hi : i < 2
  · have hn : ¬2 ≤ i := by omega
    simp [hi, hn, divisorFlag]
  · by_cases hip : i < p
    · have hpos : i ≠ 0 := by omega
      have hm := decNat_modBits (encNat p) (encNat i) (by simpa using hpos)
      by_cases hz : p % i = 0 <;>
        simp [hi, hip, hz, binaryEq, hm, divisorFlag, show 2 ≤ i by omega]
    · simp [hi, hip, divisorFlag]

theorem primeInstructionStr_eq (p : ℕ) (a : PrimeAddress p) :
    primeInstructionStr (encNat p) (primeAddressCode p a) =
      ((primeDivisorProgram p).instruction a).binaryCode (primeAddressCode p)
        (DecisionScalar.binaryCode (fun x : ZMod 2 ↦ encNat x.val)) := by
  apply binaryOrInstruction_eq
  · intro; rfl
  · intro i a
    cases a
    exact binaryPrimeLeaf_eq p i.val

theorem cobham_binaryPrimeLeaf {n : ℕ} {p query : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hq : Cobham query) :
    Cobham fun v ↦ binaryPrimeLeaf (p v) (query v) :=
  cobham_binaryLt (cobham_pairFst_comp hq) (.const (encNat 2)) (.const _)
    (cobham_binaryLt (cobham_pairFst_comp hq) hp
      (cobham_binaryEq (cobham_modBits_comp hp (cobham_pairFst_comp hq)) (.const (encNat 0))
        (.const _) (.const _)) (.const _))

theorem cobham_primeInstructionStr {n : ℕ} {p addr : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ha : Cobham addr) :
    Cobham fun v ↦ primeInstructionStr (p v) (addr v) :=
  cobham_binaryOrInstruction (fun _ hq ↦ cobham_binaryPrimeLeaf hp hq) hp (.const []) ha

theorem primeInstructionStr_mem_FP :
    (fun s ↦ primeInstructionStr (pairFst s) (pairSnd s)) ∈ FP :=
  CobhamFP_subset_FP (cobham_primeInstructionStr (cobham_pairFst_comp (.proj 0))
    (cobham_pairSnd_comp (.proj 0)))

end SparseIrred.UpperBounds.Section4
