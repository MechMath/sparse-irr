import SparseIrred.UpperBounds.Section4.BinaryInput

/-! # Canonical binary views of every decoded input, including malformed strings -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

def binaryInputPrime (s : List Bool) : List Bool := inputPrimeStr (canonicalInputStr s)
def binaryInputModulus (s : List Bool) : List Bool := inputModulusStr (canonicalInputStr s)
def binaryInputTerms (s : List Bool) : List Bool := inputTermsStr (canonicalInputStr s)

@[simp] theorem binaryInputPrime_eq (s : List Bool) :
    binaryInputPrime s = encNat (Input.decode s).field.characteristic := by
  simp [binaryInputPrime, canonicalInputStr_eq, inputPrimeStr, Input.encode, canonBits]

@[simp] theorem binaryInputModulus_eq (s : List Bool) :
    binaryInputModulus s = encodeNumerals (Input.decode s).field.modulus := by
  simp [binaryInputModulus, canonicalInputStr_eq, inputModulusStr, Input.encode]

@[simp] theorem binaryInputTerms_eq (s : List Bool) :
    binaryInputTerms s = frame ((Input.decode s).terms.map encodeTerm) := by
  simp [binaryInputTerms, canonicalInputStr_eq, inputTermsStr, Input.encode]

theorem cobham_binaryInputPrime {n : ℕ} {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ binaryInputPrime (s u) :=
  cobham_canonBits_comp (cobham_pairFst_comp (cobham_canonicalInputStr hs))

theorem cobham_binaryInputModulus {n : ℕ} {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ binaryInputModulus (s u) :=
  cobham_pairFst_comp (cobham_pairSnd_comp (cobham_canonicalInputStr hs))

theorem cobham_binaryInputTerms {n : ℕ} {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ binaryInputTerms (s u) :=
  cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_canonicalInputStr hs))

end SparseIrred.UpperBounds.Section4
