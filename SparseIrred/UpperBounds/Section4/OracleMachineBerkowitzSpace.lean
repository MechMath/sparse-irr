import SparseIrred.UpperBounds.Section4.OracleMachineScalarCompiler
import SparseIrred.UpperBounds.Section4.EntryMachineEncodedBounds

/-!
# Input-polynomial bounds for the actual Berkowitz controller representation

The original matrix input is kept next to the continuation, so every query can
include it. Dimensions remain binary; no dense matrix or sequence is stored.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Matrix

variable {R : Type} [CommRing R] {n : ℕ}

def berkowitzOracleControllerCode (params : List Bool) (encR : R → List Bool)
    (c : EntryConfig (BerkowitzAddress n) R) : List Bool :=
  pair params (c.framedEncode BerkowitzAddress.binaryCode encR)

private theorem succ_size_le (n L : ℕ) (hn : n.size ≤ L) : (n + 1).size ≤ L + 1 := by
  apply Nat.size_le.mpr
  have h := Nat.size_le.mp hn
  have hp : 0 < 2 ^ L := pow_pos (by omega) _
  rw [pow_succ]
  omega

/-- The controller stack is polynomial in the binary matrix dimension. -/
theorem berkowitzProgram_rank_input (A : Matrix (Fin n) (Fin n) R)
    (L : ℕ) (hn : n.size ≤ L) :
    (berkowitzProgram A).rank .initial ≤ 100 * (L + 3) ^ 4 := by
  have hsize := succ_size_le n L hn
  have hlog : (n + 1).log2 ≤ L + 1 := by
    have h := (Nat.log2_lt (by omega : n + 1 ≠ 0)).mpr (Nat.size_le.mp hsize)
    omega
  have hr := berkowitzProgram_rank_initial A
  unfold berkowitzStackBound at hr
  nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 4)]

/-- Every suspended or active controller configuration has an explicit polynomial bit bound. -/
theorem berkowitzOracleControllerCode_length (A : Matrix (Fin n) (Fin n) R)
    (params : List Bool) (encR : R → List Bool) (L : ℕ)
    (hp : params.length ≤ L) (hn : n.size ≤ L)
    (hscalar : ∀ v, (encR v).length ≤ 2 * L ^ 2 + 2 * L) (t : ℕ) :
    (berkowitzOracleControllerCode params encR
      ((berkowitzProgram A).step^[t] (.eval .initial []))).length ≤
      1000000 * (L + 3) ^ 8 := by
  have hstate := berkowitzProgram_addresses_bounded A t
  have hrank := berkowitzProgram_rank_input A L hn
  have hstack := (berkowitzProgram A).stack_length_iterate_le .initial t
  have hsize := succ_size_le n L hn
  have haddr : ∀ a : BerkowitzAddress n, a.Bounded →
      a.binaryCode.length ≤ 200 * (L + 3) ^ 4 := by
    intro a ha
    have h := a.binaryCode_length_of_bounded (n + 1) ha le_rfl
    nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 4)]
  have hval : ∀ v, (encR v).length ≤ 200 * (L + 3) ^ 4 := by
    intro v
    have h := hscalar v
    nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 4)]
  have hw := EntryConfig.framedEncode_length_le _ _ _ (200 * (L + 3) ^ 4)
    haddr hval _ hstate
  simp only [berkowitzOracleControllerCode, pair_length]
  have hmul := Nat.mul_le_mul_left (2 * (200 * (L + 3) ^ 4) + 7)
    (hstack.trans hrank)
  have h1 : 1 ≤ (L + 3) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hL : L ≤ (L + 3) ^ 4 := by nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 4)]
  have heq : (L + 3) ^ 8 = ((L + 3) ^ 4) ^ 2 := by ring
  rw [heq]
  nlinarith

/-- Header bits and all field-element bits can be included in a larger polynomial ruler. -/
theorem berkowitzController_space_of_ruler (A : Matrix (Fin n) (Fin n) R)
    (params : List Bool) (encR : R → List Bool) (L : ℕ)
    (hp : params.length ≤ L) (hn : n.size ≤ L)
    (hscalar : ∀ v, (encR v).length ≤ 2 * L ^ 2 + 2 * L) :
    (∀ t, (berkowitzOracleControllerCode params encR
      ((berkowitzProgram A).step^[t] (.eval .initial []))).length ≤ 1000000 * (L + 3) ^ 8) ∧
    (berkowitzProgram A).rank .initial ≤ 100 * (L + 3) ^ 4 :=
  ⟨berkowitzOracleControllerCode_length A params encR L hp hn hscalar,
    berkowitzProgram_rank_input A L hn⟩

end SparseIrred.UpperBounds.Section4
