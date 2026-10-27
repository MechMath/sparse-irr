import SparseIrred.UpperBounds.Section4.EntryMachinePolynomialEncoding
import SparseIrred.UpperBounds.Section4.UniformStages

/-!
# A fixed binary representation for the uniform three-stage machine

Running states begin with `00`, whereas the initialization input `pair [] s`
begins with `01`. The phase, original input and all stack payloads have explicit
frames. Proofs that validate a field are erased from the code, not computed by
an oracle.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith

set_option backward.isDefEq.respectTransparency false

def primeAddressCode (p : ℕ) : PrimeAddress p → List Bool :=
  OrAddress.binaryCode (fun _ _ ↦ [])

def primeConfigCode (s : List Bool) (c : (primeStage s).ReachableCfg) : List Bool :=
  c.val.framedEncode (primeAddressCode (Input.decode s).field.characteristic)
    (DecisionScalar.binaryCode (fun a : ZMod 2 ↦ encNat a.val))

def modulusConfigCode (s : List Bool) (h : (primeStage s).answer = true)
    (c : (modulusStage s h).ReachableCfg) : List Bool := by
  letI := primeFactOfStage s h
  exact c.val.framedEncode (polynomialAddressCode _ _)
    (DecisionScalar.binaryCode (fun a : ZMod (Input.decode s).field.characteristic ↦ encNat a.val))

def sparseConfigCode (s : List Bool) (h : (primeStage s).answer = true)
    (h' : (modulusStage s h).answer = true) (c : (sparseStage s h h').ReachableCfg) : List Bool := by
  letI : Fact (Input.decode s).field.Valid := ⟨validFieldOfStages s h h'⟩
  exact c.val.framedEncode (polynomialAddressCode _ _)
    (DecisionScalar.binaryCode (fun a : (Input.decode s).field.Carrier ↦
      encodeNumerals ((Input.decode s).field.encodeElement a)))

/-- This exact representation is the one used by the final local machine interface. -/
def uniformCode (s : List Bool) : (uniformStages s).State → List Bool
  | .first c => [false, false] ++ pair s ([false, false] ++ primeConfigCode s c)
  | .second h c => [false, false] ++ pair s ([false, true] ++ modulusConfigCode s h c)
  | .third h h' c => [false, false] ++ pair s ([true, false] ++ sparseConfigCode s h h' c)
  | .done b => [true, b]

@[simp] theorem uniformCode_flag (s : List Bool) (c : (uniformStages s).State) :
    (uniformCode s c).headD false = decide c.Halted := by
  cases c <;> rfl

/-- Running-state codes cannot collide with initialization inputs. -/
theorem uniformCode_ne_initial (s x : List Bool) (c : (uniformStages s).State) :
    uniformCode s c ≠ pair [] x := by
  cases c <;> simp [uniformCode, pair]

private theorem zmod2_scalar_length (a : ZMod 2) : (encNat a.val).length ≤ 2 := by
  rw [length_encNat]
  have h := ZMod.val_lt a
  have hs := Nat.size_le_size (show a.val ≤ 2 by omega)
  exact hs

theorem primeDivisorProgram_closed (p : ℕ) :
    (primeDivisorProgram p).Closed (OrAddress.Bounded (fun _ _ ↦ True)) := by
  apply orProgram_closed
  · intro i a op l r ha he
    cases he
  · intro i; trivial

private theorem log2_le_size' (n : ℕ) : n.log2 ≤ n.size := by
  by_cases h : n = 0
  · subst n; decide
  · have hh := (Nat.log2_lt h).mpr (Nat.lt_size_self n); omega

theorem primeConfigCode_length (s : List Bool) (c : (primeStage s).ReachableCfg) :
    (primeConfigCode s c).length ≤ 1000000 * (s.length + 3) ^ 8 := by
  rcases c with ⟨c, t, rfl⟩
  let p := (Input.decode s).field.characteristic
  have hp : p.size ≤ s.length := Input.decoded_characteristic_size_le s
  have hb := (primeDivisorProgram p).addresses_iterate
    (OrAddress.Bounded (fun _ _ ↦ True)) (primeDivisorProgram_closed p)
    (primeDivisorInitial p) (by change 0 + p ≤ p; omega) t
  have hs := (primeDivisorProgram p).stack_length_iterate_le (primeDivisorInitial p) t
  have hr := primeDivisorProgram_rank p
  have hl := log2_le_size' p
  have hstack : ((primeDivisorProgram p).step^[t] (.eval (primeDivisorInitial p) [])).stack.length ≤
      100 * (s.length + 3) ^ 4 := by
    nlinarith [Nat.zero_le (s.length ^ 3), Nat.zero_le (s.length ^ 4)]
  have haddr : ∀ a : PrimeAddress p, OrAddress.Bounded (fun _ _ ↦ True) a →
      (primeAddressCode p a).length ≤ 200 * (s.length + 3) ^ 4 := by
    intro a ha
    have hh := OrAddress.binaryCode_length_of_bounded (fun _ _ ↦ [])
      (fun _ _ ↦ True) 0 (by intros; rfl) a ha
    change (primeAddressCode p a).length ≤ _ at hh
    nlinarith [Nat.zero_le (s.length ^ 3), Nat.zero_le (s.length ^ 4)]
  have hval : ∀ v : DecisionScalar (ZMod 2),
      (v.binaryCode (fun a ↦ encNat a.val)).length ≤ 200 * (s.length + 3) ^ 4 := by
    intro v
    have hv := DecisionScalar.binaryCode_length (fun a : ZMod 2 ↦ encNat a.val) 2
      zmod2_scalar_length v
    nlinarith [Nat.zero_le (s.length ^ 3), Nat.zero_le (s.length ^ 4)]
  have hw := EntryConfig.framedEncode_length_le _ _ _ (200 * (s.length + 3) ^ 4)
    haddr hval _ hb
  change ((primeDivisorProgram p).step^[t] (.eval (primeDivisorInitial p) []) |>.framedEncode
    (primeAddressCode p) (DecisionScalar.binaryCode (fun a : ZMod 2 ↦ encNat a.val))).length ≤ _
  have h1 : 1 ≤ (s.length + 3) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hpow : (s.length + 3) ^ 8 = ((s.length + 3) ^ 4) ^ 2 := by ring
  rw [hpow]
  nlinarith

theorem modulusConfigCode_length (s : List Bool) (h : (primeStage s).answer = true)
    (c : (modulusStage s h).ReachableCfg) :
    (modulusConfigCode s h c).length ≤ 1000000 * (s.length + 3) ^ 8 := by
  letI := primeFactOfStage s h
  have hp := (preflightAnswer_correct s).mp h
  have he := hp.1
  have hc := hp.2.1
  rcases c with ⟨c, t, rfl⟩
  apply polynomialConfig_code_length_input
  · intro v
    have hv := (Input.decode s).header_scalar_bits_le hc v
    rw [he] at hv
    nlinarith
  · have hd := (Input.decode s).header_degree_size_le hc
    simpa only [FieldCode.degree, he] using hd
  · rw [ZMod.card]
    have hs := (Input.decode s).characteristic_size_le
    rw [he] at hs
    nlinarith

theorem sparseConfigCode_length (s : List Bool) (h : (primeStage s).answer = true)
    (h' : (modulusStage s h).answer = true) (c : (sparseStage s h h').ReachableCfg) :
    (sparseConfigCode s h h' c).length ≤ 1000000 * (s.length + 3) ^ 8 := by
  classical
  letI : Fact (Input.decode s).field.Valid := ⟨validFieldOfStages s h h'⟩
  have he := ((preflightAnswer_correct s).mp h).1
  rcases c with ⟨c, t, rfl⟩
  apply polynomialConfig_code_length_input
  · intro v
    simpa only [he] using (Input.decode s).scalar_encoding_length_le v
  · simpa only [he] using (Input.decode s).polynomial_degree_size_le
  · simpa only [he] using (Input.decode s).field_card_size_le

/-- All three phases share one input-polynomial bound, including their input copy and tags. -/
theorem uniformCode_length (s : List Bool) (c : (uniformStages s).State) :
    (uniformCode s c).length ≤ 2000000 * (s.length + 3) ^ 8 := by
  have hbase : 2 * s.length + 6 ≤ 1000000 * (s.length + 3) ^ 8 := by
    have h1 : 1 ≤ s.length + 3 := by omega
    have hp : s.length + 3 ≤ (s.length + 3) ^ 8 := by
      exact le_self_pow₀ h1 (by omega)
    omega
  cases c with
  | first c =>
    have h := primeConfigCode_length s c
    simp only [uniformCode, List.length_append, pair_length, List.length_cons, List.length_nil]
    omega
  | second h c =>
    have hh := modulusConfigCode_length s h c
    simp only [uniformCode, List.length_append, pair_length, List.length_cons, List.length_nil]
    omega
  | third h h' c =>
    have hh := sparseConfigCode_length s h h' c
    simp only [uniformCode, List.length_append, pair_length, List.length_cons, List.length_nil]
    omega
  | done b => simp [uniformCode]; omega

end SparseIrred.UpperBounds.Section4
