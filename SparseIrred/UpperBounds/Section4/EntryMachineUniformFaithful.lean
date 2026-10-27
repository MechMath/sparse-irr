import SparseIrred.UpperBounds.Section4.EntryMachineUniformEncoding

/-! # Faithfulness of the complete uniform staged-state representation -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

set_option backward.isDefEq.respectTransparency false

private theorem zmodScalarCode_injective (p : ℕ) [NeZero p] :
    Function.Injective (fun a : ZMod p ↦ encNat a.val) := by
  intro a b h
  apply ZMod.val_injective p
  have he := congrArg decNat h
  simpa only [decNat_encNat] using he

theorem primeConfigCode_injective (s : List Bool) : Function.Injective (primeConfigCode s) := by
  intro c d h
  apply Subtype.ext
  have haddr : Function.Injective (primeAddressCode (Input.decode s).field.characteristic) :=
    OrAddress.binaryCode_injective
      (fun _ : Fin (Input.decode s).field.characteristic ↦ fun _ : Unit ↦ [])
      (fun _ a b _ ↦ Subsingleton.elim a b)
  exact EntryConfig.framedEncode_injective _ _ haddr
    (DecisionScalar.binaryCode_injective _ (zmodScalarCode_injective 2)) h

theorem modulusConfigCode_injective (s : List Bool) (h : (primeStage s).answer = true) :
    Function.Injective (modulusConfigCode s h) := by
  letI := primeFactOfStage s h
  intro c d he
  apply Subtype.ext
  exact EntryConfig.framedEncode_injective _ _ (polynomialAddressCode_injective _ _)
    (DecisionScalar.binaryCode_injective _ (zmodScalarCode_injective _)) he

theorem sparseConfigCode_injective (s : List Bool) (h : (primeStage s).answer = true)
    (h' : (modulusStage s h).answer = true) : Function.Injective (sparseConfigCode s h h') := by
  letI : Fact (Input.decode s).field.Valid := ⟨validFieldOfStages s h h'⟩
  intro c d he
  apply Subtype.ext
  exact EntryConfig.framedEncode_injective _ _ (polynomialAddressCode_injective _ _)
    (DecisionScalar.binaryCode_injective _ (FieldCode.scalar_encoding_injective _)) he

/-- Each typed state can be recovered uniquely from its fixed binary representation. -/
theorem uniformCode_injective (s : List Bool) : Function.Injective (uniformCode s) := by
  intro c d he
  cases c <;> cases d <;>
    simp only [uniformCode, List.cons_append, List.nil_append, List.cons.injEq,
      Bool.false_eq_true, Bool.true_eq_false, false_and, true_and, and_true] at he
  all_goals try contradiction
  all_goals try exact congrArg ThreeStages.State.done he
  all_goals
    have hp := (pair_inj he).2
    simp only [List.cons_append, List.nil_append, List.cons.injEq, Bool.false_eq_true,
      Bool.true_eq_false, false_and, true_and] at hp
  · exact congrArg ThreeStages.State.first (primeConfigCode_injective s hp)
  · exact congrArg (ThreeStages.State.second _) (modulusConfigCode_injective s _ hp)
  · exact congrArg (ThreeStages.State.third _ _) (sparseConfigCode_injective s _ _ hp)

end SparseIrred.UpperBounds.Section4
