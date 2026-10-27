import SparseIrred.UpperBounds.Section4.EntryMachineBoolean
import SparseIrred.UpperBounds.Section4.HeaderBounds

/-!
# The first stage: input syntax and trial division

Trial division is unfolded into the same small-stack evaluator. A leaf performs
one remainder operation; it does not decide primality. Balanced enumeration uses
logarithmic depth even when the characteristic is exponentially large.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial

set_option backward.isDefEq.respectTransparency false

def DecisionScalar.asBool {K : Type*} : DecisionScalar K → Bool
  | .flag b => b
  | _ => false

def constantProgram {R : Type*} (v : R) : EntryProgram Unit R where
  instruction _ := .value v
  rank _ := 0
  descend _ _ _ _ h := by cases h

@[simp] theorem constantProgram_value {R : Type*} [Add R] [Mul R] (v : R) (a : Unit) :
    (constantProgram v).value a = v := by rw [EntryProgram.value]; rfl

def divisorFlag (p i : ℕ) : Bool := decide (2 ≤ i ∧ i < p ∧ p % i = 0)

abbrev PrimeAddress (p : ℕ) := OrAddress (fun _ : Fin p ↦ Unit)

def primeDivisorProgram (p : ℕ) : EntryProgram (PrimeAddress p) (DecisionScalar (ZMod 2)) :=
  orProgram (fun i ↦ constantProgram (.flag (divisorFlag p i.val)))
    (fun _ ↦ ()) 0 (fun _ ↦ le_rfl)

def primeDivisorInitial (p : ℕ) : PrimeAddress p := .range 0 p

theorem primeDivisorProgram_value (p : ℕ) :
    (primeDivisorProgram p).value (primeDivisorInitial p) =
      .flag ((List.range p).any (divisorFlag p)) := by
  rw [primeDivisorProgram, primeDivisorInitial,
    orProgram_value _ _ _ _ (fun i ↦ divisorFlag p i.val) (fun _ ↦ constantProgram_value _ _)]
  congr 1
  apply List.any_congr rfl
  intro i
  by_cases hi : i < p <;> simp [hi, divisorFlag]

theorem no_divisor_iff_prime (p : ℕ) :
    (2 ≤ p ∧ (List.range p).any (divisorFlag p) = false) ↔ p.Prime := by
  rw [Nat.prime_def_lt']
  simp only [List.any_eq_false, List.mem_range, divisorFlag, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun m hm hmp hdiv ↦ ?_⟩
    exact hd m hmp ⟨hm, hmp, Nat.mod_eq_zero_of_dvd hdiv⟩
  · rintro ⟨hp, hd⟩
    exact ⟨hp, fun m hm h ↦ hd m h.1 hm (Nat.dvd_of_mod_eq_zero h.2.2)⟩

theorem primeDivisorProgram_rank (p : ℕ) :
    (primeDivisorProgram p).rank (primeDivisorInitial p) ≤ p.log2 + 4 := by
  change 0 + splitDepth p + 2 ≤ _
  have := splitDepth_le_log p
  omega

/-- The first stage also rejects malformed framing and a noncanonical header.
These checks do not require deciding polynomial irreducibility. -/
def preflightOutput (s : List Bool) : DecisionScalar (ZMod 2) → Bool :=
  fun v ↦ decide ((Input.decode s).encode = s) && (Input.decode s).field.structuralFlag &&
    !v.asBool

noncomputable def preflightAnswer (s : List Bool) : Bool :=
  preflightOutput s ((primeDivisorProgram (Input.decode s).field.characteristic).value
    (primeDivisorInitial (Input.decode s).field.characteristic))

theorem preflightAnswer_correct (s : List Bool) :
    preflightAnswer s = true ↔ (Input.decode s).encode = s ∧
      (Input.decode s).field.Structural ∧ (Input.decode s).field.characteristic.Prime := by
  rw [preflightAnswer, primeDivisorProgram_value]
  simp only [preflightOutput, DecisionScalar.asBool, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', FieldCode.structuralFlag_correct]
  constructor
  · rintro ⟨⟨he, hs⟩, hd⟩
    exact ⟨he, hs, (no_divisor_iff_prime _).mp ⟨hs.characteristic, hd⟩⟩
  · rintro ⟨he, hs, hp⟩
    exact ⟨⟨he, hs⟩, ((no_divisor_iff_prime _).mpr hp).2⟩

end SparseIrred.UpperBounds.Section4
