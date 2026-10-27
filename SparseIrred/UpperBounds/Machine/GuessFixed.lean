import Complexitylib.Models.TuringMachine.Subroutines.GuessBounded
import SparseIrred.UpperBounds.Machine.GuessVerify
import Mathlib.Data.List.OfFn

/-!
# A fixed-length uniform guessing machine

This is a concrete four-state nondeterministic Turing machine. Its witness length
is supplied on a unary counter tape, so its finite control is independent of the
input length. It always continues while the counter is nonempty, writes one fresh
random bit per counter mark, and finally rewinds the witness tape.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity Complexity.NTM

variable {n : ℕ}

/-- Force the continue choice in the administrative state; retain the random bit
in the writing state. -/
def fixedChoice (state : GuessBoundedPhase) (choice : Bool) : Bool :=
  if state = .choose then true else choice

/-- Uniform fixed-length guessing using a preloaded unary counter. -/
def guessFixedNTM (witnessIdx counterIdx : Fin n) : NTM n where
  Q := GuessBoundedPhase
  qstart := .choose
  qhalt := .done
  δ := fun choice state ↦
    (guessBoundedNTM witnessIdx counterIdx).δ (fixedChoice state choice) state
  δ_right_of_start := fun choice state ↦
    (guessBoundedNTM witnessIdx counterIdx).δ_right_of_start (fixedChoice state choice) state

set_option backward.isDefEq.respectTransparency false

/-- One fixed-guess step is a bounded-guess step with its administrative choice forced. -/
theorem guessFixedNTM_trace_one (witnessIdx counterIdx : Fin n) (choice : Bool)
    (c : Cfg n GuessBoundedPhase) :
    (guessFixedNTM witnessIdx counterIdx).trace 1 (fun _ ↦ choice) c =
      (guessBoundedNTM witnessIdx counterIdx).trace 1
        (fun _ ↦ fixedChoice c.state choice) c := by
  by_cases h : c.state = GuessBoundedPhase.done <;>
    simp [NTM.trace, guessFixedNTM, guessBoundedNTM, h]

/-- Every fixed-guess trace is a trace of the existing bounded-guess machine.
This transfers its tape-frame and rewind facts without changing the random bits. -/
theorem guessFixedNTM_trace_eq_bounded (witnessIdx counterIdx : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n GuessBoundedPhase) :
    ∃ boundedChoices : Fin T → Bool,
      (guessFixedNTM witnessIdx counterIdx).trace T choices c =
        (guessBoundedNTM witnessIdx counterIdx).trace T boundedChoices c := by
  induction T with
  | zero => exact ⟨choices, rfl⟩
  | succ T ih =>
      obtain ⟨seedPrefix, hprefix⟩ := ih (fun i ↦ choices i.castSucc)
      let current := (guessBoundedNTM witnessIdx counterIdx).trace T seedPrefix c
      refine ⟨Fin.snoc seedPrefix (fixedChoice current.state (choices (Fin.last T))), ?_⟩
      erw [NTM.trace_snoc (guessFixedNTM witnessIdx counterIdx) T,
        NTM.trace_snoc (guessBoundedNTM witnessIdx counterIdx) T]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      erw [hprefix, guessFixedNTM_trace_one]

/-- A successful two-step iteration uses precisely its second choice bit. -/
theorem guessFixedNTM_trace_two (witnessIdx counterIdx : Fin n)
    (choices : Fin 2 → Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).read ≠ Γ.blank) :
    (guessFixedNTM witnessIdx counterIdx).trace 2 choices
      { state := .choose, input := inp, work := work, output := out } =
    (guessBoundedNTM witnessIdx counterIdx).trace 2
      (fun i ↦ if i.val = 0 then true else choices 1)
      { state := .choose, input := inp, work := work, output := out } := by
  simp [NTM.trace, guessFixedNTM, fixedChoice, guessBoundedNTM, hcounter]

/-- The compact seed read during the first `2 * B` steps. -/
def fixedGuessBits (B : ℕ) (choices : ℕ → Bool) : List Bool :=
  List.ofFn (fun i : Fin B ↦ choices (2 * i.val + 1))

@[simp] theorem fixedGuessBits_length (B : ℕ) (choices : ℕ → Bool) :
    (fixedGuessBits B choices).length = B := by simp [fixedGuessBits]

theorem fixedGuessBits_succ (B : ℕ) (choices : ℕ → Bool) :
    fixedGuessBits (B + 1) choices = choices 1 :: fixedGuessBits B (fun i ↦ choices (i + 2)) := by
  simp only [fixedGuessBits, List.ofFn_succ, Fin.val_zero, mul_zero, zero_add]
  congr 2

/-- After two steps per remaining counter mark, the machine has written exactly
the bits at positions `1, 3, ..., 2 * B - 1`. -/
theorem guessFixedNTM_writes (witnessIdx counterIdx : Fin n)
    (hne : witnessIdx ≠ counterIdx) (B used total : ℕ) (bits : List Bool)
    (c : Cfg n GuessBoundedPhase) (hstate : c.state = .choose)
    (hbound : used + B ≤ total)
    (hwitness : (c.work witnessIdx).HasBinaryPrefix bits)
    (hcell0 : (c.work witnessIdx).cells 0 = Γ.start)
    (hcounter : (c.work counterIdx).HasCounterRemainder used total)
    (choices : ℕ → Bool) :
    let result := (guessFixedNTM witnessIdx counterIdx).trace (2 * B)
      (fun i ↦ choices i.val) c
    result.state = .choose ∧
      (result.work counterIdx).HasCounterRemainder (used + B) total ∧
      (result.work witnessIdx).HasBinaryPrefix (bits ++ fixedGuessBits B choices) ∧
      (result.work witnessIdx).cells 0 = Γ.start := by
  induction B generalizing used bits c choices with
  | zero => simpa [NTM.trace, fixedGuessBits] using ⟨hstate, hcounter, hwitness, hcell0⟩
  | succ B ih =>
      let first := (guessFixedNTM witnessIdx counterIdx).trace 2
        (fun i ↦ choices i.val) c
      have hstep : first.state = .choose ∧
          (first.work counterIdx).HasCounterRemainder (used + 1) total ∧
          (first.work witnessIdx).HasBinaryPrefix (bits ++ [choices 1]) ∧
          (first.work witnessIdx).cells 0 = Γ.start := by
        cases c with
        | mk state inp work out =>
            simp only at hstate
            subst state
            dsimp [first]
            have hread : (work counterIdx).read ≠ Γ.blank := by
              rw [Tape.hasCounterRemainder_read_one_of_remaining hcounter (by omega)]
              decide
            erw [guessFixedNTM_trace_two witnessIdx counterIdx _ inp work out hread]
            exact guessBoundedNTM_continue_write_invariants witnessIdx counterIdx hne
              (choices 1) inp work out hwitness hcell0 hcounter (by omega)
      have htail := ih (used + 1) (bits ++ [choices 1]) first hstep.1 (by omega)
        hstep.2.2.1 hstep.2.2.2 hstep.2.1 (fun i ↦ choices (i + 2))
      have htime : 2 * (B + 1) = 2 + 2 * B := by omega
      dsimp only
      erw [NTM.trace_cast _ htime]
      erw [NTM.trace_add_fun]
      change _ ∧ _ ∧ _ ∧ _ at htail
      simpa [first, fixedGuessBits_succ, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using htail

/-- Once the counter is exhausted, the fixed-guess machine completes and rewinds
the exact witness already written on its tape. -/
theorem guessFixedNTM_finishes (witnessIdx counterIdx : Fin n) (bits : List Bool)
    (c : Cfg n GuessBoundedPhase) (hstate : c.state = .choose)
    (hwitness : (c.work witnessIdx).HasBinaryPrefix bits)
    (hcell0 : (c.work witnessIdx).cells 0 = Γ.start)
    (hcounter : (c.work counterIdx).read = Γ.blank)
    (choices : Fin (bits.length + 3) → Bool) :
    let result := (guessFixedNTM witnessIdx counterIdx).trace (bits.length + 3) choices c
    (guessFixedNTM witnessIdx counterIdx).halted result ∧
      (result.work witnessIdx).HasBinaryString bits ∧
      (result.work witnessIdx).cells 0 = Γ.start := by
  obtain ⟨boundedChoices, htrace⟩ :=
    guessFixedNTM_trace_eq_bounded witnessIdx counterIdx (bits.length + 3) choices c
  dsimp only
  erw [htrace]
  cases c with
  | mk state inp work out =>
      simp only at hstate
      subst state
      exact guessBoundedNTM_choose_counter_blank_completes_witness witnessIdx counterIdx bits
        inp work out hwitness hcell0 hcounter boundedChoices

/-- The exact all-path behavior: `B` uniformly chosen bits are written, the
witness head is rewound, and every path halts within `3 * B + 3` steps. -/
theorem guessFixedNTM_halts_with_bits (witnessIdx counterIdx : Fin n)
    (hne : witnessIdx ≠ counterIdx) (B : ℕ) (c : Cfg n GuessBoundedPhase)
    (hstate : c.state = .choose)
    (hwitness : (c.work witnessIdx).HasBinaryPrefix [])
    (hcell0 : (c.work witnessIdx).cells 0 = Γ.start)
    (hcounter : (c.work counterIdx).HasUnaryCounter B) (choices : ℕ → Bool) :
    let result := (guessFixedNTM witnessIdx counterIdx).trace (3 * B + 3)
      (fun i ↦ choices i.val) c
    (guessFixedNTM witnessIdx counterIdx).halted result ∧
      (result.work witnessIdx).HasBinaryString (fixedGuessBits B choices) ∧
      (result.work witnessIdx).cells 0 = Γ.start := by
  have hwrite := guessFixedNTM_writes witnessIdx counterIdx hne B 0 B [] c hstate
    (by omega) hwitness hcell0 (Tape.hasUnaryCounter_iff_remainder_zero.mp hcounter) choices
  simp only [Nat.zero_add, List.nil_append] at hwrite
  let first := (guessFixedNTM witnessIdx counterIdx).trace (2 * B)
    (fun i ↦ choices i.val) c
  have hfinish := guessFixedNTM_finishes witnessIdx counterIdx (fixedGuessBits B choices)
    first hwrite.1 hwrite.2.2.1 hwrite.2.2.2
    (Tape.hasCounterRemainder_read_blank_of_done hwrite.2.1)
    (fun i ↦ choices (2 * B + i.val))
  dsimp only at hfinish
  erw [fixedGuessBits_length] at hfinish
  dsimp only
  erw [NTM.trace_cast _ (show 3 * B + 3 = 2 * B + (B + 3) by omega)]
  erw [NTM.trace_add_fun]
  exact hfinish

/-- The actual random-bit positions of the fixed-guess subroutine. -/
def fixedGuessSchedule (B : ℕ) : Fin B ↪ Fin (3 * B + 3) where
  toFun i := ⟨2 * i.val + 1, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := Fin.ext_iff.mp h; dsimp at this; omega

/-- A finite trace produces exactly the compact seed selected by its fixed schedule. -/
theorem guessFixedNTM_halts_with_seed (witnessIdx counterIdx : Fin n)
    (hne : witnessIdx ≠ counterIdx) (B : ℕ) (c : Cfg n GuessBoundedPhase)
    (hstate : c.state = .choose)
    (hwitness : (c.work witnessIdx).HasBinaryPrefix [])
    (hcell0 : (c.work witnessIdx).cells 0 = Γ.start)
    (hcounter : (c.work counterIdx).HasUnaryCounter B)
    (choices : Fin (3 * B + 3) → Bool) :
    let result := (guessFixedNTM witnessIdx counterIdx).trace (3 * B + 3) choices c
    (guessFixedNTM witnessIdx counterIdx).halted result ∧
      (result.work witnessIdx).HasBinaryString
        (List.ofFn (scheduledSeed (fixedGuessSchedule B) choices)) ∧
      (result.work witnessIdx).cells 0 = Γ.start := by
  let stream : ℕ → Bool := fun i ↦ if h : i < 3 * B + 3 then choices ⟨i, h⟩ else false
  have h := guessFixedNTM_halts_with_bits witnessIdx counterIdx hne B c hstate
    hwitness hcell0 hcounter stream
  have hstream : (fun i : Fin (3 * B + 3) ↦ stream i.val) = choices := by
    funext i
    simp [stream, i.isLt]
  have hbits : fixedGuessBits B stream =
      List.ofFn (scheduledSeed (fixedGuessSchedule B) choices) := by
    unfold fixedGuessBits
    congr 1
    funext i
    have hi : 2 * i.val + 1 < 3 * B + 3 := by omega
    change stream (2 * i.val + 1) = choices ⟨2 * i.val + 1, hi⟩
    simp [stream, hi]
  simpa only [hstream, hbits] using h

/-- Every output seed has the same number of full machine-choice strings. -/
theorem fixedGuessSchedule_fiber (B : ℕ) (seed : Fin B → Bool) :
    (Finset.univ.filter fun choices : Fin (3 * B + 3) → Bool =>
      scheduledSeed (fixedGuessSchedule B) choices = seed).card = 2 ^ (2 * B + 3) := by
  rw [card_scheduledSeed_fiber]
  congr 1
  omega

/-- The guessed witness tape has the exact initialized binary-tape shape expected
by the pair builder and deterministic verifier. -/
theorem guessFixedNTM_halts_with_exact_tape (witnessIdx counterIdx : Fin n)
    (hne : witnessIdx ≠ counterIdx) (B : ℕ) (c : Cfg n GuessBoundedPhase)
    (hstate : c.state = .choose)
    (hwitness : (c.work witnessIdx).HasBinaryPrefix [])
    (hcell0 : (c.work witnessIdx).cells 0 = Γ.start)
    (hcounter : (c.work counterIdx).HasUnaryCounter B)
    (choices : Fin (3 * B + 3) → Bool) :
    let result := (guessFixedNTM witnessIdx counterIdx).trace (3 * B + 3) choices c
    (guessFixedNTM witnessIdx counterIdx).halted result ∧
      result.work witnessIdx =
        (Tape.init ((List.ofFn (scheduledSeed (fixedGuessSchedule B) choices)).map Γ.ofBool)).move
          Dir3.right := by
  have h := guessFixedNTM_halts_with_seed witnessIdx counterIdx hne B c hstate
    hwitness hcell0 hcounter choices
  exact ⟨h.1, Tape.eq_init_move_right_of_hasBinaryString h.2.1 h.2.2⟩

/-- A started input tape is preserved throughout fixed guessing. -/
theorem guessFixedNTM_preserves_input (witnessIdx counterIdx : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n GuessBoundedPhase)
    (hread : c.input.read ≠ Γ.start) :
    ((guessFixedNTM witnessIdx counterIdx).trace T choices c).input = c.input := by
  obtain ⟨boundedChoices, htrace⟩ :=
    guessFixedNTM_trace_eq_bounded witnessIdx counterIdx T choices c
  rw [htrace]
  exact guessBoundedNTM_trace_preserves_input witnessIdx counterIdx T boundedChoices c hread

/-- A started output tape is preserved throughout fixed guessing. -/
theorem guessFixedNTM_preserves_output (witnessIdx counterIdx : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n GuessBoundedPhase)
    (hread : c.output.read ≠ Γ.start) :
    ((guessFixedNTM witnessIdx counterIdx).trace T choices c).output = c.output := by
  obtain ⟨boundedChoices, htrace⟩ :=
    guessFixedNTM_trace_eq_bounded witnessIdx counterIdx T choices c
  rw [htrace]
  exact guessBoundedNTM_trace_preserves_output witnessIdx counterIdx T boundedChoices c hread

/-- Every other started work tape is preserved throughout fixed guessing. -/
theorem guessFixedNTM_preserves_other_work (witnessIdx counterIdx i : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n GuessBoundedPhase)
    (hw : i ≠ witnessIdx) (hc : i ≠ counterIdx) (hread : (c.work i).read ≠ Γ.start) :
    ((guessFixedNTM witnessIdx counterIdx).trace T choices c).work i = c.work i := by
  obtain ⟨boundedChoices, htrace⟩ :=
    guessFixedNTM_trace_eq_bounded witnessIdx counterIdx T choices c
  rw [htrace]
  exact guessBoundedNTM_trace_preserves_other_work witnessIdx counterIdx i T boundedChoices c
    hw hc hread

/-- A reusable Hoare specification with an exact witness length and tape shape. -/
theorem guessFixedNTM_hoareTime (witnessIdx counterIdx : Fin n)
    (hne : witnessIdx ≠ counterIdx) (B : ℕ) :
    (guessFixedNTM witnessIdx counterIdx).HoareTime
      (fun _ work _ ↦ (work witnessIdx).HasBinaryPrefix [] ∧
        (work witnessIdx).cells 0 = Γ.start ∧ (work counterIdx).HasUnaryCounter B)
      (fun _ work _ ↦ ∃ bits : List Bool, bits.length = B ∧
        work witnessIdx = (Tape.init (bits.map Γ.ofBool)).move Dir3.right)
      (3 * B + 3) := by
  intro inp work out hpre choices
  have h := guessFixedNTM_halts_with_exact_tape witnessIdx counterIdx hne B
    { state := .choose, input := inp, work := work, output := out }
    rfl hpre.1 hpre.2.1 hpre.2.2 choices
  exact ⟨h.1, _, List.length_ofFn, h.2⟩

end SparseIrred.UpperBounds.Machine
