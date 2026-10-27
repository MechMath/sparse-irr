import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Tape.Encoding
import Complexitylib.Models.TuringMachine.Frame
import SparseDivComplexity.Encoding

/-!
# Loading a packed sparse input in linear space

The three-state transducer copies the input and appends a one-bit sentinel.
It runs in exactly `|x|+2` steps, so every reachable configuration also has a
linear space bound. The sentinel preserves trailing zero bits when the result
is subsequently treated as a canonical binary natural register.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity Complexity.TM SparseDiv

inductive PackedInputPhase where
  | start | copy | done
  deriving DecidableEq

instance : Fintype PackedInputPhase where
  elems := {.start, .copy, .done}
  complete q := by cases q <;> simp

def packedInputTM : TM 0 where
  Q := PackedInputPhase
  qstart := .start
  qhalt := .done
  δ := fun q ih _wh oh ↦
    match q with
    | .start => (.copy, Fin.elim0, readBackWrite oh, .right, Fin.elim0, .right)
    | .copy =>
        match ih with
        | .zero => (.copy, Fin.elim0, .zero, .right, Fin.elim0, .right)
        | .one => (.copy, Fin.elim0, .one, .right, Fin.elim0, .right)
        | _ => (.done, Fin.elim0, .one, idleDir ih, Fin.elim0, .right)
    | .done => (.done, Fin.elim0, readBackWrite oh, idleDir ih, Fin.elim0, idleDir oh)
  δ_right_of_start := by
    intro q ih wh oh
    cases q <;> cases ih <;>
      simp [idleDir]

private theorem packedInputTM_loop (xs ys : List Bool)
    (inp out : Tape) (work : Fin 0 → Tape)
    (hin : inp.HasBinarySuffix xs) (hout : out.HasBinaryPrefix ys) :
    ∃ c : Cfg 0 PackedInputPhase,
      packedInputTM.reachesIn (xs.length + 1)
        ⟨.copy, inp, work, out⟩ c ∧ packedInputTM.halted c ∧
        c.output.HasBinaryPrefix (ys ++ xs ++ [true]) := by
  induction xs generalizing ys inp out work with
  | nil =>
      have hr := hin.read_nil
      let c : Cfg 0 PackedInputPhase :=
        ⟨.done, inp.move (idleDir inp.read), Fin.elim0, out.writeAndMove Γ.one .right⟩
      refine ⟨c, TM.reachesIn.step ?_ TM.reachesIn.zero, rfl, ?_⟩
      · simp [packedInputTM, TM.step, hr, c]
        exact Subsingleton.elim _ _
      · simpa [c, Γ.ofBool] using Tape.hasBinaryPrefix_write_bit true hout
  | cons b xs ih =>
      have hr := hin.read_cons
      let inp' := inp.move Dir3.right
      let out' := out.writeAndMove (Γ.ofBool b) Dir3.right
      have hin' : inp'.HasBinarySuffix xs := hin.move_right_cons
      have hout' : out'.HasBinaryPrefix (ys ++ [b]) := Tape.hasBinaryPrefix_write_bit b hout
      obtain ⟨c, hc, hh, hp⟩ := ih (ys ++ [b]) inp' out' Fin.elim0 hin' hout'
      refine ⟨c, TM.reachesIn.step ?_ hc, hh, ?_⟩
      · cases b <;> simp [packedInputTM, TM.step, hr, inp', out', Γ.ofBool] <;>
          exact Subsingleton.elim _ _
      · simpa only [List.append_assoc, List.singleton_append] using hp

/-- The concrete transducer loads the sentinel representation in linear time. -/
theorem packedInputTM_computesInTime :
    packedInputTM.ComputesInTime (fun x ↦ x ++ [true]) (fun n ↦ n + 2) := by
  intro x
  let inp := (Tape.init (x.map Γ.ofBool)).move Dir3.right
  let out := (Tape.init []).move Dir3.right
  obtain ⟨c, hc, hh, hp⟩ := packedInputTM_loop x [] inp out Fin.elim0
    (Tape.init_move_right_hasBinarySuffix x) Tape.init_nil_move_right_hasBinaryPrefix_nil
  refine ⟨c, x.length + 2, le_rfl, TM.reachesIn.step ?_ hc, hh, ?_⟩
  · simp [packedInputTM, TM.step, inp, out, Tape.read, Tape.init,
      Tape.writeAndMove, Tape.write, readBackWrite]
    exact Subsingleton.elim _ _
  · simpa using hp.hasOutput

/-- Every configuration of the loading phase has a linear auxiliary-space bound. -/
theorem packedInputTM_allPrefixes (x : List Bool) (c : Cfg 0 PackedInputPhase)
    (hreach : packedInputTM.reaches (packedInputTM.initCfg x) c) :
    c.WithinAuxSpace x.length (x.length + 2) := by
  let pre : TM.TapePred 0 := fun inp work out ↦
    inp = Tape.init (x.map Γ.ofBool) ∧ work = (fun _ ↦ Tape.init []) ∧ out = Tape.init []
  have ht : packedInputTM.HoareTime pre
      (fun _ _ out ↦ out.HasOutput (x ++ [true])) (x.length + 2) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact packedInputTM_computesInTime x
  have hs := ht.toHoareTimeSpace (inputLength := x.length) (initialSpace := 0) (by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
    simp [Tape.init])
  simpa only [Cfg.WithinAuxSpace, Nat.zero_add] using hs.2 _ _ _ ⟨rfl, rfl, rfl⟩ c hreach

end SparseIrred.UpperBounds.Machine
