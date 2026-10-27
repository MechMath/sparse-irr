import SparseIrred.UpperBounds.Section4.BinaryConclusion
/-! End-to-end binary execution checks. Run: lake env lean scripts/Section4Smoke.lean
Expected results: true, false, true, false, true, false, false.
These runtime checks supplement the kernel-checked machine theorem. -/

open SparseIrred.UpperBounds.Section4 Complexity

def runBinary (fuel : Nat) (state : List Bool) : Option (List Bool) :=
  match fuel with
  | 0 => none
  | fuel + 1 => if state.headD false then some (section4BinaryStep state)
    else runBinary fuel (section4BinaryStep state)

def runInput (x : Input) := runBinary 200000 (pair [] x.encode)
#eval runInput ⟨⟨2, [0, 1]⟩, [([1], 0), ([1], 1)]⟩
#eval runInput ⟨⟨2, [0, 1]⟩, [([1], 1), ([1], 1)]⟩
#eval runInput ⟨⟨2, [0, 1]⟩, [([1], 0), ([1], 1), ([1], 2)]⟩
#eval runInput ⟨⟨2, [0, 1]⟩, [([1], 0), ([1], 2)]⟩
#eval runInput ⟨⟨2, [1, 1, 1]⟩, [([0, 1], 0), ([1, 0], 1)]⟩
#eval runInput ⟨⟨4, [0, 1]⟩, [([1], 1)]⟩
#eval runBinary 200000 (pair [] [])
