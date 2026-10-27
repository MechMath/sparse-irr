import SparseIrred.UpperBounds.Section4.OracleMachineRun
import SparseIrred.UpperBounds.Section4.OracleMachineDispatch

/-!
# Turning an actual entry Turing machine into the coroutine's scalar oracle

The source assumptions are precisely an actual halting computation of the entry
value and a bound on every reachable tape configuration. The resulting oracle
uses the proved polynomial-time one-transition simulator and has an exponential
first-return bound derived from its spatial window.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.Cobham

variable {I R : Type*} {k : ℕ}

/-- An actual entry machine, with its binary interface and spatial bounds.
There is no time bound or polynomial-time whole-entry function in this structure. -/
structure EntryMachineSource (M : TM k) (answer : I → R) where
  query : I → List Bool
  encode : R → List Bool
  decode : List Bool → R
  roundtrip : ∀ v, decode (encode v) = v
  space : I → ℕ
  window : I → ℕ
  window_space : ∀ i, (query i).length + space i + 1 ≤ window i
  window_states : ∀ i, Fintype.card M.Q ≤ blockWidth (window i)
  window_output : ∀ i, (encode (answer i)).length + 1 ≤ window i
  bounded : ∀ i c, M.reaches (M.initCfg (query i)) c →
    c.WithinDecisionSpace (query i).length (space i)
  computes : ∀ i, ∃ c, M.reaches (M.initCfg (query i)) c ∧ M.halted c ∧
    c.output.HasOutput (encode (answer i))

namespace EntryMachineSource

variable {M : TM k} {answer : I → R} (E : EntryMachineSource M answer)

private theorem firstReturn_exists (i : I) : ∃ t,
    t < 2 ^ oracleTimeExponent M (E.query i).length (E.space i) ∧
    M.halted (M.runCfg (M.initCfg (E.query i)) t) ∧
    ∀ u < t, ¬M.halted (M.runCfg (M.initCfg (E.query i)) u) := by
  apply oracle_exists_first_halt M (E.query i) (E.space i) (E.bounded i)
  obtain ⟨c, hr, hh, _⟩ := E.computes i
  exact ⟨c, hr, hh⟩

/-- A proof index for the first return, never represented in an oracle register. -/
def firstReturn (i : I) : ℕ := Classical.choose (E.firstReturn_exists i)

theorem firstReturn_bound (i : I) :
    E.firstReturn i < 2 ^ oracleTimeExponent M (E.query i).length (E.space i) :=
  (Classical.choose_spec (E.firstReturn_exists i)).1

theorem firstReturn_halted (i : I) :
    M.halted (M.runCfg (M.initCfg (E.query i)) (E.firstReturn i)) :=
  (Classical.choose_spec (E.firstReturn_exists i)).2.1

theorem firstReturn_minimal (i : I) (t : ℕ) (ht : t < E.firstReturn i) :
    ¬M.halted (M.runCfg (M.initCfg (E.query i)) t) :=
  (Classical.choose_spec (E.firstReturn_exists i)).2.2 t ht

/-- The query start code contains the actual machine's initial configuration. -/
def startCode (i : I) : List Bool :=
  oracleConfigCode M (E.window i) (M.initCfg (E.query i))

/-- Scalar readout is permitted only after the oracle's finite state has halted. -/
def readCode (z : List Bool) : Option R :=
  if (oracleHalt M z).headD false then some (E.decode (oracleOutput z)) else none

theorem iterate_code (i : I) (t : ℕ) :
    (oracleStep M)^[t] (E.startCode i) =
      oracleConfigCode M (E.window i) (M.runCfg (M.initCfg (E.query i)) t) :=
  oracleStep_iterate_code M (E.query i) (E.space i) (E.window i)
    (E.window_states i) (E.window_space i) (E.bounded i) t

theorem running_code (i : I) (t : ℕ) (ht : t < E.firstReturn i) :
    E.readCode ((oracleStep M)^[t] (E.startCode i)) = none := by
  rw [E.iterate_code]
  simp only [readCode, oracleHalt_code M _ _ (E.window_states i)]
  have hn := E.firstReturn_minimal i t ht
  simp [hn]

theorem returned_code (i : I) :
    E.readCode ((oracleStep M)^[E.firstReturn i] (E.startCode i)) = some (answer i) := by
  rw [E.iterate_code]
  have hc := oracle_codeInv M (E.query i) (E.space i) (E.window i)
    (E.window_space i) (E.bounded i) (E.firstReturn i)
  obtain ⟨c, hr, hh, ho⟩ := E.computes i
  have heq : M.runCfg (M.initCfg (E.query i)) (E.firstReturn i) = c :=
    by
      obtain ⟨u, hu⟩ := M.reaches_to_reachesIn hr
      calc
        M.runCfg (M.initCfg (E.query i)) (E.firstReturn i) =
            M.runCfg (M.initCfg (E.query i)) (E.firstReturn i + u) := by
          rw [M.runCfg_add, M.runCfg_of_halted (E.firstReturn_halted i)]
        _ = c := by
          rw [Nat.add_comm, M.runCfg_add, M.runCfg_of_reachesIn hu, M.runCfg_of_halted hh]
  simp only [readCode, oracleHalt_code M _ _ (E.window_states i)]
  have hh' := E.firstReturn_halted i
  rw [decide_eq_true hh']
  simp only [List.headD_cons, ↓reduceIte]
  rw [oracleOutput_code M _ _ (E.encode (answer i)) hc (heq ▸ ho)
    (E.window_output i), E.roundtrip]

/-- The abstract scalar oracle is implemented by the actual machine's encoded configurations. -/
def scalarOracle : ScalarOracle I R (List Bool) answer where
  start := E.startCode
  step := oracleStep M
  read := E.readCode
  stop := E.firstReturn
  running := E.running_code
  returned := E.returned_code

/-- The oracle's encoded workspace is independent of its running time. -/
theorem iterate_length (i : I) (t : ℕ) :
    ((oracleStep M)^[t] (E.startCode i)).length =
      (2 * codeBlocks k + 2) * (E.window i + 1) + 2 := by
  rw [E.iterate_code, oracleConfigCode_length]

/-- The initializer is also the proved polynomial-time initializer of the actual TM. -/
theorem startCode_eq_init (i : I) :
    E.startCode i = oracleInit M (pair (oracleRuler (E.window i)) (E.query i)) := by
  symm
  apply oracleInit_code
  have h := E.window_space i
  omega

end EntryMachineSource

end SparseIrred.UpperBounds.Section4
