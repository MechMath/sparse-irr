import SparseIrred.UpperBounds.Section4.OracleMachineTM

/-!
# Finite-configuration halting bounds for entry-oracle machines

No running-time assumption is made. Determinism and actual termination imply
that no configuration repeats before the first halt; a spatial window therefore
bounds the number of oracle transitions by a single exponential.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity

variable {k : ℕ}

private theorem windowed_step (M : TM k) {x : List Bool} {S : ℕ}
    {c d : Cfg k M.Q} (hw : Windowed x S c) (hs : M.step c = some d)
    (hsp : c.WithinDecisionSpace x.length S) : Windowed x S d := by
  rw [TM.step, ite_eq_right (TM.state_ne_qhalt_of_step hs)] at hs
  injection hs with hs
  subst d
  refine ⟨?_, ?_, ?_⟩
  · show (c.input.move _).cells = _
    cases (M.δ c.state c.input.read (fun i ↦ (c.work i).read) c.output.read).2.2.2.1 <;>
      exact hw.input
  · intro i p hp
    have hh := hsp.1.1 i
    show ((c.work i).writeAndMove _ _).cells p = Γ.blank
    rw [cells_writeAndMove_of_ne _ _ _ (by omega)]
    exact hw.work i p hp
  · intro p hp
    have hh := hsp.2
    show (c.output.writeAndMove _ _).cells p = Γ.blank
    rw [cells_writeAndMove_of_ne _ _ _ (by omega)]
    exact hw.output p hp

/-- Every point in the total run remains reachable by an actual finite path. -/
theorem oracle_run_reaches (M : TM k) (x : List Bool) (t : ℕ) :
    M.reaches (M.initCfg x) (M.runCfg (M.initCfg x) t) := by
  obtain ⟨u, _, hu⟩ := M.runCfg_reachesIn (M.initCfg x) t
  exact TM.reaches_of_reachesIn hu

theorem oracle_run_windowed (M : TM k) (x : List Bool) (S : ℕ)
    (hspace : ∀ c, M.reaches (M.initCfg x) c → c.WithinDecisionSpace x.length S) (t : ℕ) :
    Windowed x S (M.runCfg (M.initCfg x) t) := by
  induction t with
  | zero => exact windowed_init _ _ _
  | succ t ih =>
    rw [TM.runCfg_succ]
    cases hs : M.step (M.runCfg (M.initCfg x) t) with
    | none => exact ih
    | some d =>
      exact windowed_step M ih hs (hspace _ (oracle_run_reaches M x t))

private theorem oracle_run_injective (M : TM k) (x : List Bool) (t : ℕ)
    (hhalt : M.halted (M.runCfg (M.initCfg x) t))
    (hmin : ∀ u < t, ¬M.halted (M.runCfg (M.initCfg x) u)) :
    Function.Injective (fun u : Fin (t + 1) ↦ M.runCfg (M.initCfg x) u.val) := by
  suffices hn : ∀ a b, a < b → b ≤ t →
      M.runCfg (M.initCfg x) a ≠ M.runCfg (M.initCfg x) b by
    intro a b hab
    apply Fin.ext
    by_contra he
    rcases lt_or_gt_of_ne he with hlt | hgt
    · exact hn a b hlt (by omega) hab
    · exact hn b a hgt (by omega) hab.symm
  intro a b hab hbt he
  have hh : M.runCfg (M.initCfg x) (a + (t - b)) = M.runCfg (M.initCfg x) t := by
    rw [M.runCfg_add, he, ← M.runCfg_add, Nat.add_sub_of_le hbt]
  exact hmin (a + (t - b)) (by omega) (hh ▸ hhalt)

/-- A terminated oracle run has fewer steps than there are configurations in its window. -/
theorem oracle_first_halt_lt_card (M : TM k) (x : List Bool) (S t : ℕ)
    (hspace : ∀ c, M.reaches (M.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hhalt : M.halted (M.runCfg (M.initCfg x) t))
    (hmin : ∀ u < t, ¬M.halted (M.runCfg (M.initCfg x) u)) :
    t < Fintype.card (Code M.Q k x.length S) := by
  have hinj : Function.Injective (fun u : Fin (t + 1) ↦
      Complexity.cfgCode x.length S (M.runCfg (M.initCfg x) u.val)) := by
    intro a b he
    apply oracle_run_injective M x t hhalt hmin
    exact cfgCode_inj (oracle_run_windowed M x S hspace a.val)
      (hspace _ (oracle_run_reaches M x a.val))
      (oracle_run_windowed M x S hspace b.val)
      (hspace _ (oracle_run_reaches M x b.val)) he
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

/-- A concrete exponent linear in oracle space, input size and finite control size. -/
def oracleTimeExponent (M : TM k) (inputLength space : ℕ) : ℕ :=
  Fintype.card M.Q + (inputLength + space + 2) + 3 * k * (space + 1) + 3 * (space + 2)

/-- Termination plus spatial boundedness yields a bounded first halt, with no oracle time premise. -/
theorem oracle_exists_first_halt (M : TM k) (x : List Bool) (S : ℕ)
    (hspace : ∀ c, M.reaches (M.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hterm : ∃ c, M.reaches (M.initCfg x) c ∧ M.halted c) :
    ∃ t, t < 2 ^ oracleTimeExponent M x.length S ∧
      M.halted (M.runCfg (M.initCfg x) t) ∧
      ∀ u < t, ¬M.halted (M.runCfg (M.initCfg x) u) := by
  classical
  have hex : ∃ t, M.halted (M.runCfg (M.initCfg x) t) := by
    obtain ⟨c, hr, hh⟩ := hterm
    obtain ⟨t, ht⟩ := M.reaches_to_reachesIn hr
    exact ⟨t, by rw [M.runCfg_of_reachesIn ht]; exact hh⟩
  let t := Nat.find hex
  have hh : M.halted (M.runCfg (M.initCfg x) t) := Nat.find_spec hex
  have hm : ∀ u < t, ¬M.halted (M.runCfg (M.initCfg x) u) := fun u hu ↦ Nat.find_min hex hu
  refine ⟨t, ?_, hh, hm⟩
  exact (oracle_first_halt_lt_card M x S t hspace hh hm).trans_le
    (card_Code_le_two_pow M.Q k x.length S)

end SparseIrred.UpperBounds.Section4
