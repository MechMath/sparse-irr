import SparseIrred.UpperBounds.Section4.UniformStages
import SparseIrred.UpperBounds.Section4.PolynomialProgramBounds
import SparseIrred.UpperBounds.Section4.StageMachineSpace

/-!
# Unconditional bounds for all three uniform stages

The first stage is bounded even on malformed strings. Later stages carry the
proved successful preflight, so their actual input encodings equal the original
string. This supplies all degree and field-cardinality bounds internally.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial

set_option backward.isDefEq.respectTransparency false

def uniformStageRankBound (L : ℕ) : ℕ := 100 * (L + 3) ^ 4

private theorem log2_le_binary_size (n : ℕ) : n.log2 ≤ n.size := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Nat.le_of_lt ((Nat.log2_lt hn).mpr (Nat.lt_size_self n))

/-- The trial-division stage is bounded on every raw binary input. -/
theorem primeStage_rank_bound (s : List Bool) :
    (primeStage s).program.rank (primeStage s).initial ≤ uniformStageRankBound s.length := by
  have hp := primeDivisorProgram_rank (Input.decode s).field.characteristic
  have hlog := log2_le_binary_size (Input.decode s).field.characteristic
  have hsize := Input.decoded_characteristic_size_le s
  have hpow : s.length + 3 ≤ (s.length + 3) ^ 4 :=
    le_self_pow₀ (by omega) (by decide)
  change (primeDivisorProgram _).rank (primeDivisorInitial _) ≤ _
  unfold uniformStageRankBound
  omega

/-- No irreducibility of the modulus is needed to bound the modulus test: the
completed first stage has already certified its explicit shape and prime field. -/
theorem modulusStage_rank_bound (s : List Bool) (h : (primeStage s).answer = true) :
    (modulusStage s h).program.rank (modulusStage s h).initial ≤
      uniformStageRankBound s.length := by
  have := primeFactOfStage s h
  have hs := (preflightAnswer_correct s).mp h
  have hd := (Input.decode s).header_degree_size_le hs.2.1
  rw [hs.1] at hd
  have hq : (Fintype.card (ZMod (Input.decode s).field.characteristic)).size ≤
      s.length ^ 2 + 1 := by
    rw [ZMod.card]
    have hp := Input.decoded_characteristic_size_le s
    nlinarith
  exact polynomialProgram_rank_input (Input.decode s).field.polynomial s.length hd hq

/-- The actual extension field, including its input extension degree, obeys the
same polynomial rank bound after the two successful validation stages. -/
theorem sparseStage_rank_bound (s : List Bool) (h : (primeStage s).answer = true)
    (h' : (modulusStage s h).answer = true) :
    (sparseStage s h h').program.rank (sparseStage s h h').initial ≤
      uniformStageRankBound s.length := by
  classical
  have : Fact (Input.decode s).field.Valid := ⟨validFieldOfStages s h h'⟩
  have hs := (preflightAnswer_correct s).mp h
  have hd := (Input.decode s).polynomial_degree_size_le
  have hq := (Input.decode s).field_card_size_le
  rw [hs.1] at hd hq
  exact polynomialProgram_rank_input
    ((Input.decode s).field.sparsePolynomial (Input.decode s).terms) s.length hd hq

/-- A binary arithmetic tree of bounded rank has a bounded initial work measure. -/
theorem StageSpec.initial_work_le_pow (S : StageSpec) (r : ℕ)
    (hr : S.program.rank S.initial ≤ r) :
    S.program.work S.initialConfig ≤ 2 ^ (r + 3) := by
  have ht := S.program.treeSize_le S.initial
  have hp : 2 ^ (S.program.rank S.initial + 1) ≤ 2 ^ (r + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have he : 2 ^ (r + 3) = 4 * 2 ^ (r + 1) := by
    rw [show r + 3 = (r + 1) + 2 by omega, pow_add]
    norm_num
    omega
  change 3 * S.program.treeSize S.initial + 0 ≤ _
  rw [he]
  omega

/-- A proof-only work budget, never written to a runtime register. -/
def uniformStageWorkBound (s : List Bool) : ℕ :=
  2 ^ (uniformStageRankBound s.length + 3)

theorem uniformStages_work_bound (s : List Bool) :
    (uniformStages s).WorkBound (uniformStageWorkBound s) where
  first := (primeStage s).initial_work_le_pow _ (primeStage_rank_bound s)
  second h := (modulusStage s h).initial_work_le_pow _ (modulusStage_rank_bound s h)
  third h h' := (sparseStage s h h').initial_work_le_pow _ (sparseStage_rank_bound s h h')

/-- The exponent of the overall local-step clock is a fixed polynomial in input length. -/
noncomputable def uniformTimeExponent : Polynomial ℕ :=
  Polynomial.C 100 * (Polynomial.X + Polynomial.C 3) ^ 4 + Polynomial.C 6

@[simp] theorem uniformTimeExponent_eval (L : ℕ) :
    uniformTimeExponent.eval L = uniformStageRankBound L + 6 := by
  simp [uniformTimeExponent, uniformStageRankBound]

theorem uniformStages_time_budget (s : List Bool) :
    3 * (uniformStageWorkBound s + 1) + 1 ≤ 2 ^ uniformTimeExponent.eval s.length := by
  rw [uniformTimeExponent_eval]
  unfold uniformStageWorkBound
  have he : 2 ^ (uniformStageRankBound s.length + 6) =
      8 * 2 ^ (uniformStageRankBound s.length + 3) := by
    rw [show uniformStageRankBound s.length + 6 =
      (uniformStageRankBound s.length + 3) + 3 by omega, pow_add]
    norm_num
    omega
  rw [he]
  have hp : 0 < 2 ^ (uniformStageRankBound s.length + 3) := by positivity
  omega

/-- The staged computation itself terminates within this singly exponential clock. -/
theorem uniformStages_stop_bound (s : List Bool) :
    (uniformStages s).stop (uniformStageWorkBound s) (uniformStages_work_bound s) + 1 ≤
      2 ^ uniformTimeExponent.eval s.length :=
  (Nat.add_le_add_right ((uniformStages s).stop_bound _ _) 1).trans
    (uniformStages_time_budget s)

end SparseIrred.UpperBounds.Section4
