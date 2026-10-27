import SparseIrred.UpperBounds.Section4.BinaryInput

/-! # Degree from sparse coefficient queries, including cancellations -/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith

def supportDegree (nonzero : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | e :: es => if nonzero e then max e (supportDegree nonzero es) else supportDegree nonzero es

theorem supportDegree_le (nonzero : ℕ → Bool) (es : List ℕ) (n : ℕ)
    (h : ∀ e ∈ es, nonzero e = true → e ≤ n) : supportDegree nonzero es ≤ n := by
  induction es with
  | nil => exact Nat.zero_le _
  | cons e es ih =>
    have hi := ih (fun k hk ↦ h k (by simp [hk]))
    dsimp only [supportDegree]
    split_ifs with he
    · exact max_le (h e (by simp) he) hi
    · exact hi

theorem le_supportDegree (nonzero : ℕ → Bool) (es : List ℕ) {e : ℕ}
    (he : e ∈ es) (hne : nonzero e = true) : e ≤ supportDegree nonzero es := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · simp [supportDegree, hne]
    · have hi := ih he
      dsimp only [supportDegree]
      split_ifs <;> omega

theorem natDegree_eq_supportDegree {R : Type*} [Semiring R] [DecidableEq R]
    (f : R[X]) (es : List ℕ) (h : ∀ e, f.coeff e ≠ 0 → e ∈ es) :
    f.natDegree = supportDegree (fun e ↦ decide (f.coeff e ≠ 0)) es := by
  apply le_antisymm
  · by_cases hf : f = 0
    · simp [hf]
    · have hc : f.coeff f.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hf
      exact le_supportDegree _ _ (h _ hc) (by simpa using hc)
  · apply supportDegree_le
    intro e he hn
    exact le_natDegree_of_ne_zero (of_decide_eq_true hn)

/-- Candidate exponents are blocks containing binary naturals. A zero-query
callback can itself scan the original sparse input to account for duplicates. -/
def degreeScanStepStr (zero : List Bool → List Bool) (acc exponent : List Bool) : List Bool :=
  caseBit₀ (zero exponent) acc (binaryLt acc exponent (canonBits exponent) acc)

def degreeScanStr (zero : List Bool → List Bool) (exponents : List Bool) : List Bool :=
  foldBlocks (degreeScanStepStr zero) [] exponents

theorem degreeScanStepStr_length (zero : List Bool → List Bool) (acc e : List Bool) :
    (degreeScanStepStr zero acc e).length ≤ acc.length + (e.length + 1) := by
  unfold degreeScanStepStr
  cases h : zero e with
  | nil =>
    simp only [caseBit₀, binaryLt]
    split_ifs
    · have := length_canonBits_le e; omega
    · omega
  | cons b bs =>
    cases b <;> simp only [caseBit₀, Bool.cond_false, Bool.cond_true, binaryLt]
    · split_ifs
      · have := length_canonBits_le e; omega
      · omega
    · omega

theorem cobham_degreeScanStepStr {n : ℕ}
    {zero : (Fin n → List Bool) → List Bool → List Bool}
    (hz : Cobham fun u : Fin (n + 1) → List Bool ↦ zero (Fin.tail u) (u 0))
    {a e : (Fin n → List Bool) → List Bool} (ha : Cobham a) (he : Cobham e) :
    Cobham fun u ↦ degreeScanStepStr (zero u) (a u) (e u) := by
  have hz' := (Cobham.comp hz (gs := fun i u ↦
    (Fin.cons (e u) u : Fin (n + 1) → List Bool) i)
    (fun i ↦ Fin.cases he (fun j ↦ .proj j) i)).of_eq (fun _ ↦ rfl)
  exact Cobham.iteFn hz' ha (cobham_binaryLt ha he (cobham_canonBits_comp he) ha)

theorem cobham_degreeScanStr {n : ℕ}
    {zero : (Fin n → List Bool) → List Bool → List Bool}
    (hz : Cobham fun u : Fin (n + 1) → List Bool ↦ zero (Fin.tail u) (u 0))
    {es : (Fin n → List Bool) → List Bool} (he : Cobham es) :
    Cobham fun u ↦ degreeScanStr (zero u) (es u) := by
  have hquery := (Cobham.comp hz (gs := fun i u ↦
    (Fin.cons (u 1) (Fin.tail (Fin.tail u)) : Fin (n + 1) → List Bool) i)
    (fun i ↦ Fin.cases (.proj 1) (fun j ↦ .proj j.succ.succ) i)).of_eq (fun _ ↦ rfl)
  have hstep : Cobham fun u : Fin (n + 2) → List Bool ↦
      degreeScanStepStr (zero (Fin.tail (Fin.tail u))) (u 0) (u 1) :=
    Cobham.iteFn hquery (.proj 0)
      (cobham_binaryLt (.proj 0) (.proj 1) (cobham_canonBits_comp (.proj 1)) (.proj 0))
  have hf := cobham_foldBlocks hstep (.const []) 1 (by
    intro u; simpa using degreeScanStepStr_length (zero (Fin.tail (Fin.tail u))) (u 0) (u 1))
  exact (Cobham.comp hf (gs := fun i u ↦ (Fin.cons (es u) u : Fin (n + 1) → List Bool) i)
    (fun i ↦ Fin.cases he (fun j ↦ .proj j) i)).of_eq (fun _ ↦ rfl)

theorem degreeScanStr_encoded (zero : List Bool → List Bool) (nz : ℕ → Bool)
    (hz : ∀ e, zero (encNat e) = [!nz e]) (es : List ℕ) :
    degreeScanStr zero (encodeNumerals es) = encNat (supportDegree nz es) := by
  have hstep (a e : ℕ) : degreeScanStepStr zero (encNat a) (encNat e) =
      encNat (if nz e then max a e else a) := by
    simp only [degreeScanStepStr, hz, caseBit₀, binaryLt, decNat_encNat,
      canonBits]
    cases hn : nz e <;> simp only [Bool.not_false, Bool.not_true, Bool.cond_false,
      Bool.cond_true, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, decNat_encNat]
    split_ifs with he
    · rw [max_eq_right (Nat.le_of_lt he)]
    · rw [max_eq_left (Nat.le_of_not_gt he)]
  have hfold (xs : List ℕ) (a : ℕ) :
      (xs.map encNat).foldl (degreeScanStepStr zero) (encNat a) =
        encNat (max a (supportDegree nz xs)) := by
    induction xs generalizing a with
    | nil => simp [supportDegree]
    | cons e xs ih =>
      rw [List.map_cons, List.foldl_cons, hstep, ih]
      cases hn : nz e <;> simp [supportDegree, hn, max_assoc]
  rw [degreeScanStr, encodeNumerals, foldBlocks_frame]
  change (es.map encNat).foldl (degreeScanStepStr zero) (encNat 0) = _
  rw [hfold, zero_max]

/-- A fully uniform binary degree query, when the candidates cover the support. -/
theorem degreeScanStr_polynomial {R : Type*} [Semiring R] [DecidableEq R]
    (f : R[X]) (es : List ℕ) (zero : List Bool → List Bool)
    (hz : ∀ e, zero (encNat e) = [decide (f.coeff e = 0)])
    (hs : ∀ e, f.coeff e ≠ 0 → e ∈ es) :
    degreeScanStr zero (encodeNumerals es) = encNat f.natDegree := by
  rw [degreeScanStr_encoded zero (fun e ↦ decide (f.coeff e ≠ 0))
    (by intro e; simpa using hz e)]
  rw [← natDegree_eq_supportDegree f es hs]

end SparseIrred.UpperBounds.Section4
