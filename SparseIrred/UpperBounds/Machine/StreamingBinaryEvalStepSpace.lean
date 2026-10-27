import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalStep
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalDerivativeSpace

/-! # Linear-width space of the complete parsed-term update -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

theorem copySequence_space {n : ℕ} (pairs : List (Fin n × Fin n)) (scratch : Fin n)
    {S W : ℕ → ℕ} {v : ℕ → BinaryValues n} (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (seqList (pairs.map (fun p ↦ binaryCopy p.1 p.2 scratch))) S v W := by
  induction pairs generalizing v with
  | nil => exact SpaceBoundByWidthAt.identity
  | cons p pairs ih =>
    apply SpaceBoundByWidthAt.seq
    · exact SpaceBoundByWidthAt.binaryCopy _ _ _ (fun j ↦ hv j p.1) (fun j ↦ hv j p.2)
    · apply ih
      intro j i
      exact values_update_le p.2 (hv j) (hv j p.1) i

theorem binaryEvalLoadTerm_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt binaryEvalLoadTerm S v W := by
  apply SpaceBoundByWidthAt.seq (clearRegisters_space _ hv)
  apply copySequence_space [(17, 1), (18, 6), (27, 7), (26, 9), (28, 10), (19, 11), (20, 12)] 5
  intro j i
  rw [clearRegisters_effect]
  split_ifs
  · omega
  · exact hv j i

theorem binaryEvalStoreTerm_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt binaryEvalStoreTerm S v W := by
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq
    · exact SpaceBoundByWidthAt.binaryCopy _ _ _ (fun j ↦ hv j 11) (fun j ↦ hv j 19)
    · apply SpaceBoundByWidthAt.binaryCopy <;> intro j <;>
        simpa [binaryCopy] using hv j _
  · apply clearRegisters_space
    intro j i
    exact values_update_le 20 (values_update_le 19 (hv j) (hv j 11))
      (by simpa [binaryCopy] using hv j 12) i

theorem signedTermValues_le (a m e i c sign pos neg r W : ℕ) (extra : Fin 57 → ℕ)
    (ha : a ≤ W) (hm : m ≤ W) (he : e ≤ W) (hi : i ≤ W) (hc : c ≤ W)
    (hs : sign ≤ W) (hp : pos ≤ W) (hn : neg ≤ W) (hr : r ≤ W)
    (hx : ∀ j, extra j ≤ W) (j : Fin 70) :
    signedTermValues a m e i c sign pos neg r extra j ≤ W := by
  rw [signedTermValues_eq]
  refine Fin.addCases (m := 13) (n := 57) (fun j ↦ ?_) (fun j ↦ ?_) j
  · fin_cases j <;> simp [Fin.append, Fin.addCases] <;> omega
  · simpa using hx j

theorem binarySignedEvalTerm_values_le (deriv : Bool) (a m e c sign pos neg W : ℕ)
    (extra : Fin 57 → ℕ) (hm : 0 < m) (ha : a ≤ W) (hmW : m ≤ W) (he : e ≤ W)
    (hc : c ≤ W) (hce : c * e ≤ W) (hs : sign ≤ W) (hp : pos < m) (hn : neg < m)
    (hx : ∀ j, extra j ≤ W) (j : Fin 70) :
    (binarySignedEvalTerm deriv).effect (signedTermValues a m e 0 c sign pos neg 0 extra) j ≤ W := by
  have hpW := hp.le.trans hmW
  have hnW := hn.le.trans hmW
  have hmod : ∀ n, n % m ≤ W := fun n ↦ (Nat.mod_lt n hm).le.trans hmW
  cases deriv
  · rw [binarySignedEvalTerm, ite_eq_right Bool.false_ne_true,
      binarySignedTerm_effect _ _ _ _ _ _ _ _ hm]
    apply signedTermValues_le _ _ _ _ _ _ _ _ _ _ _ ha hmW he he hc hs
    · split_ifs <;> first | exact hmod _ | exact hpW
    · split_ifs <;> first | exact hmod _ | exact hnW
    · omega
    · exact hx
  · simp only [binarySignedEvalTerm, ite_true,
      binarySignedDerivative_effect _ _ _ _ _ _ _ _ hm]
    by_cases he0 : e = 0
    · simp only [he0, ite_true]
      exact signedTermValues_le _ _ _ _ _ _ _ _ _ _ _ ha hmW (by omega) (by omega) hc hs
        hpW hnW (by omega) hx j
    · simp only [he0, ite_false]
      apply signedTermValues_le _ _ _ _ _ _ _ _ _ _ _ ha hmW
        ((Nat.sub_le _ _).trans he) ((Nat.sub_le _ _).trans he) hce hs
      · split_ifs <;> first | exact hmod _ | exact hpW
      · split_ifs <;> first | exact hmod _ | exact hnW
      · omega
      · exact hx

private theorem product_lt_quartic {x y z B : ℕ} (hx : x ≤ B) (hy : y ≤ B) (hz : z ≤ B) :
    x * y * z < (B + 1) ^ 4 := by
  have hprod : x * y * z ≤ B ^ 3 := by
    calc
      _ ≤ B * B * B := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
      _ = _ := by ring
  exact hprod.trans_lt ((Nat.pow_lt_pow_left (Nat.lt_succ_self B) (by decide : 3 ≠ 0)).trans_le
    (Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 4)))

/-- Loading, evaluating, and storing a parsed sparse term all reuse one
polynomial numeric envelope, whose binary width is linear in the input bound. -/
theorem binaryEvalTermStep_space (deriv : Bool) {S B : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ B j) (hm : ∀ j, 0 < v j 17)
    (hp : ∀ j, v j 19 < v j 17) (hn : ∀ j, v j 20 < v j 17) :
    SpaceBoundByWidthAt (binaryEvalTermStep deriv) S v (fun j ↦ (B j + 1) ^ 4) := by
  let W : ℕ → ℕ := fun j ↦ (B j + 1) ^ 4
  have hB : ∀ j, 1 ≤ B j := fun j ↦ (hm j).trans_le (hv j 17)
  have hW : ∀ j i, v j i < W j := fun j i ↦ by
    have h := product_lt_quartic (hv j i) (hB j) (hB j)
    simpa only [Nat.mul_one] using h
  have hB' : ∀ j, B j ≤ W j := by
    intro j
    have h := product_lt_quartic (le_refl (B j)) (hB j) (hB j)
    simpa only [Nat.mul_one] using h.le
  have hmul : ∀ j i q, v j i * v j q < W j := fun j i q ↦ by
    simpa only [Nat.mul_one] using product_lt_quartic (hv j i) (hv j q) (hB j)
  have htriple : ∀ j i q r, v j i * v j q * v j r < W j := fun j i q r ↦
    product_lt_quartic (hv j i) (hv j q) (hv j r)
  have h2m : ∀ j, 2 * v j 17 < W j := by
    intro j
    have hpower : (B j + 1) ^ 2 ≤ (B j + 1) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have h := hv j 17
    dsimp only [W]
    nlinarith [sq_nonneg (B j)]
  have heq : (fun j ↦ binaryEvalLoadTerm.effect (v j)) =
      (fun j ↦ signedTermValues (v j 18) (v j 17) (v j 27) 0 (v j 26) (v j 28)
        (v j 19) (v j 20) 0 (fun i ↦ v j (i.natAdd 13))) :=
    funext (fun j ↦ binaryEvalLoadTerm_effect _)
  apply SpaceBoundByWidthAt.seq
  · exact (binaryEvalLoadTerm_space hv).mono hB'
  · rw [heq]
    apply SpaceBoundByWidthAt.seq
    · exact binarySignedEvalTerm_space deriv _ _ _ _ _ _ _ _ hm S W
        (fun j ↦ (hW j 18).le) (fun j ↦ (hW j 27).le) (fun j ↦ (hW j 26).le)
        (fun j ↦ (hmul j 26 27).le) (fun j ↦ hmul j 18 17) (fun j ↦ hmul j 26 17)
        (fun j ↦ htriple j 26 27 17) hp hn (fun j ↦ hW j 17) h2m
    · apply binaryEvalStoreTerm_space
      intro j i
      exact binarySignedEvalTerm_values_le deriv _ _ _ _ _ _ _ _ _ (hm j)
        (hW j 18).le (hW j 17).le (hW j 27).le (hW j 26).le (hmul j 26 27).le
        (hW j 28).le (hp j) (hn j) (fun q ↦ (hW j _).le) i

/-- The complete term update uses a constant multiple of the original binary
register width, including the derivative's temporary products. -/
theorem binaryEvalTermStep_space_linearWidth (deriv : Bool) {S B : ℕ → ℕ}
    {v : ℕ → BinaryValues 70} (hv : ∀ j i, v j i ≤ B j) (hm : ∀ j, 0 < v j 17)
    (hp : ∀ j, v j 19 < v j 17) (hn : ∀ j, v j 20 < v j 17) :
    SpaceBoundByWidthAt (binaryEvalTermStep deriv) S v B :=
  spaceWidth_pow_add_one 4 (by decide) (binaryEvalTermStep_space deriv hv hm hp hn)

end SparseIrred.UpperBounds.Machine
