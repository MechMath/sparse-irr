import SparseIrred.UpperBounds.Machine.StreamingProgram
import SparseIrred.UpperBounds.PrimeStreaming

/-!
# Exact semantics of the deterministic rectangular enumeration

The single loop index `i < X*X` enumerates `(p,a) = (i / X, i % X)`.
The padding residues `a ≥ p` contribute zero, so the rectangular traversal has
exactly the counts of the paper's triangular loop `p < X, a < p`.
-/

open Polynomial Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith SparseGcd
open scoped BigOperators

namespace SparseIrred.UpperBounds.Machine

/-- Quotient and remainder enumerate the entire rectangle exactly once. -/
theorem sum_rectangle_div_mod (X : ℕ) (F : ℕ → ℕ → ℕ) :
    (∑ i ∈ Finset.range (X * X), F (i / X) (i % X)) =
      ∑ p ∈ Finset.range X, ∑ a ∈ Finset.range X, F p a := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ z : Fin X × Fin X, F z.1.val z.2.val :=
      Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun i ↦ rfl)
    _ = ∑ p : Fin X, ∑ a : Fin X, F p.val a.val := Fintype.sum_prod_type _
    _ = _ := by
      simp_rw [Fin.sum_univ_eq_sum_range]
      exact Fin.sum_univ_eq_sum_range (fun p ↦ ∑ a ∈ Finset.range X, F p a) X

/-- Evaluation flags on the canonical numeric arguments give the modular-root predicate. -/
theorem sparseEvalModStr_nat_isZero_iff (deriv : Bool) (p a : ℕ)
    (l : ITerms) (hp : p ≠ 0) :
    isZeroBits (sparseEvalModStr deriv (encNat p) (encNat a) (encITerms l)) = [true] ↔
      (if deriv then
        ((toPolyZ l).map (Int.castRingHom (ZMod p))).derivative.eval (a : ZMod p)
      else ((toPolyZ l).map (Int.castRingHom (ZMod p))).eval (a : ZMod p)) = 0 := by
  have hpenc := decNat_encNat p
  have haenc := decNat_encNat a
  generalize encNat p = ps at *
  generalize encNat a = as at *
  subst p a
  exact sparseEvalModStr_isZero_iff deriv ps as l hp


/-- Every position changes the prime counter by at most one. -/
theorem streamPrimeIncrement_le (p a : ℕ) : streamPrimeIncrement p a ≤ 1 := by
  simp only [streamPrimeIncrement]
  split_ifs <;> omega

/-- Every position changes the weighted root counter by at most two. -/
theorem streamRootIncrement_le (s : List Bool) (p a : ℕ) :
    streamRootIncrement s p a ≤ 2 := by
  unfold streamRootIncrement
  split_ifs <;> omega

/-- The exact update invariant for the binary accumulators. -/
theorem streamCounts_succ (s : List Bool) (X t : ℕ) :
    streamCounts s X (t + 1) =
      ((streamCounts s X t).1 + streamPrimeIncrement (t / X) (t % X),
       (streamCounts s X t).2 + streamRootIncrement s (t / X) (t % X)) := by
  simp only [streamCounts, Finset.sum_range_succ]

@[simp] theorem streamCounts_zero (s : List Bool) (X : ℕ) :
    streamCounts s X 0 = (0, 0) := by simp [streamCounts]

/-- Prefix bounds hold for every encoded input, even a malformed one. -/
theorem streamCounts_bounds (s : List Bool) (X t : ℕ) :
    (streamCounts s X t).1 ≤ t ∧ (streamCounts s X t).2 ≤ 2 * t := by
  constructor
  · calc
      _ ≤ ∑ _i ∈ Finset.range t, 1 :=
        Finset.sum_le_sum fun i _ ↦ streamPrimeIncrement_le (i / X) (i % X)
      _ = _ := by simp
  · calc
      _ ≤ ∑ _i ∈ Finset.range t, 2 :=
        Finset.sum_le_sum fun i _ ↦ streamRootIncrement_le s (i / X) (i % X)
      _ = _ := by simp [Nat.mul_comm]

/-- On a genuine prime, the implemented increment is the modular-root increment,
with zero contribution from padding residues. -/
theorem streamRootIncrement_eq (l : ITerms) (p a : ℕ) (hp : p.Prime) :
    streamRootIncrement (encITerms l) p a =
      if a < p then modularRootIncrement (toPolyZ l) p a else 0 := by
  classical
  have hroot := sparseEvalModStr_nat_isZero_iff false p a l hp.ne_zero
  have hderiv := sparseEvalModStr_nat_isZero_iff true p a l hp.ne_zero
  simp only [Bool.false_eq_true, ↓reduceIte] at hroot
  simp only [↓reduceIte] at hderiv
  simp only [streamRootIncrement, hp, true_and, hroot, hderiv, modularRootIncrement]
  split_ifs <;> simp_all

/-- A row contributes exactly one if its candidate is prime. -/
theorem sum_streamPrimeIncrement (X p : ℕ) (hX : 0 < X) :
    (∑ a ∈ Finset.range X, streamPrimeIncrement p a) = if p.Prime then 1 else 0 := by
  by_cases hp : p.Prime <;> simp [streamPrimeIncrement, hp, hX]

/-- Removing the zero padding leaves precisely the full modular scan. -/
theorem sum_streamRootIncrement (l : ITerms) (X p : ℕ) (hpX : p < X) :
    (∑ a ∈ Finset.range X, streamRootIncrement (encITerms l) p a) =
      primeRootWeight (toPolyZ l) p := by
  classical
  by_cases hp : p.Prime
  · calc
      _ = ∑ a ∈ Finset.range p, streamRootIncrement (encITerms l) p a := by
        symm
        apply Finset.sum_subset (Finset.range_mono hpX.le)
        intro a _ ha
        have hpa : ¬a < p := by simpa only [Finset.mem_range] using ha
        simp [streamRootIncrement, hpa]
      _ = ∑ a ∈ Finset.range p, modularRootIncrement (toPolyZ l) p a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [streamRootIncrement_eq l p a hp, ite_eq_left (Finset.mem_range.mp ha)]
      _ = modularRootScan (toPolyZ l) p := by
        simp [modularRootScan, modularRootScanAux_eq_sum]
      _ = _ := modularRootScan_eq_primeRootWeight _ p hp
  · simp [streamRootIncrement, hp, primeRootWeight]

/-- Complete rectangular enumeration produces exactly the two paper counters.
Normalization is not needed for this counting identity. -/
theorem streamCounts_eq_counts (l : ITerms) (X : ℕ) :
    streamCounts (encITerms l) X (X * X) =
      (primeCountBelow X, primeRootSum (toPolyZ l) X) := by
  classical
  apply Prod.ext
  · change (∑ i ∈ Finset.range (X * X), streamPrimeIncrement (i / X) (i % X)) = _
    rw [sum_rectangle_div_mod]
    calc
      _ = ∑ p ∈ Finset.range X, if p.Prime then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact sum_streamPrimeIncrement X p (by have := Finset.mem_range.mp hp; omega)
      _ = _ := by rw [Finset.sum_boole]; rfl
  · change (∑ i ∈ Finset.range (X * X),
      streamRootIncrement (encITerms l) (i / X) (i % X)) = _
    rw [sum_rectangle_div_mod]
    calc
      _ = ∑ p ∈ Finset.range X, primeRootWeight (toPolyZ l) p :=
        Finset.sum_congr rfl fun p hp ↦ sum_streamRootIncrement l X p (Finset.mem_range.mp hp)
      _ = _ := by
        rw [primeRootSum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : p.Prime <;> simp [hp, primeRootWeight]

/-- Both counters are monotone as more positions are enumerated. -/
theorem streamCounts_mono (s : List Bool) (X t u : ℕ) (htu : t ≤ u) :
    (streamCounts s X t).1 ≤ (streamCounts s X u).1 ∧
      (streamCounts s X t).2 ≤ (streamCounts s X u).2 := by
  constructor <;> exact Finset.sum_le_sum_of_subset (Finset.range_mono htu)

/-- Every running prefix satisfies the sharper counter bounds stated in Section 3.6. -/
theorem streamCounts_prefix_bounds (l : ITerms) (hf : (toPolyZ l).IsPrimitive)
    (X t : ℕ) (ht : t ≤ X * X) :
    (streamCounts (encITerms l) X t).1 ≤ X ∧
      (streamCounts (encITerms l) X t).2 ≤ 2 * (toPolyZ l).natDegree * X := by
  have h := streamCounts_mono (encITerms l) X t (X * X) ht
  rw [streamCounts_eq_counts] at h
  have hfull := prime_counter_bounds (toPolyZ l) hf X
  exact ⟨h.1.trans hfull.1, h.2.trans hfull.2⟩

/-- The implemented cutoff agrees with the proved arithmetic cutoff on canonical inputs. -/
theorem streamCutoff_encITerms (C₀ : ℕ) (l : ITerms) (hl : NormalizedZ l) :
    streamCutoff C₀ (encITerms l) = primeCountingCutoff C₀ (toPolyZ l) := by
  have hd := (decodeTerms_eq_some_iff (encITerms l) l).mpr ⟨hl, rfl⟩
  rw [streamCutoff, cutoffUnary_eq C₀ _ l hd]
  simp only [unaryN, List.length_replicate,
    termCutoffExponent_eq C₀ l hl, primeCountingCutoff]

/-- Exact meaning of the implemented final comparison on canonical input. -/
theorem streamVerdict_encITerms (l : ITerms) (hl : NormalizedZ l) (P A : ℕ) :
    streamVerdict (encITerms l) P A = true ↔
      if degreeZ l = 0 then (contentZ l).Prime
      else contentZ l = 1 ∧ 2 * A < 3 * P := by
  have hvalid : validCode (encITerms l) = [true] :=
    (validCode_eq_true_iff _).mpr ⟨l, (decodeTerms_eq_some_iff _ _).mpr ⟨hl, rfl⟩⟩
  simp only [streamVerdict, streamVerdictStr, hvalid, caseBit₀_cons, Bool.cond_true,
    isZeroBits_eq_decide_decNat, decNat_degreeStr, binaryPrimeFlag, decNat_contentStr,
    eqBits_eq_decide_decNat, decNat_cons, decNat_nil, ltBits_eq_decide_decNat,
    decNat_mulBits, decNat_encNat, andBit_single]
  by_cases hd : degreeZ l = 0 <;> simp [hd]

/-- The complete numerical enumeration and final comparison decide irreducibility. -/
theorem streamVerdict_counts_encITerms (C₀ : ℕ) (l : ITerms) (hl : NormalizedZ l)
    (hC : 1 ≤ C₀) (hExternal : UniformPrimeIdealEstimate C₀) :
    let X := streamCutoff C₀ (encITerms l)
    streamVerdict (encITerms l) (streamCounts (encITerms l) X (X * X)).1
      (streamCounts (encITerms l) X (X * X)).2 = true ↔ Irreducible (toPolyZ l) := by
  dsimp only
  rw [streamCutoff_encITerms C₀ l hl, streamCounts_eq_counts, streamVerdict_encITerms l hl]
  have h := (rawList_irreducible_iff_primeCounting_test C₀ l hC hExternal).symm
  rw [natDegree_toPolyZ_of_normalizedZ hl] at h
  by_cases hd : degreeZ l = 0
  · simpa only [hd, ↓reduceIte, contentZ_eq_natAbs_constant l hl hd,
      termConstantCoefficient_eq] using h
  · simpa only [hd, ↓reduceIte, contentZ_eq_one_iff l hl] using h

/-- Every input, including malformed encodings, has the intended final language decision. -/
theorem streamVerdict_counts_iff_mem_IrredLang (C₀ : ℕ)
    (hC : 1 ≤ C₀) (hExternal : UniformPrimeIdealEstimate C₀) (s : List Bool) :
    let X := streamCutoff C₀ s
    streamVerdict s (streamCounts s X (X * X)).1
      (streamCounts s X (X * X)).2 = true ↔ s ∈ IrredLang := by
  cases hdecode : decodeTerms s with
  | none =>
    have hpoly : decodePoly s = none := by rw [decodePoly_eq_map_decodeTerms, hdecode]; rfl
    have hn := not_mem_IrredLang_of_decodePoly_eq_none hpoly
    simp [streamVerdict, streamVerdictStr, validCode_eq_false_of_decode_none s hdecode,
      caseBit₀_cons, hn]
  | some l =>
    obtain ⟨hl, hs⟩ := (decodeTerms_eq_some_iff s l).mp hdecode
    rw [← hs]
    have hcode : encPoly (toPolyZ l) = encITerms l := by
      simp only [encPoly, canonTerms_toPolyZ hl]
    have hv := streamVerdict_counts_encITerms C₀ l hl hC hExternal
    dsimp only at hv ⊢
    rw [hv, ← hcode, encPoly_mem_IrredLang_iff]

end SparseIrred.UpperBounds.Machine
