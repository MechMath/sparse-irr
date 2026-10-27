import SparseIrred.Machine.Data
import SparseIrred.Construction.Laurent
import SparseIrred.Reduction.Defs

/-!
# Correctness of the data-level algorithm: `canonTerms (H_M) = hmCore …`

This file proves that the computable algorithm of `Machine/Data.lean` computes the canonical term
lists of the polynomials of `Construction/Defs.lean` (`varIdx`/`numVars` renumbering,
`oddPrime = Nat.nth`, `Spoly`/`Dexp`/`Apoly`, `wParam`/`mParam`/`Mval`), and that `reduceTerms`
follows the branches of `reducePoly`.

## Main results

* `canonTerms_Apoly`: `canonTerms (Apoly Φ) = hmA (oddPrimeList (numVars Φ)) (renumber Φ)`;
* `canonTerms_Hfinal`: `canonTerms (Hfinal Φ) = hmCore (oddPrimeList (numVars Φ)) (renumber Φ)`;
* `canonTerms_reducePoly`: `canonTerms (reducePoly x) = reduceTerms x`;
* `reduce_eq_encITerms`: `reduce x = encITerms (reduceTerms x)`.

The Laurent polynomial `S` is handled by the offset trick: the raw list `sRawD K Cs` denotes
`X^K S(X)` (`toLaurent_toPolyZ_sNormD`), and the smallest exponent of its canonical list is
`K - D` (`headExpD_sNormD_add_Dexp`).  The facts used about the construction are `bigN_pos`,
`varIdx_lt_numVars`, `Spoly_coeff_eq_zero_of_lt`, `Spoly_coeff_Dexp_ne_zero` and `Apoly_coeff`
(`Construction/Laurent.lean`).
-/

open Polynomial LaurentPolynomial Complexity.SAT SparseDiv.Appendix

namespace SparseIrred.Machine

open SparseIrred

/-! ### Primes and literals -/

theorem prod_oddPrimeList (Φ : CNF) : (oddPrimeList (numVars Φ)).prod = bigN Φ := by
  rw [bigN]
  induction numVars Φ with
  | zero => rfl
  | succ n ih =>
    rw [oddPrimeList, List.range_succ, List.map_append, List.prod_append, ← oddPrimeList, ih,
      Finset.prod_range_succ]
    simp

theorem getD_oddPrimeList {n i : ℕ} (hi : i < n) : (oddPrimeList n).getD i 0 = oddPrime i := by
  simp [oddPrimeList, List.getD_eq_getElem?_getD, hi]

theorem toPolyZ_litTermsD (Φ : CNF) (l : Lit) (hl : Occurs Φ l.var) :
    toPolyZ (litTermsD (oddPrimeList (numVars Φ)) (bigN Φ) (renumLit Φ l)) = litPoly Φ l := by
  have hi := varIdx_lt_numVars Φ hl
  unfold litTermsD litPoly renumLit
  simp only [getD_oddPrimeList hi]
  cases l.sign
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [toPolyZ_negLitTerms]
    rfl
  · simp only [↓reduceIte]
    rw [toPolyZ_posLitTerms]
    rfl

theorem toPolyZ_clauseTermsD (Φ : CNF) {c : Clause} (hc : c ∈ Φ) :
    toPolyZ (clauseTermsD (oddPrimeList (numVars Φ)) (bigN Φ) (c.map (renumLit Φ))) =
      clausePoly Φ c := by
  have key : ∀ d : Clause, (∀ l ∈ d, Occurs Φ l.var) →
      toPolyZ (clauseTermsD (oddPrimeList (numVars Φ)) (bigN Φ) (d.map (renumLit Φ))) =
        (d.map (litPoly Φ)).prod := by
    intro d
    induction d with
    | nil => intro _; simp [clauseTermsD, toPolyZ]
    | cons l d ih =>
      intro hd
      rw [List.map_cons, clauseTermsD, List.foldr_cons, ← clauseTermsD, toPolyZ_mulITerms,
        toPolyZ_litTermsD Φ l (hd l List.mem_cons_self),
        ih fun l' hl' => hd l' (List.mem_cons_of_mem _ hl'), List.map_cons, List.prod_cons]
  exact key c fun l hl => ⟨c, hc, l, hl, rfl⟩

theorem clauseListD_renumber (Φ : CNF) :
    clauseListD (oddPrimeList (numVars Φ)) (renumber Φ) =
      Φ.map fun c => clauseTermsD (oddPrimeList (numVars Φ)) (bigN Φ) (c.map (renumLit Φ)) := by
  rw [clauseListD, renumber, List.map_map, prod_oddPrimeList]
  rfl

/-! ### Laurent bookkeeping: the offset trick -/

theorem coeff_toLaurent_natCast (P : ℤ[X]) (j : ℕ) : (toLaurent P).coeff (j : ℤ) = P.coeff j := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ j

theorem coeff_toLaurent_of_neg (P : ℤ[X]) {n : ℤ} (hn : n < 0) : (toLaurent P).coeff n = 0 := by
  rw [coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, rfl⟩
  simp at hn
  omega

theorem coeff_T_mul (f : ℤ[T;T⁻¹]) (n m : ℤ) : (T n * f).coeff m = f.coeff (m - n) := by
  rw [T_mul, T, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

theorem toLaurent_toPolyZ_reflectITerms (K : ℕ) (l : ITerms) (hK : ∀ t ∈ l, t.2 ≤ K) :
    toLaurent (toPolyZ (reflectITerms K l)) = T (K : ℤ) * invert (toLaurent (toPolyZ l)) := by
  induction l with
  | nil => simp [reflectITerms]
  | cons t l ih =>
    have ht : t.2 ≤ K := hK t List.mem_cons_self
    rw [reflectITerms, List.map_cons, ← reflectITerms, toPolyZ_cons, toPolyZ_cons, map_add, map_add,
      map_add, ih fun u hu => hK u (List.mem_cons_of_mem _ hu), toLaurent_C_mul_X_pow,
      toLaurent_C_mul_X_pow, map_mul, invert_C, invert_T,
      show ((K - t.2 : ℕ) : ℤ) = (K : ℤ) + -(t.2 : ℤ) by push_cast [Nat.cast_sub ht]; ring, T_add]
    ring

theorem toLaurent_toPolyZ_sRawD (K : ℕ) (Cs : List ITerms) (hK : ∀ C ∈ Cs, ∀ t ∈ C, t.2 ≤ K) :
    toLaurent (toPolyZ (sRawD K Cs)) =
      T (K : ℤ) * (Cs.map fun C => toLaurent (toPolyZ C) * invert (toLaurent (toPolyZ C))).sum := by
  induction Cs with
  | nil => simp [sRawD]
  | cons C Cs ih =>
    rw [sRawD, List.flatMap_cons, ← sRawD, toPolyZ_append, map_add, toPolyZ_mulITerms, map_mul,
      toLaurent_toPolyZ_reflectITerms K C (hK C List.mem_cons_self),
      ih fun C' hC' => hK C' (List.mem_cons_of_mem _ hC'), List.map_cons, List.sum_cons]
    ring

/-- The collected list `sNormD` denotes `X^K S(X)`, where `K` is the offset. -/
theorem toLaurent_toPolyZ_sNormD (Φ : CNF) :
    toLaurent (toPolyZ (sNormD (oddPrimeList (numVars Φ)) (renumber Φ))) =
      T (offsetD (clauseListD (oddPrimeList (numVars Φ)) (renumber Φ)) : ℤ) * Spoly Φ := by
  have hK : ∀ C ∈ clauseListD (oddPrimeList (numVars Φ)) (renumber Φ), ∀ t ∈ C,
      t.2 ≤ offsetD (clauseListD (oddPrimeList (numVars Φ)) (renumber Φ)) :=
    fun C hC t ht => le_offsetD hC ht
  rw [sNormD, toPolyZ_normalizeZ, toLaurent_toPolyZ_sRawD _ _ hK, Spoly]
  congr 1
  rw [clauseListD_renumber, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun c hc => ?_)
  simp only [Function.comp_apply, toPolyZ_clauseTermsD Φ hc]

theorem coeff_eq_of_toLaurent_eq {P : ℤ[X]} {K : ℕ} {S : ℤ[T;T⁻¹]}
    (h : toLaurent P = T (K : ℤ) * S) (j : ℕ) : P.coeff j = S.coeff ((j : ℤ) - K) := by
  have := congrArg (fun f : ℤ[T;T⁻¹] => f.coeff (j : ℤ)) h
  simpa only [coeff_toLaurent_natCast, coeff_T_mul] using this

theorem headExpD_le {s : ITerms} (hs : s.Pairwise (fun a b => a.2 < b.2)) :
    ∀ t ∈ s, headExpD s ≤ t.2 := by
  cases s with
  | nil => simp
  | cons t₀ rest =>
    intro t ht
    rw [headExpD_cons]
    rcases List.mem_cons.1 ht with rfl | h
    · exact le_rfl
    · exact ((List.pairwise_cons.1 hs).1 t h).le

/-- The head exponent of a canonical list is the trailing degree. -/
theorem headExpD_eq_natTrailingDegree {l : ITerms} (hl : NormalizedZ l) :
    headExpD l = (toPolyZ l).natTrailingDegree := by
  cases l with
  | nil => simp [headExpD_nil]
  | cons t rest =>
    have hc : (toPolyZ (t :: rest)).coeff t.2 = t.1 :=
      coeff_toPolyZ_of_normalizedZ_mem hl List.mem_cons_self
    have hne : (toPolyZ (t :: rest)).coeff t.2 ≠ 0 := by
      rw [hc]
      exact hl.2 t List.mem_cons_self
    have hp : toPolyZ (t :: rest) ≠ 0 := fun h0 => hne (by rw [h0, coeff_zero])
    rw [headExpD_cons]
    refine le_antisymm (le_natTrailingDegree hp fun m hm => ?_)
      (natTrailingDegree_le_of_ne_zero hne)
    by_contra hm0
    have hmem : m ∈ (toPolyZ (t :: rest)).support := mem_support_iff.2 hm0
    rw [support_toPolyZ_of_normalizedZ hl, List.mem_toFinset, List.mem_map] at hmem
    obtain ⟨u, hu, rfl⟩ := hmem
    have := headExpD_le hl.1 u hu
    rw [headExpD_cons] at this
    omega

/-- The smallest exponent of `X^K S` is `K - D` (and `D ≤ K`), where `K` is the offset. -/
theorem headExpD_sNormD_add_Dexp (Φ : CNF) (hΦ : Φ ≠ []) :
    headExpD (sNormD (oddPrimeList (numVars Φ)) (renumber Φ)) + Dexp Φ =
      offsetD (clauseListD (oddPrimeList (numVars Φ)) (renumber Φ)) := by
  set K := offsetD (clauseListD (oddPrimeList (numVars Φ)) (renumber Φ)) with hK
  set s := sNormD (oddPrimeList (numVars Φ)) (renumber Φ) with hs
  have hL := toLaurent_toPolyZ_sNormD Φ
  rw [← hK, ← hs] at hL
  have hS := Spoly_coeff_Dexp_ne_zero Φ hΦ
  have hsN : NormalizedZ s := normalizedZ_normalizeZ _
  -- `D ≤ K`: the coefficient of `T^K S` at `K - D` is `S_{-D} ≠ 0`
  have hDK : Dexp Φ ≤ K := by
    by_contra hlt
    have h1 := congrArg (fun f : ℤ[T;T⁻¹] => f.coeff ((K : ℤ) - Dexp Φ)) hL
    simp only [coeff_T_mul, sub_sub_cancel_left] at h1
    rw [coeff_toLaurent_of_neg _ (by omega)] at h1
    exact hS.2 h1.symm
  have hcoeff : ∀ j : ℕ, (toPolyZ s).coeff j = (Spoly Φ).coeff ((j : ℤ) - K) :=
    coeff_eq_of_toLaurent_eq hL
  have hne : (toPolyZ s).coeff (K - Dexp Φ) ≠ 0 := by
    rw [hcoeff, Nat.cast_sub hDK]
    simpa using hS.2
  have hp : toPolyZ s ≠ 0 := fun h0 => hne (by rw [h0, coeff_zero])
  have htr : (toPolyZ s).natTrailingDegree = K - Dexp Φ := by
    refine le_antisymm (natTrailingDegree_le_of_ne_zero hne)
      (le_natTrailingDegree hp fun m hm => ?_)
    rw [hcoeff]
    apply Spoly_coeff_eq_zero_of_lt
    rw [abs_of_neg (by omega)]
    omega
  rw [headExpD_eq_natTrailingDegree hsN, htr]
  omega

theorem coeff_toPolyZ_aTermsD {s : ITerms} (hs : NormalizedZ s) (k : ℕ) :
    (toPolyZ (aTermsD s)).coeff k = 3 * (toPolyZ s).coeff (k + headExpD s) := by
  have key : ∀ (l : ITerms) (h : ℕ), (∀ t ∈ l, h ≤ t.2) →
      toPolyZ (l.map fun t => (3 * t.1, t.2 - h)) * X ^ h = Polynomial.C 3 * toPolyZ l := by
    intro l h hl
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.map_cons, toPolyZ_cons, toPolyZ_cons, add_mul,
        ih fun u hu => hl u (List.mem_cons_of_mem _ hu), mul_assoc, ← pow_add,
        Nat.sub_add_cancel (hl t List.mem_cons_self), C_mul]
      ring
  have h := key s (headExpD s) (headExpD_le hs.1)
  have := congrArg (fun p : ℤ[X] => p.coeff (k + headExpD s)) h
  simpa only [coeff_mul_X_pow, coeff_C_mul, aTermsD] using this

/-! ### `A` -/

theorem toPolyZ_hmA (Φ : CNF) (hΦ : Φ ≠ []) :
    toPolyZ (hmA (oddPrimeList (numVars Φ)) (renumber Φ)) = Apoly Φ := by
  ext k
  have hs : NormalizedZ (sNormD (oddPrimeList (numVars Φ)) (renumber Φ)) := normalizedZ_normalizeZ _
  have hsum := headExpD_sNormD_add_Dexp Φ hΦ
  rw [hmA, coeff_toPolyZ_aTermsD hs, coeff_eq_of_toLaurent_eq (toLaurent_toPolyZ_sNormD Φ),
    Apoly_coeff]
  congr 2
  push_cast
  omega

theorem normalizedZ_hmA (qs : List ℕ) (Ψ : CNF) : NormalizedZ (hmA qs Ψ) := by
  exact normalizedZ_aTermsD (normalizedZ_normalizeZ _)

theorem canonTerms_Apoly (Φ : CNF) (hΦ : Φ ≠ []) :
    canonTerms (Apoly Φ) = hmA (oddPrimeList (numVars Φ)) (renumber Φ) := by
  rw [← toPolyZ_hmA Φ hΦ]
  exact canonTerms_toPolyZ (normalizedZ_hmA _ _)

/-! ### Weights, counts and degrees read off canonical lists -/

theorem weight_eq_sqSumD (f : ℤ[X]) : weight f = sqSumD (canonTerms f) := by
  rw [weight, sqSumD, canonTerms, List.map_map, Finset.sum_eq_multiset_sum,
    ← Finset.sort_eq f.support (· ≤ ·), Multiset.map_coe, Multiset.sum_coe]
  rfl

theorem termCount_eq_length (f : ℤ[X]) : termCount f = (canonTerms f).length := by
  rw [termCount, ← card_support_toPolyZ_of_normalizedZ (canonTerms_normalizedZ f),
    toPolyZ_canonTerms]

theorem natDegree_eq_degreeZ (f : ℤ[X]) : f.natDegree = degreeZ (canonTerms f) := by
  rw [← natDegree_toPolyZ_of_normalizedZ (canonTerms_normalizedZ f), toPolyZ_canonTerms]

theorem canonTerms_cPoly (Φ : CNF) : canonTerms (cPoly Φ) = [(1, 0), (-1, bigN Φ)] := by
  have hN := bigN_pos Φ
  have hn : NormalizedZ [((1 : ℤ), 0), (-1, bigN Φ)] := ⟨by simp [hN], by simp⟩
  have ht : toPolyZ [((1 : ℤ), 0), (-1, bigN Φ)] = cPoly Φ := by
    simp [cPoly, toPolyZ]
    ring
  rw [← ht, canonTerms_toPolyZ hn]

theorem wParam_eq (Φ : CNF) (hΦ : Φ ≠ []) :
    wParam Φ = wD (hmA (oddPrimeList (numVars Φ)) (renumber Φ)) := by
  rw [wParam, weight_eq_sqSumD, weight_eq_sqSumD, termCount_eq_length, termCount_eq_length,
    canonTerms_cPoly, canonTerms_Apoly Φ hΦ, wD]
  simp [sqSumD]
  omega

theorem mParam_eq (Φ : CNF) (hΦ : Φ ≠ []) :
    mParam Φ = mD (bigN Φ) (hmA (oddPrimeList (numVars Φ)) (renumber Φ)) := by
  rw [mParam, natDegree_eq_degreeZ (cPoly Φ), natDegree_eq_degreeZ (Apoly Φ), canonTerms_cPoly,
    canonTerms_Apoly Φ hΦ, mD]
  simp [degreeZ]

theorem Mval_eq (Φ : CNF) (hΦ : Φ ≠ []) :
    Mval Φ = MD (bigN Φ) (hmA (oddPrimeList (numVars Φ)) (renumber Φ)) := by
  rw [Mval, MD, wParam_eq Φ hΦ, mParam_eq Φ hΦ]

/-- **The bridge.** The canonical list of `H_M` is computed by the data-level algorithm. -/
theorem canonTerms_Hfinal (Φ : CNF) (hΦ : Φ ≠ []) :
    canonTerms (Hfinal Φ) = hmCore (oddPrimeList (numVars Φ)) (renumber Φ) := by
  rw [hmCore, prod_oddPrimeList]
  have h : Hfinal Φ =
      toPolyZ (outTermsD (bigN Φ) (hmA (oddPrimeList (numVars Φ)) (renumber Φ))) := by
    rw [toPolyZ_outTermsD, toPolyZ_hmA Φ hΦ, ← Mval_eq Φ hΦ, Hfinal, Hpoly, Bpoly]
  rw [h, canonTerms_toPolyZ (normalizedZ_outTermsD (normalizedZ_hmA _ _) (bigN_pos Φ))]

/-! ### The branches of `reducePoly` -/

theorem numVars_ne_zero_of_is3CNF {Φ : CNF} (h3 : Φ.Is3CNF) (hΦ : Φ ≠ []) : numVars Φ ≠ 0 := by
  obtain ⟨c, Ψ, rfl⟩ := List.exists_cons_of_ne_nil hΦ
  have hc : c.length = 3 := h3 c List.mem_cons_self
  obtain ⟨l, hl⟩ : ∃ l, l ∈ c := List.exists_mem_of_length_pos (by omega)
  have hocc : Occurs (c :: Ψ) l.var := ⟨c, List.mem_cons_self, l, hl, rfl⟩
  have := varIdx_lt_numVars _ hocc
  omega

theorem numVars_le_encode_length (Φ : CNF) : numVars Φ ≤ Φ.encode.length + 1 := by
  have h1 : numVars Φ ≤ Φ.maxVar + 1 := by
    rw [numVars, varList]
    exact (List.length_filter_le _ _).trans (by simp)
  have h2 := CNF.maxVar_le_encode_length Φ
  omega

theorem canonTerms_X : canonTerms (X : ℤ[X]) = [(1, 1)] := by
  have hn : NormalizedZ [((1 : ℤ), 1)] := ⟨by simp, by simp⟩
  have ht : toPolyZ [((1 : ℤ), 1)] = X := by simp [toPolyZ]
  rw [← ht, canonTerms_toPolyZ hn]

theorem canonTerms_X_sq_sub_one : canonTerms (X ^ 2 - 1 : ℤ[X]) = [(-1, 0), (1, 2)] := by
  have hn : NormalizedZ [((-1 : ℤ), 0), (1, 2)] := ⟨by simp, by simp⟩
  have ht : toPolyZ [((-1 : ℤ), 0), (1, 2)] = X ^ 2 - 1 := by
    simp [toPolyZ]
    ring
  rw [← ht, canonTerms_toPolyZ hn]

/-- On the code `Φ.encode` of a CNF, the prime list computed by the algorithm (the first
`numVars Φ` odd primes below `primeBound |Φ.encode|`) is `oddPrimeList (numVars Φ)`. -/
theorem firstOddPrimes_encode (Φ : CNF) :
    firstOddPrimes (primeBound Φ.encode.length) (numVars Φ) = oddPrimeList (numVars Φ) :=
  firstOddPrimes_primeBound (numVars_le_encode_length Φ)

theorem hmTerms_encode (Φ : CNF) :
    hmTerms (primeBound Φ.encode.length) Φ = hmCore (oddPrimeList (numVars Φ)) (renumber Φ) := by
  rw [hmTerms, firstOddPrimes_encode]

/-- **Data-level form of the reduction.** -/
theorem canonTerms_reducePoly (x : List Bool) : canonTerms (reducePoly x) = reduceTerms x := by
  unfold reducePoly reduceTerms
  rcases h : CNF.decode3? x with _ | Φ
  · exact canonTerms_X
  · obtain ⟨rfl, h3⟩ := CNF.decode3?_eq_some_iff.1 h
    by_cases hΦ : Φ = []
    · subst hΦ
      simp [CNF.satisfiable_nil, canonTerms_X_sq_sub_one]
    · have hn := numVars_ne_zero_of_is3CNF h3 hΦ
      simp only [hΦ, hn, or_self, ite_false]
      rw [canonTerms_Hfinal Φ hΦ, hmTerms_encode]

theorem reduce_eq_encITerms (x : List Bool) : reduce x = encITerms (reduceTerms x) := by
  rw [reduce, encPoly, canonTerms_reducePoly]

end SparseIrred.Machine
