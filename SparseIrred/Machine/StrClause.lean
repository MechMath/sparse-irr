import SparseIrred.Machine.StrArith
import SparseIrred.Machine.StrPrimes

/-!
# Literal and clause raw term lists as strings

The prime list is `frame (qs.map unaryN)` and `N = encNat qs.prod`; a literal block is
`encLitU l = pair [l.sign] (unaryN l.var)` of the *renumbered* formula (so `l.var` indexes `qs`).

* `litStr` — `encITerms (litTermsD qs N l)`: `P⁺ = [(-1,0),(1,m)]`, `P⁻ = [(1, r m) | r < q]` with
  `q = qs.getD l.var 0` read by `nthBlockStr` (default block `[] = unaryN 0`) and
  `m = N / q` by `TermsStr.divBits₀` (total, `N / 0 = 0`);
* `clauseStr` — `encITerms (clauseTermsD qs N c)` for clauses of at most three literals: the
  product is unrolled exactly three times (`TermsStr.cobham_iterate`) from the reversed literal
  list, matching the `foldr` of `clauseTermsD` (the same scheme as `SparseGcd.clauseTermsStr`).
-/

open Complexity SparseDiv SparseDiv.StringArith SparseDiv.Appendix SparseGcd Complexity.SAT

namespace SparseIrred.Machine

open SparseIrred

/-! ### Literals -/

/-- The code of `P⁺ = X^m - 1`, i.e. of `[(-1, 0), (1, m)]`. -/
def posLitStr (m : List Bool) : List Bool := frame [encITerm (-1, 0), pair (encInt 1) m]

/-- The code of `P⁻ = ∑_{r<q} X^{r m}` from the unary `q` and the binary `m`. -/
def negLitStr (qU m : List Bool) : List Bool :=
  mapBlocks (fun r => pair (encInt 1) (canonBits (mulBits (unaryToBinStr r) m)))
    (TermsStr.idxBlocks qU)

/-- The raw term list of a literal block `l`, from the unary prime list `qs` and `N`. -/
def litStr (qs N l : List Bool) : List Bool :=
  caseBit₀ (pairFst l)
    (posLitStr (TermsStr.divBits₀ N (unaryToBinStr (nthBlockStr (pairSnd l) qs))))
    (negLitStr (nthBlockStr (pairSnd l) qs)
      (TermsStr.divBits₀ N (unaryToBinStr (nthBlockStr (pairSnd l) qs))))

theorem nthBlockStr_primes (qs : List ℕ) (i : ℕ) :
    nthBlockStr (unaryN i) (frame (qs.map unaryN)) = unaryN (qs.getD i 0) := by
  rw [nthBlockStr_frame, show ([] : List Bool) = unaryN 0 from rfl, List.getD_map]

theorem posLitStr_eq (m : ℕ) : posLitStr (encNat m) = encITerms (posLitTerms m) := by
  rfl

theorem negLitStr_eq (q m : ℕ) : negLitStr (unaryN q) (encNat m) = encITerms (negLitTerms q m) := by
  rw [negLitStr, TermsStr.idxBlocks_unaryN, mapBlocks_frame, encITerms, negLitTerms, List.map_map,
    List.map_map]
  refine congrArg frame (List.map_congr_left fun r _ => ?_)
  simp only [Function.comp_apply, unaryToBinStr_unaryN, encITerm, canonBits, decNat_mulBits,
    decNat_encNat]

theorem litStr_eq (qs : List ℕ) (N : ℕ) (l : Lit) :
    litStr (frame (qs.map unaryN)) (encNat N) (encLitU l) = encITerms (litTermsD qs N l) := by
  rw [litStr, encLitU, pairFst_pair, pairSnd_pair, nthBlockStr_primes, unaryToBinStr_unaryN,
    TermsStr.divBits₀_eq_encNat, decNat_encNat, decNat_encNat, litTermsD]
  cases l.sign
  · simp only [caseBit₀_cons, Bool.cond_false, Bool.false_eq_true, ite_false]
    exact negLitStr_eq _ _
  · simp only [caseBit₀_cons, Bool.cond_true, ite_true]
    exact posLitStr_eq _

theorem cobham_litStr_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v => litStr (g₀ v) (g₁ v) (g₂ v) := by
  have hq := TermsStr.cobham_nthBlockStr_comp (cobham_pairSnd_comp h₂) h₀
  have hm := TermsStr.cobham_divBits₀_comp h₁ (cobham_comp₁ cobham_unaryToBinStr hq)
  unfold litStr posLitStr negLitStr
  exact Cobham.iteFn (cobham_pairFst_comp h₂)
    (SparseGcd.cobham_frame2_comp (Cobham.const _) (cobham_pair_comp (Cobham.const _) hm))
    (TermsStr.cobham_mapBlocks_comp
      (F := fun r v => pair (encInt 1) (canonBits (mulBits (unaryToBinStr r)
        (TermsStr.divBits₀ (g₁ v) (unaryToBinStr (nthBlockStr (pairSnd (g₂ v)) (g₀ v)))))))
      (cobham_pair_comp (Cobham.const _) (cobham_canonBits_comp (cobham_mulBits_comp
        (cobham_comp₁ cobham_unaryToBinStr (.proj 0)) (TermsStr.cobham_tail_comp hm))))
      (TermsStr.cobham_idxBlocks_comp hq))

/-! ### Clauses -/

/-- One literal of the clause product; the state is `pair remainingLiterals acc`. -/
def clauseStepStr (qs N st : List Bool) : List Bool :=
  caseBit₀ (nonemptyFlag (pairFst st))
    (pair (pairSnd (pairFst st)) (mulITermsStr (litStr qs N (pairFst (pairFst st))) (pairSnd st)))
    st

/-- The raw term list of a clause of at most three literals: three steps of `clauseStepStr`. -/
def clauseStr (qs N c : List Bool) : List Bool :=
  pairSnd ((clauseStepStr qs N)^[3] (pair (TermsStr.revBlocks c) (encITerms [(1, 0)])))

theorem clauseStepStr_cons (qs : List ℕ) (N : ℕ) (l : Lit) (ls : List Lit) (acc : ITerms) :
    clauseStepStr (frame (qs.map unaryN)) (encNat N)
        (pair (frame ((l :: ls).map encLitU)) (encITerms acc)) =
      pair (frame (ls.map encLitU)) (encITerms (mulITerms (litTermsD qs N l) acc)) := by
  rw [clauseStepStr, List.map_cons, TermsStr.frame_cons_eq_pair, pairFst_pair, pairSnd_pair,
    nonemptyFlag_of_ne_nil (pair_ne_nil _ _), caseBit₀_cons, Bool.cond_true, pairFst_pair,
    pairSnd_pair, litStr_eq, mulITermsStr_eq]

theorem clauseStepStr_nil (qs N A : List Bool) : clauseStepStr qs N (pair [] A) = pair [] A := by
  rw [clauseStepStr, pairFst_pair, nonemptyFlag_nil, caseBit₀_nil]

theorem clauseStepStr_iterate (qs : List ℕ) (N : ℕ) :
    ∀ (k : ℕ) (ls : List Lit) (acc : ITerms), ls.length ≤ k →
      (clauseStepStr (frame (qs.map unaryN)) (encNat N))^[k]
          (pair (frame (ls.map encLitU)) (encITerms acc)) =
        pair [] (encITerms (ls.foldl (fun acc l => mulITerms (litTermsD qs N l) acc) acc))
  | 0, ls, acc, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]
    simp [frame_nil]
  | k + 1, [], acc, _ => by
    rw [List.map_nil, frame_nil, Function.iterate_succ_apply, clauseStepStr_nil, List.foldl_nil]
    exact Function.iterate_fixed (clauseStepStr_nil _ _ _) k
  | k + 1, l :: ls, acc, h => by
    rw [Function.iterate_succ_apply, clauseStepStr_cons,
      clauseStepStr_iterate qs N k ls _ (by simpa using h), List.foldl_cons]

theorem clauseStr_eq (qs : List ℕ) (N : ℕ) (c : Clause) (hc : c.length ≤ 3) :
    clauseStr (frame (qs.map unaryN)) (encNat N) (encClauseU c) =
      encITerms (clauseTermsD qs N c) := by
  rw [clauseStr, encClauseU, TermsStr.revBlocks_frame, ← List.map_reverse,
    clauseStepStr_iterate qs N 3 c.reverse [(1, 0)] (by simpa using hc), pairSnd_pair,
    clauseTermsD, List.foldl_reverse]

theorem cobham_clauseStr_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v => clauseStr (g₀ v) (g₁ v) (g₂ v) := by
  unfold clauseStr
  refine cobham_pairSnd_comp ?_
  refine TermsStr.cobham_iterate (f := fun s v => clauseStepStr (g₀ v) (g₁ v) s) ?_
    (cobham_pair_comp (TermsStr.cobham_revBlocks_comp h₂) (Cobham.const _)) 3
  have ht₀ := TermsStr.cobham_tail_comp h₀
  have ht₁ := TermsStr.cobham_tail_comp h₁
  have hF := cobham_pairFst_comp (Cobham.proj (n := n + 1) 0)
  unfold clauseStepStr
  exact Cobham.iteFn (Cobham.nonemptyFn hF)
    (cobham_pair_comp (cobham_pairSnd_comp hF)
      (cobham_mulITermsStr_comp (cobham_litStr_comp ht₀ ht₁ (cobham_pairFst_comp hF))
        (cobham_pairSnd_comp (.proj 0))))
    (.proj 0)

end SparseIrred.Machine
