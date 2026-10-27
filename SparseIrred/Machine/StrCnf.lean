import SparseIrred.Machine.StrArith

/-!
# CNF-level string functions: validity of exact-3 codes, occurrence, renumbering

Input side: complexitylib's `CNF.encode` is parsed by `SparseGcd.parseCnfStr` into the internal
encoding `encCNFU Φ` (literals `pair [sign] (unaryN var)`, variables in unary — so every variable
index is at most the input length and unary loops over variables are polynomial).

* `is3Str`: the exact-3 check; `validStr x = [(decode3? x).isSome]` (`validStr_eq`);
* `occursStr u t`: does the unary variable `u` occur in `t`;
* `rankStr v t = unaryN (varIdx Φ v)`, the number of occurring variables `< v`;
* `numVarsU t = unaryN (numVars Φ)`;
* `renumStr t = encCNFU (renumber Φ)` (`renumStr_eq`).
-/

open Complexity SparseDiv SparseDiv.StringArith SparseDiv.Appendix SparseGcd Complexity.SAT

namespace SparseIrred.Machine

open SparseIrred

/-! ### Parsing and the exact-3 check -/

theorem pairSnd_parseCnfStr {x : List Bool} {Φ : CNF} (h : CNF.decode? x = some Φ) :
    pairSnd (parseCnfStr x) = encCNFU Φ := by
  rw [parseCnfStr_eq, h, pairSnd_pair]

/-- `[true]` iff every clause has exactly three literals. -/
def is3Str (t : List Bool) : List Bool :=
  foldBlocks (fun acc c => andBit acc (Cobham.eqFlag (TermsStr.countBlocks c) [true, true, true]))
    [true] t

theorem is3Str_encCNFU (Φ : CNF) : is3Str (encCNFU Φ) = [decide Φ.Is3CNF] := by
  have key : ∀ (Φ : CNF) (b : Bool),
      (Φ.map encClauseU).foldl
          (fun acc c => andBit acc (Cobham.eqFlag (TermsStr.countBlocks c) [true, true, true]))
          [b] =
        [b && decide Φ.Is3CNF] := by
    intro Φ
    induction Φ with
    | nil => intro b; simp
    | cons c Φ ih =>
      intro b
      have h1 : Cobham.eqFlag (TermsStr.countBlocks (encClauseU c)) [true, true, true] =
          [decide (c.length = 3)] := by
        rw [encClauseU, TermsStr.countBlocks_frame, List.length_map,
          show [true, true, true] = unaryN 3 from rfl, eqFlag_unaryN]
      rw [List.map_cons, List.foldl_cons, h1, andBit_single, ih]
      simp only [CNF.is3CNF_cons, Bool.and_assoc, Bool.decide_and]
  rw [is3Str, encCNFU, foldBlocks_frame, key Φ true, Bool.true_and]

theorem cobham_is3Str_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => is3Str (g v) := by
  have hstep : Cobham fun w : Fin 2 → List Bool =>
      andBit (w 0) (Cobham.eqFlag (TermsStr.countBlocks (w 1)) [true, true, true]) :=
    Cobham.andFn (.proj 0) (Cobham.eqFlag_mem (TermsStr.cobham_countBlocks_comp (.proj 1))
      (Cobham.const _))
  have h : Cobham fun v : Fin 1 → List Bool => is3Str (v 0) :=
    (cobham_foldBlocks (n := 0) hstep (init := fun _ => [true]) (Cobham.const _) 1 fun w => by
      rw [length_andBit]
      omega).of_eq fun v => rfl
  exact (Cobham.comp h fun _ : Fin 1 => hg).of_eq fun v => rfl

/-- `[true]` iff `x` is the code of an exact-3 CNF (the parser's success flag is the head bit of
`parseCnfStr x`). -/
def validStr (x : List Bool) : List Bool :=
  caseBit₀ (parseCnfStr x) (is3Str (pairSnd (parseCnfStr x))) [false]

theorem validStr_eq (x : List Bool) : validStr x = [(CNF.decode3? x).isSome] := by
  rw [validStr, parseCnfStr_eq]
  unfold CNF.decode3?
  rcases h : CNF.decode? x with _ | Φ
  · simp
  · simp only [pairSnd_pair, is3Str_encCNFU]
    by_cases h3 : Φ.Is3CNF <;> simp [h3, pair, delimit]

theorem cobham_validStr : Cobham fun v : Fin 1 → List Bool => validStr (v 0) := by
  have hp : Cobham fun v : Fin 1 → List Bool => parseCnfStr (v 0) :=
    FP_subset_CobhamFP parseCnfStr_mem_FP
  unfold validStr
  exact Cobham.iteFn hp (cobham_is3Str_comp (cobham_pairSnd_comp hp)) (Cobham.const _)

/-! ### Occurrence and rank -/

/-- `[true]` iff some literal of the clause block `c` has the unary variable `u`. -/
def clauseHasStr (u c : List Bool) : List Bool :=
  foldBlocks (fun acc l => orBit acc (Cobham.eqFlag (pairSnd l) u)) [false] c

/-- `[true]` iff the unary variable `u` occurs in the formula `t`. -/
def occursStr (u t : List Bool) : List Bool :=
  foldBlocks (fun acc c => orBit acc (clauseHasStr u c)) [false] t

theorem clauseHasStr_encClauseU (v : ℕ) (c : Clause) :
    clauseHasStr (unaryN v) (encClauseU c) = [decide (∃ l ∈ c, l.var = v)] := by
  have key : ∀ (c : Clause) (b : Bool),
      (c.map encLitU).foldl (fun acc l => orBit acc (Cobham.eqFlag (pairSnd l) (unaryN v))) [b] =
        [b || decide (∃ l ∈ c, l.var = v)] := by
    intro c
    induction c with
    | nil => intro b; simp
    | cons l c ih =>
      intro b
      rw [List.map_cons, List.foldl_cons, encLitU, pairSnd_pair, eqFlag_unaryN, orBit_single, ih]
      simp only [List.mem_cons, exists_eq_or_imp, Bool.decide_or, Bool.or_assoc]
  rw [clauseHasStr, encClauseU, foldBlocks_frame, key c false, Bool.false_or]

theorem occursStr_eq (v : ℕ) (Φ : CNF) :
    occursStr (unaryN v) (encCNFU Φ) = [decide (Occurs Φ v)] := by
  have key : ∀ (Ψ : CNF) (b : Bool),
      (Ψ.map encClauseU).foldl (fun acc c => orBit acc (clauseHasStr (unaryN v) c)) [b] =
        [b || decide (Occurs Ψ v)] := by
    intro Ψ
    induction Ψ with
    | nil => intro b; simp [Occurs]
    | cons c Ψ ih =>
      intro b
      rw [List.map_cons, List.foldl_cons, clauseHasStr_encClauseU, orBit_single, ih]
      simp only [Occurs, List.mem_cons, exists_eq_or_imp, Bool.decide_or, Bool.or_assoc]
  rw [occursStr, encCNFU, foldBlocks_frame, key Φ false, Bool.false_or]

theorem cobham_clauseHasStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => clauseHasStr (g₀ v) (g₁ v) := by
  have hstep : Cobham fun w : Fin 3 → List Bool =>
      orBit (w 0) (Cobham.eqFlag (pairSnd (w 1)) (w 2)) :=
    Cobham.orFn (.proj 0) (Cobham.eqFlag_mem (cobham_pairSnd_comp (.proj 1)) (.proj 2))
  have h : Cobham fun v : Fin 2 → List Bool => clauseHasStr (v 1) (v 0) :=
    (cobham_foldBlocks (n := 1) hstep (init := fun _ => [false]) (Cobham.const _) 1 fun w => by
      rw [length_orBit]
      omega).of_eq fun v => rfl
  exact (Cobham.comp₂ h h₁ h₀).of_eq fun v => by simp

theorem cobham_occursStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => occursStr (g₀ v) (g₁ v) := by
  have hstep : Cobham fun w : Fin 3 → List Bool => orBit (w 0) (clauseHasStr (w 2) (w 1)) :=
    Cobham.orFn (.proj 0) (cobham_clauseHasStr_comp (.proj 2) (.proj 1))
  have h : Cobham fun v : Fin 2 → List Bool => occursStr (v 1) (v 0) :=
    (cobham_foldBlocks (n := 1) hstep (init := fun _ => [false]) (Cobham.const _) 1 fun w => by
      rw [length_orBit]
      omega).of_eq fun v => rfl
  exact (Cobham.comp₂ h h₁ h₀).of_eq fun v => by simp

/-- `unaryN (varIdx Φ v)`: count the occurring `u < v` (a unary counter, growth `≤ 1` per
block). -/
def rankStr (v t : List Bool) : List Bool :=
  foldBlocks (fun acc u => caseBit₀ (occursStr u t) (true :: acc) acc) [] (TermsStr.idxBlocks v)

theorem rankStr_eq (v : ℕ) (Φ : CNF) : rankStr (unaryN v) (encCNFU Φ) = unaryN (varIdx Φ v) := by
  have key : ∀ (us : List ℕ) (a : ℕ),
      (us.map unaryN).foldl (fun acc u => caseBit₀ (occursStr u (encCNFU Φ)) (true :: acc) acc)
          (unaryN a) = unaryN (a + (us.filter fun u => decide (Occurs Φ u)).length) := by
    intro us
    induction us with
    | nil => intro a; simp
    | cons u us ih =>
      intro a
      rw [List.map_cons, List.foldl_cons, occursStr_eq]
      by_cases h : Occurs Φ u
      · simp only [h, decide_true, caseBit₀_cons, Bool.cond_true]
        rw [← unaryN_succ, ih, List.filter_cons_of_pos (by simpa using h), List.length_cons]
        congr 1
        omega
      · simp only [h, decide_false, caseBit₀_cons, Bool.cond_false]
        rw [ih, List.filter_cons_of_neg (by simpa using h)]
  rw [rankStr, TermsStr.idxBlocks_unaryN, foldBlocks_frame,
    show ([] : List Bool) = unaryN 0 from rfl, key, zero_add, varIdx]

theorem cobham_rankStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => rankStr (g₀ v) (g₁ v) := by
  have hstep : Cobham fun w : Fin 3 → List Bool =>
      caseBit₀ (occursStr (w 1) (w 2)) (true :: w 0) (w 0) :=
    Cobham.iteFn (cobham_occursStr_comp (.proj 1) (.proj 2)) (cobham_cons true (.proj 0)) (.proj 0)
  have h : Cobham fun v : Fin 2 → List Bool =>
      foldBlocks (fun acc u => caseBit₀ (occursStr u (v 1)) (true :: acc) acc) [] (v 0) :=
    (cobham_foldBlocks (n := 1) hstep (init := fun _ => []) Cobham.empty 1 fun w => by
      rcases SparseGcd.caseBit₀_cases (occursStr (w 1) (w 2)) (true :: w 0) (w 0) with h | h <;>
      · rw [h]
        try simp only [List.length_cons]
        omega).of_eq fun v => rfl
  exact (Cobham.comp₂ h (TermsStr.cobham_idxBlocks_comp h₀) h₁).of_eq fun v => by
    simp [rankStr]

/-- `unaryN (numVars Φ)`: the rank of `maxVar + 1`. -/
def numVarsU (t : List Bool) : List Bool := rankStr (numVarsStr t) t

theorem numVarsU_eq (Φ : CNF) : numVarsU (encCNFU Φ) = unaryN (numVars Φ) := by
  rw [numVarsU, numVarsStr_encCNFU, rankStr_eq]
  rfl

theorem cobham_numVarsU_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => numVarsU (g v) := by
  unfold numVarsU
  exact cobham_rankStr_comp (cobham_comp₁ (FP_subset_CobhamFP numVarsStr_mem_FP) hg) hg

/-! ### Renumbering -/

/-- Replace every literal's unary variable by its rank. -/
def renumStr (t : List Bool) : List Bool :=
  mapBlocks (fun c => mapBlocks (fun l => pair (pairFst l) (rankStr (pairSnd l) t)) c) t

theorem renumStr_eq (Φ : CNF) : renumStr (encCNFU Φ) = encCNFU (renumber Φ) := by
  have key : ∀ (t : List Bool) (Ψ : CNF),
      mapBlocks (fun c => mapBlocks (fun l => pair (pairFst l) (rankStr (pairSnd l) t)) c)
        (encCNFU Ψ) =
        frame (Ψ.map fun c => frame (c.map fun l => pair [l.sign] (rankStr (unaryN l.var) t))) := by
    intro t Ψ
    rw [encCNFU, mapBlocks_frame, List.map_map]
    refine congrArg frame (List.map_congr_left fun c _ => ?_)
    simp only [Function.comp_apply, encClauseU, mapBlocks_frame, List.map_map]
    refine congrArg frame (List.map_congr_left fun l _ => ?_)
    simp only [Function.comp_apply, encLitU, pairFst_pair, pairSnd_pair]
  rw [renumStr, key, show encCNFU (renumber Φ) = frame ((renumber Φ).map encClauseU) from rfl,
    renumber, List.map_map]
  refine congrArg frame (List.map_congr_left fun c _ => ?_)
  simp only [Function.comp_apply, encClauseU, List.map_map]
  refine congrArg frame (List.map_congr_left fun l _ => ?_)
  simp only [Function.comp_apply, encLitU, rankStr_eq, renumLit]

theorem cobham_renumStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => renumStr (g v) := by
  unfold renumStr
  refine TermsStr.cobham_mapBlocks_comp
    (F := fun c v => mapBlocks (fun l => pair (pairFst l) (rankStr (pairSnd l) (g v))) c) ?_ hg
  refine TermsStr.cobham_mapBlocks_comp
    (F := fun l u => pair (pairFst l) (rankStr (pairSnd l) (g (Fin.tail u)))) ?_ (.proj 0)
  exact cobham_pair_comp (cobham_pairFst_comp (.proj 0))
    (cobham_rankStr_comp (cobham_pairSnd_comp (.proj 0))
      (TermsStr.cobham_tail_comp (TermsStr.cobham_tail_comp hg)))

end SparseIrred.Machine
