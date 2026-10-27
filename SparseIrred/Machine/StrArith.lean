import SparseIrred.Machine.Data
import SparseGcd.Machine.TermsStr
import Complexitylib.Classes.P

/-!
# String-level signed arithmetic and term-list operations

String implementations of the arithmetic steps of `Machine/Data.lean`.  Numbers are binary
numerals (`encNat`), signed integers are `pair [sign] magnitude` (`encInt`), and term lists are
framed lists of `pair coefficient exponent` blocks (`encITerms`).

Every function here maps canonical codes to canonical codes: each emitted numeral goes through
`canonBits` (or is copied from a canonical input), and each emitted sign is `[decide (z < 0)]`.
Hence the correctness lemmas are literal equalities with `encNat`/`encInt`/`encITerms` of the
data-level results, as in `SparseGcd/Machine/TermsStr.lean`.  Each function has a Cobham lemma in
`_comp` form (`Cobham g₀ → … → Cobham fun v ↦ F (g₀ v) …`).

## Contents

* `mulIntStr`, `prodBlockZ`, `mulITermsStr`: signed product, product of two terms, and the raw
  product of two term lists (all pairwise products, no merging);
* `reflectStr`: exponent reflection `e ↦ K - e`;
* `degreeStr_encITerms`: the degree computation `degreeStr` on canonical codes;
* `canonITermsStr`: canonical output after `normalizeZStr` (sorting, merging, dropping zeros);
* `headExpStr`, `aTermsStr`: the head exponent and the terms of `A = 3 X^D S`;
* `sqSumStr`, `wStr`, `mStr`, `pow6Str`: `∑ c²`, `w`, `m = max(N, deg A)` and sixth powers;
* `binToUnaryStr`: binary to unary conversion, clamped by a unary ruler;
* `shiftStr`, `MStr`: `2^k · y` and `M = 2^{20(w+1)} (m+1)^6` in binary;
* `outStr`: the output list `A ++ [(-1, M), (1, M + N)]`.
-/

open Complexity SparseDiv SparseDiv.StringArith SparseDiv.Appendix SparseGcd

namespace SparseIrred.Machine

/-! ### Flags and signed-integer accessors on canonical codes -/

theorem eqFlag_eq_decide' (a b : List Bool) : Cobham.eqFlag a b = [decide (a = b)] := by
  rcases Cobham.eqFlag_flag a b with h | h
  · rw [h, (Cobham.eqFlag_eq_true_iff a b).1 h]
    simp
  · have hab : a ≠ b := fun hab => by
      rw [(Cobham.eqFlag_eq_true_iff a b).2 hab] at h
      simp at h
    rw [h]
    simp [hab]

theorem unaryN_eq_unaryN_iff (a b : ℕ) : unaryN a = unaryN b ↔ a = b :=
  ⟨fun h => by simpa using congrArg List.length h, fun h => by rw [h]⟩

theorem length_andBit (x y : List Bool) : (andBit x y).length = 1 := by
  unfold andBit
  rcases SparseGcd.caseBit₀_cases x (caseBit₀ y [true] [false]) [false] with h | h <;> rw [h]
  · rcases SparseGcd.caseBit₀_cases y [true] [false] with h' | h' <;> rw [h'] <;> rfl
  · rfl

theorem length_orBit (x y : List Bool) : (orBit x y).length = 1 := by
  unfold orBit
  rcases SparseGcd.caseBit₀_cases x [true] (caseBit₀ y [true] [false]) with h | h <;> rw [h]
  · rfl
  · rcases SparseGcd.caseBit₀_cases y [true] [false] with h' | h' <;> rw [h'] <;> rfl

theorem eqFlag_unaryN (a b : ℕ) : Cobham.eqFlag (unaryN a) (unaryN b) = [decide (a = b)] := by
  rw [eqFlag_eq_decide']
  simp only [unaryN_eq_unaryN_iff]

theorem lenLeFlag_eq_decide (a b : List Bool) :
    Cobham.lenLeFlag a b = [decide (b.length ≤ a.length)] := by
  unfold Cobham.lenLeFlag
  by_cases h : b.length ≤ a.length
  · rw [List.drop_eq_nil_of_le h, nonemptyFlag_nil]
    simp [h]
    rfl
  · rw [nonemptyFlag_of_ne_nil (by simp; omega)]
    simp [h]

theorem negFlag_encInt (z : ℤ) : negFlag (encInt z) = [decide (z < 0)] := by
  rw [negFlag, encInt, pairFst_pair, eqFlag_eq_decide']
  cases decide (z < 0) <;> rfl

theorem magOf_encInt (z : ℤ) : magOf (encInt z) = encNat z.natAbs := by
  rw [magOf, encInt, pairSnd_pair]

theorem isZeroBits_encNat (k : ℕ) : isZeroBits (encNat k) = [decide (k = 0)] := by
  rcases isZeroBits_flag (encNat k) with h | h
  · rw [h, (isZeroBits_eq_true_iff _).1 h |>.symm.trans (decNat_encNat k) |>.symm]
    simp
  · have hk : k ≠ 0 := fun hk => by
      rw [(isZeroBits_eq_true_iff _).2 (by rw [decNat_encNat, hk])] at h
      simp at h
    rw [h]
    simp [hk]

theorem ltBits_encNat (a b : ℕ) : ltBits (encNat a) (encNat b) = [decide (a < b)] := by
  rcases ltBits_flag (encNat a) (encNat b) with h | h
  · have hab := (ltBits_eq_true_iff _ _).1 h
    rw [decNat_encNat, decNat_encNat] at hab
    rw [h]
    simp [hab]
  · have hab := (ltBits_eq_false_iff _ _).1 h
    rw [decNat_encNat, decNat_encNat] at hab
    rw [h]
    simp [Nat.not_lt.2 hab]

/-! ### Framed lists of term lists -/

theorem encITerms_append (l₁ l₂ : ITerms) :
    encITerms (l₁ ++ l₂) = encITerms l₁ ++ encITerms l₂ := by
  simp [encITerms, frame_append]

theorem flattenBlocks_frame_encITerms (Ls : List ITerms) :
    TermsStr.flattenBlocks (frame (Ls.map encITerms)) = encITerms Ls.flatten := by
  rw [TermsStr.flattenBlocks_frame]
  induction Ls with
  | nil => rfl
  | cons L Ls ih => rw [List.map_cons, List.flatten_cons, ih, List.flatten_cons, encITerms_append]

/-! ### Signed products -/

/-- Canonical signed product (the sign of a zero product is `false`). -/
def mulIntStr (x y : List Bool) : List Bool :=
  pair (caseBit₀ (isZeroBits (canonBits (mulBits (magOf x) (magOf y)))) [false]
      (xorFlag (negFlag x) (negFlag y)))
    (canonBits (mulBits (magOf x) (magOf y)))

theorem mulIntStr_encInt (a b : ℤ) : mulIntStr (encInt a) (encInt b) = encInt (a * b) := by
  have hmag : canonBits (mulBits (magOf (encInt a)) (magOf (encInt b))) =
      encNat (a * b).natAbs := by
    rw [magOf_encInt, magOf_encInt, canonBits, decNat_mulBits, decNat_encNat, decNat_encNat,
      Int.natAbs_mul]
  rw [mulIntStr, hmag, negFlag_encInt, negFlag_encInt, xorFlag_single, isZeroBits_encNat, encInt]
  congr 1
  by_cases hab : a * b = 0
  · simp [hab]
  · have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    have hab' : (a * b).natAbs ≠ 0 := by simpa using hab
    simp only [hab', decide_false, caseBit₀_cons, Bool.cond_false, List.cons.injEq, and_true]
    rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
    · have : 0 < a * b := mul_pos_of_neg_of_neg ha' hb'
      simp [ha', hb', not_lt.2 this.le]
    · have : a * b < 0 := mul_neg_of_neg_of_pos ha' hb'
      simp [ha', not_lt.2 hb'.le, this]
    · have : a * b < 0 := mul_neg_of_pos_of_neg ha' hb'
      simp [not_lt.2 ha'.le, hb', this]
    · have : 0 < a * b := mul_pos ha' hb'
      simp [not_lt.2 ha'.le, not_lt.2 hb'.le, not_lt.2 this.le]

theorem cobham_mulIntStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => mulIntStr (g₀ v) (g₁ v) := by
  unfold mulIntStr
  have hm := cobham_canonBits_comp
    (cobham_mulBits_comp (cobham_magOf_comp h₀) (cobham_magOf_comp h₁))
  exact cobham_pair_comp
    (Cobham.iteFn (cobham_isZeroBits_comp hm) (Cobham.const [false])
      (cobham_xorFlag_comp (cobham_negFlag_comp h₀) (cobham_negFlag_comp h₁))) hm

/-- Product of two term blocks. -/
def prodBlockZ (b₁ b₂ : List Bool) : List Bool :=
  pair (mulIntStr (pairFst b₁) (pairFst b₂)) (canonBits (addBits (pairSnd b₁) (pairSnd b₂)))

theorem prodBlockZ_encITerm (s t : ℤ × ℕ) :
    prodBlockZ (encITerm s) (encITerm t) = encITerm (s.1 * t.1, s.2 + t.2) := by
  simp only [prodBlockZ, encITerm, pairFst_pair, pairSnd_pair, mulIntStr_encInt]
  rw [canonBits, decNat_addBits, decNat_encNat, decNat_encNat]

theorem cobham_prodBlockZ_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => prodBlockZ (g₀ v) (g₁ v) := by
  unfold prodBlockZ
  exact cobham_pair_comp (cobham_mulIntStr_comp (cobham_pairFst_comp h₀) (cobham_pairFst_comp h₁))
    (cobham_canonBits_comp (cobham_addBits_comp (cobham_pairSnd_comp h₀) (cobham_pairSnd_comp h₁)))

/-- The raw product of two term lists: all pairwise products, no merging (the signed analogue of
`TermsStr.mulTermsStr`); it computes `encITerms (mulITerms l₁ l₂)`. -/
def mulITermsStr (l₁ l₂ : List Bool) : List Bool :=
  TermsStr.flattenBlocks (mapBlocks (fun b₁ => mapBlocks (prodBlockZ b₁) l₂) l₁)

theorem mulITermsStr_eq (l₁ l₂ : ITerms) :
    mulITermsStr (encITerms l₁) (encITerms l₂) = encITerms (mulITerms l₁ l₂) := by
  have hrow : ∀ s : ℤ × ℕ, mapBlocks (prodBlockZ (encITerm s)) (encITerms l₂) =
      encITerms (l₂.map fun t => (s.1 * t.1, s.2 + t.2)) := by
    intro s
    rw [encITerms, mapBlocks_frame, encITerms, List.map_map, List.map_map]
    exact congrArg frame (List.map_congr_left fun t _ => prodBlockZ_encITerm s t)
  have hmap : (l₁.map encITerm).map (fun b₁ => mapBlocks (prodBlockZ b₁) (encITerms l₂)) =
      (l₁.map fun s => l₂.map fun t => (s.1 * t.1, s.2 + t.2)).map encITerms := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun s _ => hrow s
  rw [mulITermsStr, show encITerms l₁ = frame (l₁.map encITerm) from rfl, mapBlocks_frame, hmap,
    flattenBlocks_frame_encITerms, mulITerms, List.flatMap_def]

theorem cobham_mulITermsStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => mulITermsStr (g₀ v) (g₁ v) := by
  unfold mulITermsStr
  refine TermsStr.cobham_flattenBlocks_comp ?_
  refine TermsStr.cobham_mapBlocks_comp (F := fun b v => mapBlocks (prodBlockZ b) (g₁ v)) ?_ h₀
  refine TermsStr.cobham_mapBlocks_comp (F := fun b' u => prodBlockZ (u 0) b') ?_
    (TermsStr.cobham_tail_comp h₁)
  exact cobham_prodBlockZ_comp (.proj 1) (.proj 0)

/-! ### Reflection `e ↦ K - e` -/

/-- Exponent reflection `e ↦ K - e` (truncated) on a term list. -/
def reflectStr (K l : List Bool) : List Bool :=
  mapBlocks (fun b => pair (pairFst b) (canonBits (subBits K (pairSnd b)))) l

theorem reflectStr_eq (K : ℕ) (l : ITerms) :
    reflectStr (encNat K) (encITerms l) = encITerms (reflectITerms K l) := by
  rw [reflectStr, encITerms, mapBlocks_frame, encITerms, reflectITerms, List.map_map, List.map_map]
  refine congrArg frame (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, encITerm, pairFst_pair, pairSnd_pair]
  rw [canonBits, decNat_subBits, decNat_encNat, decNat_encNat]

theorem cobham_reflectStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => reflectStr (g₀ v) (g₁ v) := by
  unfold reflectStr
  exact TermsStr.cobham_mapBlocks_comp
    (F := fun b v => pair (pairFst b) (canonBits (subBits (g₀ v) (pairSnd b))))
    (cobham_pair_comp (cobham_pairFst_comp (.proj 0))
      (cobham_canonBits_comp (cobham_subBits_comp (TermsStr.cobham_tail_comp h₀)
        (cobham_pairSnd_comp (.proj 0))))) h₁

/-! ### Degree (literal form of `decNat_degreeStr`) -/

theorem degreeStr_encITerms (l : ITerms) : degreeStr (encITerms l) = encNat (degreeZ l) := by
  have key : ∀ (l : ITerms) (m : ℕ),
      (l.map encITerm).foldl (fun acc b => caseBit₀ (ltBits acc (expZ b)) (expZ b) acc)
        (encNat m) = encNat (max m (degreeZ l)) := by
    intro l
    induction l with
    | nil => intro m; simp [degreeZ]
    | cons t l ih =>
      intro m
      rw [List.map_cons, List.foldl_cons]
      have h1 : caseBit₀ (ltBits (encNat m) (expZ (encITerm t))) (expZ (encITerm t)) (encNat m) =
          encNat (max m t.2) := by
        rw [expZ, encITerm, pairSnd_pair, ltBits_encNat]
        by_cases h : m < t.2
        · simp [h, max_eq_right h.le]
        · simp [h, max_eq_left (Nat.not_lt.1 h)]
      rw [h1, ih]
      simp only [degreeZ, List.map_cons, List.foldr_cons]
      rw [max_assoc]
  rw [degreeStr, encITerms, foldBlocks_frame, show ([] : List Bool) = encNat 0 from rfl, key l 0,
    Nat.zero_max]

theorem cobham_degreeStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => degreeStr (g v) :=
  cobham_comp₁ (FP_subset_CobhamFP degreeStr_mem_FP) hg

/-! ### Canonical output of `normalizeZStr` -/

/-- Canonicalise a signed integer string (sign flag, canonical magnitude). -/
def canonIntStr (x : List Bool) : List Bool := pair (negFlag x) (canonBits (magOf x))

/-- Canonicalise every term block. -/
def canonITermsStr (s : List Bool) : List Bool :=
  mapBlocks (fun b => pair (canonIntStr (pairFst b)) (canonBits (pairSnd b))) s

theorem canonIntStr_of_ne_zero {x : List Bool} (hx : decInt x ≠ 0) :
    canonIntStr x = encInt (decInt x) := by
  rw [canonIntStr, encInt, negFlag, magOf, eqFlag_eq_decide', canonBits]
  unfold decInt at hx ⊢
  by_cases h : pairFst x = [true]
  · simp only [h, ite_true] at hx ⊢
    have hpos : decNat (pairSnd x) ≠ 0 := by
      intro h0
      apply hx
      simp [h0]
    congr 2
    · simp only [decide_true, true_eq_decide_iff]
      omega
    · simp
  · simp only [h, ite_false] at hx ⊢
    congr 2

theorem canonITermsStr_of_decITerms {s : List Bool} {l : ITerms} (h : decITerms s = some l)
    (hl : ∀ t ∈ l, t.1 ≠ 0) : canonITermsStr s = encITerms l := by
  unfold decITerms at h
  rcases hb : undelimitBlocks s with _ | bs
  · rw [hb] at h
    simp at h
  · rw [hb, Option.bind_some] at h
    rw [eq_frame_of_undelimitBlocks_eq_some hb, canonITermsStr, mapBlocks_frame, encITerms]
    congr 1
    clear hb
    induction bs generalizing l with
    | nil =>
      simp only [decITermList, Option.some.injEq] at h
      subst h
      rfl
    | cons b bs ih =>
      simp only [decITermList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t, ht, ts, hts, rfl⟩ := h
      rw [decITerm, Option.map_eq_some_iff] at ht
      obtain ⟨ab, hab, rfl⟩ := ht
      have hb : b = pair ab.1 ab.2 := unpair?_eq_some_iff.1 hab
      rw [List.map_cons, List.map_cons, ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)) hts, hb,
        pairFst_pair, pairSnd_pair, canonIntStr_of_ne_zero (hl _ List.mem_cons_self), encITerm]
      rfl

/-- Sorting + merging + dropping zeros, with a literally canonical output. -/
theorem canonITermsStr_normalizeZStr (l : ITerms) :
    canonITermsStr (normalizeZStr (encITerms l)) = encITerms (normalizeZ l) :=
  canonITermsStr_of_decITerms (decITerms_normalizeZStr l) (normalizedZ_normalizeZ l).2

theorem cobham_canonITermsStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v => canonITermsStr (g v) := by
  unfold canonITermsStr canonIntStr
  exact TermsStr.cobham_mapBlocks_comp
    (F := fun b _ => pair (pair (negFlag (pairFst b)) (canonBits (magOf (pairFst b))))
      (canonBits (pairSnd b)))
    (cobham_pair_comp
      (cobham_pair_comp (cobham_negFlag_comp (cobham_pairFst_comp (.proj 0)))
        (cobham_canonBits_comp (cobham_magOf_comp (cobham_pairFst_comp (.proj 0)))))
      (cobham_canonBits_comp (cobham_pairSnd_comp (.proj 0)))) hg

theorem cobham_normalizeZStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v => normalizeZStr (g v) :=
  cobham_comp₁ (FP_subset_CobhamFP normalizeZStr_mem_FP) hg

/-! ### `A = 3 X^D S` from the canonical list of `X^K S` -/

/-- Exponent of the first term block (`[]` = `encNat 0` for the empty list). -/
def headExpStr (s : List Bool) : List Bool := pairSnd (pairFst s)

theorem headExpStr_encITerms (l : ITerms) : headExpStr (encITerms l) = encNat (headExpD l) := by
  cases l with
  | nil => rfl
  | cons t l =>
    rw [headExpStr, encITerms, List.map_cons, TermsStr.frame_cons_eq_pair, pairFst_pair, encITerm,
      pairSnd_pair, headExpD_cons]

/-- Multiply a signed integer string by `3`. -/
def scale3Str (x : List Bool) : List Bool :=
  pair (negFlag x) (canonBits (mulBits [true, true] (magOf x)))

theorem scale3Str_encInt (c : ℤ) : scale3Str (encInt c) = encInt (3 * c) := by
  rw [scale3Str, negFlag_encInt, magOf_encInt, encInt, canonBits, decNat_mulBits, decNat_encNat]
  have h3 : decNat [true, true] = 3 := rfl
  rw [h3, Int.natAbs_mul]
  congr 2
  simp only [decide_eq_decide]
  omega

/-- The terms of `A = 3 X^D S` from the canonical list of `X^K S`: multiply every coefficient by
`3` and subtract the head exponent from every exponent. -/
def aTermsStr (s : List Bool) : List Bool :=
  mapBlocks (fun b => pair (scale3Str (pairFst b)) (canonBits (subBits (pairSnd b) (headExpStr s))))
    s

theorem aTermsStr_eq (l : ITerms) : aTermsStr (encITerms l) = encITerms (aTermsD l) := by
  rw [aTermsStr, headExpStr_encITerms, encITerms, mapBlocks_frame, encITerms, aTermsD, List.map_map,
    List.map_map]
  refine congrArg frame (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, encITerm, pairFst_pair, pairSnd_pair, scale3Str_encInt]
  rw [canonBits, decNat_subBits, decNat_encNat, decNat_encNat]

theorem cobham_aTermsStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => aTermsStr (g v) := by
  unfold aTermsStr scale3Str headExpStr
  exact TermsStr.cobham_mapBlocks_comp
    (F := fun b v => pair (pair (negFlag (pairFst b))
        (canonBits (mulBits [true, true] (magOf (pairFst b)))))
      (canonBits (subBits (pairSnd b) (pairSnd (pairFst (g v))))))
    (cobham_pair_comp
      (cobham_pair_comp (cobham_negFlag_comp (cobham_pairFst_comp (.proj 0)))
        (cobham_canonBits_comp (cobham_mulBits_comp (Cobham.const _)
          (cobham_magOf_comp (cobham_pairFst_comp (.proj 0))))))
      (cobham_canonBits_comp (cobham_subBits_comp (cobham_pairSnd_comp (.proj 0))
        (cobham_pairSnd_comp (cobham_pairFst_comp (TermsStr.cobham_tail_comp hg)))))) hg

/-! ### `w = 4 + ∑ c² + #A` in binary -/

/-- One step of `sqSumStr`: add the square of the coefficient of the term block `b`. -/
def sqStep (acc b : List Bool) : List Bool :=
  canonBits (addBits acc (canonBits (mulBits (magOf (pairFst b)) (magOf (pairFst b)))))

/-- `∑ c²` over a term list, in binary. -/
def sqSumStr (s : List Bool) : List Bool := foldBlocks sqStep [] s

theorem sqSumStr_eq (l : ITerms) : sqSumStr (encITerms l) = encNat (sqSumD l) := by
  have key : ∀ (l : ITerms) (m : ℕ), (l.map encITerm).foldl sqStep (encNat m) =
      encNat (m + sqSumD l) := by
    intro l
    induction l with
    | nil => intro m; simp [sqSumD]
    | cons t l ih =>
      intro m
      rw [List.map_cons, List.foldl_cons]
      have h1 : sqStep (encNat m) (encITerm t) = encNat (m + t.1.natAbs ^ 2) := by
        rw [sqStep, encITerm, pairFst_pair, magOf_encInt]
        simp only [canonBits, decNat_addBits, decNat_mulBits, decNat_encNat]
        ring_nf
      rw [h1, ih]
      simp only [sqSumD, List.map_cons, List.sum_cons]
      ring_nf
  rw [sqSumStr, encITerms, foldBlocks_frame, show ([] : List Bool) = encNat 0 from rfl, key,
    zero_add]

/-- Additive growth (the `cobham_foldBlocks` side condition, with `c = 2`). -/
theorem length_sqStep_le (acc b : List Bool) :
    (sqStep acc b).length ≤ acc.length + 2 * (b.length + 1) := by
  set m := magOf (pairFst b)
  have hm : m.length ≤ b.length := (length_pairSnd_le _).trans (length_pairFst_le _)
  have h1 := decNat_lt_two_pow_length acc
  have h2 := decNat_lt_two_pow_length m
  have h3 : decNat m * decNat m < 2 ^ (2 * m.length) := by
    rw [two_mul, pow_add]
    exact Nat.mul_lt_mul'' h2 h2
  have h4 : 2 ^ acc.length ≤ 2 ^ (acc.length + 2 * m.length) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ^ (2 * m.length) ≤ 2 ^ (acc.length + 2 * m.length) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h6 : decNat (addBits acc (canonBits (mulBits m m))) <
      2 ^ (acc.length + 2 * m.length + 1) := by
    rw [decNat_addBits, decNat_canonBits, decNat_mulBits, pow_succ]
    omega
  rw [sqStep, canonBits]
  exact (length_encNat_le_of_lt h6).trans (by omega)

theorem cobham_sqSumStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => sqSumStr (g v) := by
  have hstep : Cobham fun w : Fin 2 → List Bool => sqStep (w 0) (w 1) := by
    unfold sqStep
    exact cobham_canonBits_comp (cobham_addBits_comp (.proj 0)
      (cobham_canonBits_comp
        (cobham_mulBits_comp (cobham_magOf_comp (cobham_pairFst_comp (.proj 1)))
          (cobham_magOf_comp (cobham_pairFst_comp (.proj 1))))))
  have h : Cobham fun v : Fin 1 → List Bool => foldBlocks sqStep [] (v 0) :=
    (cobham_foldBlocks (n := 0) hstep (init := fun _ => []) Cobham.empty 2
      fun w => length_sqStep_le (w 0) (w 1)).of_eq fun v => rfl
  exact (Cobham.comp h fun _ : Fin 1 => hg).of_eq fun v => rfl

/-- `w = 4 + ∑ c² + #A`, in binary. -/
def wStr (A : List Bool) : List Bool :=
  canonBits (addBits (addBits (sqSumStr A) (unaryToBinStr (TermsStr.countBlocks A))) (encNat 4))

theorem wStr_eq (A : ITerms) : wStr (encITerms A) = encNat (wD A) := by
  rw [wStr, sqSumStr_eq, encITerms, TermsStr.countBlocks_frame, unaryToBinStr_unaryN, canonBits,
    decNat_addBits, decNat_addBits, decNat_encNat, decNat_encNat, decNat_encNat, List.length_map,
    wD]
  congr 1
  omega

theorem cobham_wStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => wStr (g v) := by
  unfold wStr
  exact cobham_canonBits_comp (cobham_addBits_comp (cobham_addBits_comp (cobham_sqSumStr_comp hg)
    (cobham_comp₁ cobham_unaryToBinStr (TermsStr.cobham_countBlocks_comp hg))) (Cobham.const _))

/-! ### `m = max (N, deg A)` and `(m+1)^6` -/

/-- Binary maximum (returns one of its canonical arguments). -/
def maxBinStr (a b : List Bool) : List Bool := caseBit₀ (ltBits a b) b a

theorem maxBinStr_encNat (a b : ℕ) : maxBinStr (encNat a) (encNat b) = encNat (max a b) := by
  rw [maxBinStr, ltBits_encNat]
  by_cases h : a < b
  · simp [h, max_eq_right h.le]
  · simp [h, max_eq_left (Nat.not_lt.1 h)]

theorem cobham_maxBinStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => maxBinStr (g₀ v) (g₁ v) := by
  unfold maxBinStr
  exact Cobham.iteFn (cobham_ltBits_comp h₀ h₁) h₁ h₀

/-- `m = max(N, deg A)`, in binary. -/
def mStr (N A : List Bool) : List Bool := maxBinStr N (degreeStr A)

theorem mStr_eq (N : ℕ) (A : ITerms) : mStr (encNat N) (encITerms A) = encNat (mD N A) := by
  rw [mStr, degreeStr_encITerms, maxBinStr_encNat]
  rfl

/-- `a^6`, in binary. -/
def pow6Str (a : List Bool) : List Bool :=
  canonBits (mulBits (canonBits (mulBits (canonBits (mulBits a a)) a))
    (canonBits (mulBits (canonBits (mulBits a a)) a)))

theorem pow6Str_encNat (a : ℕ) : pow6Str (encNat a) = encNat (a ^ 6) := by
  simp only [pow6Str, canonBits, decNat_mulBits, decNat_encNat]
  ring_nf

theorem cobham_pow6Str_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => pow6Str (g v) := by
  unfold pow6Str
  have h2 := cobham_canonBits_comp (cobham_mulBits_comp hg hg)
  have h3 := cobham_canonBits_comp (cobham_mulBits_comp h2 hg)
  exact cobham_canonBits_comp (cobham_mulBits_comp h3 h3)

/-! ### Binary → unary under a ruler -/

/-- One step of `binToUnaryStr`: increment the unary counter `s` while it is below `k`. -/
def binToUnaryStep (k s : List Bool) : List Bool :=
  caseBit₀ (ltBits (unaryToBinStr s) k) (true :: s) s

/-- `unaryN (min (decNat k) |T|)`: `|T|` clamped increments. -/
def binToUnaryStr (k T : List Bool) : List Bool := (binToUnaryStep k)^[T.length] []

theorem binToUnaryStep_iterate (k : ℕ) (i : ℕ) :
    (binToUnaryStep (encNat k))^[i] [] = unaryN (min i k) := by
  induction i with
  | zero => simp [unaryN]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, binToUnaryStep, unaryToBinStr_unaryN, ltBits_encNat]
    by_cases h : min i k < k
    · have h1 : min (i + 1) k = min i k + 1 := by omega
      simp [h, h1, unaryN_succ]
    · have h1 : min (i + 1) k = min i k := by omega
      simp [h, h1]

theorem binToUnaryStr_eq (k : ℕ) (T : List Bool) (h : k ≤ T.length) :
    binToUnaryStr (encNat k) T = unaryN k := by
  rw [binToUnaryStr, binToUnaryStep_iterate, min_eq_right h]

/-- Cobham via `Cobham.iterFn` with the ruler `T` itself (the state never exceeds the number of
steps). -/
theorem cobham_binToUnaryStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => binToUnaryStr (g₀ v) (g₁ v) := by
  have hf : Cobham fun w : Fin 2 → List Bool => binToUnaryStep (w 1) (w 0) := by
    unfold binToUnaryStep
    exact Cobham.iteFn (cobham_ltBits_comp (cobham_comp₁ cobham_unaryToBinStr (.proj 0)) (.proj 1))
      (cobham_cons true (.proj 0)) (.proj 0)
  have hlen : ∀ (k : List Bool) (i : ℕ), ((binToUnaryStep k)^[i] []).length ≤ i := by
    intro k i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      rcases SparseGcd.caseBit₀_cases (ltBits (unaryToBinStr ((binToUnaryStep k)^[i] [])) k)
        (true :: (binToUnaryStep k)^[i] []) ((binToUnaryStep k)^[i] []) with h | h <;>
        · rw [binToUnaryStep, h]
          try simp only [List.length_cons]
          omega
  have hit : Cobham fun v : Fin 2 → List Bool => binToUnaryStr (v 1) (v 0) :=
    (Cobham.iterFn (n := 1) (e := fun _ => []) (f := fun w => binToUnaryStep (w 1) (w 0))
      (j := fun w => w 0) Cobham.empty hf (.proj 0) (fun c v => hlen (v 0) c.length)).of_eq
      fun v => rfl
  exact (Cobham.comp₂ hit h₁ h₀).of_eq fun v => by simp

/-! ### `M = 2^{20(w+1)} (m+1)^6` -/

/-- `2^{|u|} · y` for a canonical `y > 0`: prepend `|u|` zero bits. -/
def shiftStr (u y : List Bool) : List Bool := List.replicate u.length false ++ y

theorem shiftStr_eq (k y : ℕ) (hy : 0 < y) :
    shiftStr (unaryN k) (encNat y) = encNat (2 ^ k * y) := by
  rw [shiftStr, length_unaryN]
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 2 ^ k * y ≠ 0 := by positivity
    rw [List.replicate_succ, List.cons_append, ih, encNat, encNat, pow_succ,
      show 2 ^ k * 2 * y = Nat.bit false (2 ^ k * y) by simp [Nat.bit]; ring,
      Nat.bits_append_bit _ _ (fun h => absurd h hpos)]

theorem cobham_shiftStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => shiftStr (g₀ v) (g₁ v) :=
  Cobham.appendFn (Cobham.zeroBlockFn h₀) h₁

/-- `M` from `N`, the `A`-terms and a unary ruler `T` with `20 (w+1) ≤ |T|`. -/
def MStr (N A T : List Bool) : List Bool :=
  shiftStr (binToUnaryStr (canonBits (mulBits (encNat 20) (succBits (wStr A)))) T)
    (pow6Str (succBits (mStr N A)))

theorem MStr_eq (N : ℕ) (A : ITerms) (T : List Bool) (hT : 20 * (wD A + 1) ≤ T.length) :
    MStr (encNat N) (encITerms A) T = encNat (MD N A) := by
  have h20 : canonBits (mulBits (encNat 20) (encNat (wD A + 1))) = encNat (20 * (wD A + 1)) := by
    rw [canonBits, decNat_mulBits, decNat_encNat, decNat_encNat]
  rw [MStr, wStr_eq, succBits_encNat, h20, binToUnaryStr_eq _ T hT, mStr_eq, succBits_encNat,
    pow6Str_encNat, shiftStr_eq _ _ (by positivity), MD]

theorem cobham_MStr_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v => MStr (g₀ v) (g₁ v) (g₂ v) := by
  unfold MStr mStr
  exact cobham_shiftStr_comp
    (cobham_binToUnaryStr_comp
      (cobham_canonBits_comp (cobham_mulBits_comp (Cobham.const _)
        (cobham_succBits_comp (cobham_wStr_comp h₁)))) h₂)
    (cobham_pow6Str_comp (cobham_succBits_comp
      (cobham_maxBinStr_comp h₀ (cobham_degreeStr_comp h₁))))

/-! ### Output assembly `A ++ [(-1, M), (1, M + N)]` -/

/-- The code of `H_M = A + X^M (X^N - 1)`, i.e. of the list `A ++ [(-1, M), (1, M + N)]`, given a
unary ruler `T` with `20 (w+1) ≤ |T|`. -/
def outStr (N A T : List Bool) : List Bool :=
  A ++ delimit (pair (encInt (-1)) (MStr N A T)) ++
    delimit (pair (encInt 1) (canonBits (addBits (MStr N A T) N)))

theorem outStr_eq (N : ℕ) (A : ITerms) (T : List Bool) (hT : 20 * (wD A + 1) ≤ T.length) :
    outStr (encNat N) (encITerms A) T = encITerms (outTermsD N A) := by
  have hM : canonBits (addBits (encNat (MD N A)) (encNat N)) = encNat (MD N A + N) := by
    rw [canonBits, decNat_addBits, decNat_encNat, decNat_encNat]
  rw [outStr, MStr_eq N A T hT, hM, outTermsD, encITerms_append]
  simp [encITerms, frame, encITerm, List.append_assoc]

theorem cobham_outStr_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v => outStr (g₀ v) (g₁ v) (g₂ v) := by
  unfold outStr
  have hM := cobham_MStr_comp h₀ h₁ h₂
  exact Cobham.appendFn
    (Cobham.appendFn h₁ (TermsStr.cobham_delimit_comp (cobham_pair_comp (Cobham.const _) hM)))
    (TermsStr.cobham_delimit_comp (cobham_pair_comp (Cobham.const _)
      (cobham_canonBits_comp (cobham_addBits_comp hM h₀))))

end SparseIrred.Machine
