import SparseDivComplexity.StringArith.Gcd
import SparseDivComplexity.StringArith.Blocks
import SparseDivComplexity.Appendix.IntTerms

/-!
# Appendix A.1 — bit complexity of the integer preprocessing

Binary encoding of sparse integer polynomials (signed coefficients) and polynomial-time (Cobham /
`FP`) implementations of the Appendix A.1 preprocessing: normalization, degree, content (gcd of the
coefficients), coefficient divisibility test, division of the coefficients by the content, and the
boundary-case decision procedure. Correctness is stated through the decoders against the term-list
functions of `Appendix/IntTerms.lean`.

Encoding: a signed integer is `pair [sign] (encNat |z|)` with `sign = true` iff `z < 0` (zero has
sign `false`); a term is `pair (encInt c) (encNat e)`; a term list is the framed concatenation of
its term codes (`StringArith.frame`); an instance `(g, f)` of Definition 7 is `pair (encITerms g)
(encITerms f)` — note the appendix's `(g, f)` order, kept here to match Appendix A.

## Design

Every string algorithm below is a composition of the block loops `mapBlocks` / `foldBlocks` of
`StringArith/Blocks.lean` with the numeral arithmetic of `StringArith` and a small layer of *signed*
arithmetic on sign–magnitude pairs (`negFlag`, `magOf`, `addInt`, `divInt`). Correctness is proved,
as in `BridgeString/Correctness.lean`, on the explicit representation of a framed term list as a
list of numeral pairs (`frameTerms`, `decodeTerms`); normalization is a left fold of a string copy
of `insertTermZ`, identified with `normalizeZ` by uniqueness of canonical forms. Cobham membership
is assembled as in `BridgeString/Complexity.lean` (insertion folds with packed parameters and the
accumulator-growth invariant).
-/

open Complexity SparseDiv.StringArith

namespace SparseDiv.Appendix

/-- Canonical encoding of a signed integer: sign flag then magnitude. -/
def encInt (z : ℤ) : List Bool := pair [decide (z < 0)] (encNat z.natAbs)

/-- Lenient decoding of a signed integer. -/
def decInt (s : List Bool) : ℤ :=
  if pairFst s = [true] then -(decNat (pairSnd s) : ℤ) else (decNat (pairSnd s) : ℤ)

@[simp] theorem decInt_encInt (z : ℤ) : decInt (encInt z) = z := by
  simp only [decInt, encInt, pairFst_pair, pairSnd_pair, decNat_encNat]
  split_ifs with h
  · simp only [List.cons.injEq, decide_eq_true_eq, and_true] at h
    omega
  · simp only [List.cons.injEq, decide_eq_true_eq, and_true] at h
    omega

theorem length_encInt (z : ℤ) : (encInt z).length = 4 + Nat.size z.natAbs := by
  rw [encInt, pair_length, List.length_singleton, length_encNat]

/-- Encode a signed term. -/
def encITerm (t : ℤ × ℕ) : List Bool := pair (encInt t.1) (encNat t.2)

/-- Decode a signed term block. -/
def decITerm (b : List Bool) : Option (ℤ × ℕ) :=
  (unpair? b).map fun ab ↦ (decInt ab.1, decNat ab.2)

@[simp] theorem decITerm_encITerm (t : ℤ × ℕ) : decITerm (encITerm t) = some t := by
  simp [decITerm, encITerm, pair]

/-- Encode a signed term list as framed blocks. -/
def encITerms (l : ITerms) : List Bool := frame (l.map encITerm)

/-- Decode a list of term blocks. -/
def decITermList : List (List Bool) → Option ITerms
  | [] => some []
  | b :: bs => do
    let t ← decITerm b
    let ts ← decITermList bs
    pure (t :: ts)

/-- Decode a signed term list. -/
def decITerms (s : List Bool) : Option ITerms := (undelimitBlocks s).bind decITermList

private theorem decITermList_map_encITerm (l : ITerms) :
    decITermList (l.map encITerm) = some l := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [decITermList, ih]

@[simp] theorem decITerms_encITerms (l : ITerms) : decITerms (encITerms l) = some l := by
  rw [decITerms, encITerms, frame, undelimitBlocks_flatten_delimit, Option.bind_some,
    decITermList_map_encITerm]

/-! ## Signed integers as sign–magnitude strings

A signed integer string is read leniently: it is negative iff it is a pair whose first component
is exactly `[true]`; its magnitude is the (lenient) numeral in the second component. -/

/-- Sign flag of a signed integer string: `[true]` iff the string is negative. -/
def negFlag (x : List Bool) : List Bool := Cobham.eqFlag (pairFst x) [true]

/-- Magnitude numeral of a signed integer string. -/
def magOf (x : List Bool) : List Bool := pairSnd x

/-- Zero test of a signed integer string. -/
def isZeroInt (x : List Bool) : List Bool := isZeroBits (magOf x)

/-- Signed addition: equal signs add the magnitudes, different signs subtract the smaller magnitude
from the larger and keep the sign of the larger. -/
def addInt (x y : List Bool) : List Bool :=
  caseBit₀ (xorFlag (negFlag x) (negFlag y))
    (caseBit₀ (ltBits (magOf x) (magOf y)) (pair (negFlag y) (subBits (magOf y) (magOf x)))
      (pair (negFlag x) (subBits (magOf x) (magOf y))))
    (pair (negFlag x) (addBits (magOf x) (magOf y)))

/-- Floor division (`Int.ediv`) of a signed integer string by a numeral: a zero divisor gives `0`;
a negative dividend rounds the magnitude quotient up when the division is not exact. -/
def divInt (x c : List Bool) : List Bool :=
  caseBit₀ (isZeroBits c) (pair [false] [])
    (caseBit₀ (negFlag x)
      (pair [true] (caseBit₀ (dvdBits (magOf x) c) (divBits (magOf x) c)
        (succBits (divBits (magOf x) c))))
      (pair [false] (divBits (magOf x) c)))

theorem negFlag_flag (x : List Bool) : negFlag x = [true] ∨ negFlag x = [false] :=
  Cobham.eqFlag_flag _ _

theorem decInt_of_negFlag_true {x : List Bool} (h : negFlag x = [true]) :
    decInt x = -(decNat (magOf x) : ℤ) := by
  rw [negFlag, Cobham.eqFlag_eq_true_iff] at h
  simp [decInt, magOf, h]

theorem decInt_of_negFlag_false {x : List Bool} (h : negFlag x = [false]) :
    decInt x = decNat (magOf x) := by
  have h' : pairFst x ≠ [true] := fun h' ↦ by
    have := (Cobham.eqFlag_eq_true_iff (pairFst x) [true]).2 h'
    rw [negFlag] at h
    rw [h] at this
    simp at this
  simp [decInt, magOf, h']

@[simp] theorem decInt_pair_true (m : List Bool) : decInt (pair [true] m) = -(decNat m : ℤ) := by
  simp [decInt]

@[simp] theorem decInt_pair_false (m : List Bool) : decInt (pair [false] m) = decNat m := by
  simp [decInt]

theorem natAbs_decInt (x : List Bool) : (decInt x).natAbs = decNat (magOf x) := by
  rcases negFlag_flag x with h | h
  · rw [decInt_of_negFlag_true h, Int.natAbs_neg, Int.natAbs_natCast]
  · rw [decInt_of_negFlag_false h, Int.natAbs_natCast]

theorem isZeroInt_eq_true_iff (x : List Bool) : isZeroInt x = [true] ↔ decInt x = 0 := by
  rw [isZeroInt, isZeroBits_eq_true_iff, ← natAbs_decInt, Int.natAbs_eq_zero]

theorem isZeroInt_flag (x : List Bool) : isZeroInt x = [true] ∨ isZeroInt x = [false] :=
  isZeroBits_flag _

theorem decInt_addInt (x y : List Bool) : decInt (addInt x y) = decInt x + decInt y := by
  unfold addInt
  rcases negFlag_flag x with hx | hx <;> rcases negFlag_flag y with hy | hy
  · rw [decInt_of_negFlag_true hx, decInt_of_negFlag_true hy, hx, hy, xorFlag_single]
    simp only [Bool.xor_self, caseBit₀_cons, Bool.cond_false, decInt_pair_true, decNat_addBits]
    push_cast
    ring
  · rw [decInt_of_negFlag_true hx, decInt_of_negFlag_false hy, hx, hy, xorFlag_single]
    simp only [Bool.true_xor, Bool.not_false, caseBit₀_cons, Bool.cond_true]
    rcases ltBits_flag (magOf x) (magOf y) with h | h
    · have := (ltBits_eq_true_iff _ _).1 h
      rw [h, caseBit₀_cons, Bool.cond_true, decInt_pair_false, decNat_subBits]
      omega
    · have := (ltBits_eq_false_iff _ _).1 h
      rw [h, caseBit₀_cons, Bool.cond_false, decInt_pair_true, decNat_subBits]
      omega
  · rw [decInt_of_negFlag_false hx, decInt_of_negFlag_true hy, hx, hy, xorFlag_single]
    simp only [Bool.false_xor, caseBit₀_cons, Bool.cond_true]
    rcases ltBits_flag (magOf x) (magOf y) with h | h
    · have := (ltBits_eq_true_iff _ _).1 h
      rw [h, caseBit₀_cons, Bool.cond_true, decInt_pair_true, decNat_subBits]
      omega
    · have := (ltBits_eq_false_iff _ _).1 h
      rw [h, caseBit₀_cons, Bool.cond_false, decInt_pair_false, decNat_subBits]
      omega
  · rw [decInt_of_negFlag_false hx, decInt_of_negFlag_false hy, hx, hy, xorFlag_single]
    simp only [Bool.xor_self, caseBit₀_cons, Bool.cond_false, decInt_pair_false, decNat_addBits]
    push_cast
    ring

/-- The divisibility flag is a flag. -/
theorem dvdBits_flag (a b : List Bool) : dvdBits a b = [true] ∨ dvdBits a b = [false] :=
  isZeroBits_flag _

/-- Floor division of a negative by a positive divisor that does not divide it. -/
private theorem neg_natCast_ediv_of_not_dvd {m c : ℕ} (hc : c ≠ 0) (hd : ¬ c ∣ m) :
    (-(m : ℤ)) / (c : ℤ) = -((m / c + 1 : ℕ) : ℤ) := by
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc
  have h1 : (m : ℤ) = (m / c : ℕ) * c + (m % c : ℕ) := by
    exact_mod_cast (Nat.div_add_mod' m c).symm
  have hr : 0 < m % c := Nat.pos_of_ne_zero fun h ↦ hd (Nat.dvd_of_mod_eq_zero h)
  have hr2 : m % c < c := Nat.mod_lt _ (Nat.pos_of_ne_zero hc)
  have : (-(m : ℤ)) = ((c : ℤ) - (m % c : ℕ)) + (-((m / c : ℕ) : ℤ) - 1) * c := by
    rw [h1]; push_cast; ring
  rw [this, Int.add_mul_ediv_right _ _ hc', Int.ediv_eq_zero_of_lt (by omega) (by omega)]
  push_cast
  ring

theorem decInt_divInt (x c : List Bool) : decInt (divInt x c) = decInt x / (decNat c : ℤ) := by
  unfold divInt
  rcases isZeroBits_flag c with h0 | h0
  · rw [(isZeroBits_eq_true_iff c).1 h0, h0, caseBit₀_cons, Bool.cond_true, decInt_pair_false]
    simp
  · have hc : decNat c ≠ 0 := fun h ↦ by
      have := (isZeroBits_eq_true_iff c).2 h
      rw [h0] at this
      simp at this
    rw [h0, caseBit₀_cons, Bool.cond_false]
    rcases negFlag_flag x with hx | hx
    · rw [hx, caseBit₀_cons, Bool.cond_true, decInt_pair_true, decInt_of_negFlag_true hx]
      rcases dvdBits_flag (magOf x) c with hd | hd
      · have hd' := (dvdBits_eq_true_iff _ _ hc).1 hd
        rw [hd, caseBit₀_cons, Bool.cond_true, decNat_divBits _ _ hc,
          Int.neg_ediv_of_dvd (Int.natCast_dvd_natCast.mpr hd')]
        simp
      · have hd' : ¬ decNat c ∣ decNat (magOf x) := fun h ↦ by
          have := (dvdBits_eq_true_iff _ _ hc).2 h
          rw [hd] at this
          simp at this
        rw [hd, caseBit₀_cons, Bool.cond_false, decNat_succBits, decNat_divBits _ _ hc,
          neg_natCast_ediv_of_not_dvd hc hd']
    · rw [hx, caseBit₀_cons, Bool.cond_false, decInt_pair_false, decInt_of_negFlag_false hx,
        decNat_divBits _ _ hc]
      simp

/-! ### Cobham membership and length of the signed arithmetic -/

theorem cobham_negFlag_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ negFlag (g v) :=
  (Cobham.eqFlag_mem (cobham_pairFst_comp hg) (Cobham.const [true])).of_eq fun _ ↦ rfl

theorem cobham_magOf_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ magOf (g v) :=
  cobham_pairSnd_comp hg

theorem cobham_isZeroInt_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ isZeroInt (g v) :=
  cobham_isZeroBits_comp (cobham_magOf_comp hg)

theorem cobham_addInt_comp {n : ℕ} {gx gy : (Fin n → List Bool) → List Bool}
    (hx : Cobham gx) (hy : Cobham gy) :
    Cobham fun v : Fin n → List Bool ↦ addInt (gx v) (gy v) := by
  have hnx := cobham_negFlag_comp hx
  have hny := cobham_negFlag_comp hy
  have hmx := cobham_magOf_comp hx
  have hmy := cobham_magOf_comp hy
  exact Cobham.iteFn (cobham_xorFlag_comp hnx hny)
    (Cobham.iteFn (cobham_ltBits_comp hmx hmy) (cobham_pair_comp hny (cobham_subBits_comp hmy hmx))
      (cobham_pair_comp hnx (cobham_subBits_comp hmx hmy)))
    (cobham_pair_comp hnx (cobham_addBits_comp hmx hmy))

theorem cobham_divInt_comp {n : ℕ} {gx gc : (Fin n → List Bool) → List Bool}
    (hx : Cobham gx) (hc : Cobham gc) :
    Cobham fun v : Fin n → List Bool ↦ divInt (gx v) (gc v) := by
  have hm := cobham_magOf_comp hx
  have hq := cobham_divBits_comp hm hc
  exact Cobham.iteFn (cobham_isZeroBits_comp hc) (Cobham.const _)
    (Cobham.iteFn (cobham_negFlag_comp hx)
      (cobham_pair_comp (Cobham.const [true])
        (Cobham.iteFn (cobham_dvdBits_comp hm hc) hq (cobham_succBits_comp hq)))
      (cobham_pair_comp (Cobham.const [false]) hq))

/-- A bit dispatch is bounded by any common bound of its two branches. -/
private theorem caseBit₀_length_le_of {s x y : List Bool} {N : ℕ} (hx : x.length ≤ N)
    (hy : y.length ≤ N) : (caseBit₀ s x y).length ≤ N := by
  cases s with
  | nil => exact hy
  | cons b s => cases b <;> simpa

theorem length_negFlag (x : List Bool) : (negFlag x).length = 1 := by
  rcases negFlag_flag x with h | h <;> simp [h]

theorem length_magOf_le (x : List Bool) : (magOf x).length ≤ x.length :=
  pairSnd_length_le x

theorem length_addInt_le (x y : List Bool) : (addInt x y).length ≤ x.length + y.length + 6 := by
  have h1 := length_magOf_le x
  have h2 := length_magOf_le y
  have h3 := length_addBits_le (magOf x) (magOf y)
  have h4 := length_subBits_le (magOf x) (magOf y)
  have h5 := length_subBits_le (magOf y) (magOf x)
  have h6 := length_negFlag x
  have h7 := length_negFlag y
  unfold addInt
  refine caseBit₀_length_le_of (caseBit₀_length_le_of ?_ ?_) ?_ <;> rw [pair_length] <;> omega

theorem length_divInt_le (x c : List Bool) : (divInt x c).length ≤ x.length + c.length + 7 := by
  have h1 := length_magOf_le x
  have h2 := length_divBits_le (magOf x) c
  have h3 := length_succBits_le (divBits (magOf x) c)
  unfold divInt
  refine caseBit₀_length_le_of (by simp) (caseBit₀_length_le_of ?_ ?_) <;> rw [pair_length]
  · refine (Nat.add_le_add_left (caseBit₀_length_le_of (Nat.le_succ _) h3) _).trans ?_
    simp only [List.length_singleton]
    omega
  · simp only [List.length_singleton]
    omega

/-! ## Framed lists of term blocks -/

/-- Coefficient (signed integer string) of a term block `pair c e`. -/
def coefZ (b : List Bool) : List Bool := pairFst b

/-- Exponent numeral of a term block `pair c e`. -/
def expZ (b : List Bool) : List Bool := pairSnd b

/-- The term block of a pair (signed coefficient string, exponent numeral). -/
private def blk (t : List Bool × List Bool) : List Bool := pair t.1 t.2

/-- The framed string of a list of such pairs. -/
private def frameTerms (ts : List (List Bool × List Bool)) : List Bool := frame (ts.map blk)

/-- The signed term list denoted by a list of such pairs. -/
private def decodeTerms (ts : List (List Bool × List Bool)) : ITerms :=
  ts.map fun t ↦ (decInt t.1, decNat t.2)

/-- The numeral pairs of the canonical encoding. -/
private def encPairs (l : ITerms) : List (List Bool × List Bool) :=
  l.map fun t ↦ (encInt t.1, encNat t.2)

private theorem coefZ_blk (t : List Bool × List Bool) : coefZ (blk t) = t.1 := by
  simp [coefZ, blk]

private theorem expZ_blk (t : List Bool × List Bool) : expZ (blk t) = t.2 := by
  simp [expZ, blk]

private theorem frameTerms_nil : frameTerms [] = [] := rfl

private theorem frameTerms_cons (t : List Bool × List Bool) (ts : List (List Bool × List Bool)) :
    frameTerms (t :: ts) = pair (blk t) (frameTerms ts) := by
  simp [frameTerms, frame, pair]

private theorem frameTerms_append (ts ts' : List (List Bool × List Bool)) :
    frameTerms (ts ++ ts') = frameTerms ts ++ frameTerms ts' := by
  simp [frameTerms, frame]

private theorem frameTerms_singleton (t : List Bool × List Bool) :
    frameTerms [t] = delimit (blk t) := by
  simp [frameTerms, frame]

private theorem frameTerms_eq_nil_iff (ts : List (List Bool × List Bool)) :
    frameTerms ts = [] ↔ ts = [] := by
  cases ts with
  | nil => simp [frameTerms_nil]
  | cons t ts =>
    simp only [List.cons_ne_nil, iff_false]
    rw [frameTerms_cons]
    exact pair_ne_nil _ _

private theorem decodeTerms_nil : decodeTerms [] = [] := rfl

private theorem decodeTerms_cons (t : List Bool × List Bool) (ts : List (List Bool × List Bool)) :
    decodeTerms (t :: ts) = (decInt t.1, decNat t.2) :: decodeTerms ts := rfl

private theorem decodeTerms_eq_nil_iff (ts : List (List Bool × List Bool)) :
    decodeTerms ts = [] ↔ ts = [] := by
  simp [decodeTerms]

private theorem encITerms_eq_frameTerms (l : ITerms) : encITerms l = frameTerms (encPairs l) := by
  simp only [encITerms, frameTerms, encPairs, List.map_map]
  rfl

private theorem decodeTerms_encPairs (l : ITerms) : decodeTerms (encPairs l) = l := by
  simp [decodeTerms, encPairs, List.map_map, Function.comp_def]

/-- Folding over the blocks of a framed list is folding over the list. -/
private theorem foldBlocks_frameTerms (step : List Bool → List Bool → List Bool)
    (init : List Bool) (ts : List (List Bool × List Bool)) :
    foldBlocks step init (frameTerms ts) = ts.foldl (fun acc t ↦ step acc (blk t)) init := by
  rw [frameTerms, foldBlocks_frame, List.foldl_map]

/-- Mapping over the blocks of a framed list of term blocks. -/
private theorem mapBlocks_frameTerms (f : List Bool → List Bool)
    (ts : List (List Bool × List Bool)) :
    mapBlocks f (frameTerms ts) = frame (ts.map fun t ↦ f (blk t)) := by
  rw [frameTerms, mapBlocks_frame, List.map_map]
  rfl

private theorem decITermList_map_blk (ts : List (List Bool × List Bool)) :
    decITermList (ts.map blk) = some (decodeTerms ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [decITermList, decITerm, blk, ih, decodeTerms_cons]

private theorem decITerms_frameTerms (ts : List (List Bool × List Bool)) :
    decITerms (frameTerms ts) = some (decodeTerms ts) := by
  rw [decITerms, frameTerms, frame, undelimitBlocks_flatten_delimit, Option.bind_some,
    decITermList_map_blk]

/-! ## String-level preprocessing (definition bodies free; specified by the theorems below) -/

/-- One step of the insertion of the signed term `(c, e)` into a sorted accumulator: the state is
`pair inserted acc`. Mirrors `insertTermZ`. -/
def insertStepZ (c e : List Bool) (state b : List Bool) : List Bool :=
  let ins := pairFst state
  let acc := pairSnd state
  let c' := coefZ b
  let e' := expZ b
  caseBit₀ ins (pair ins (acc ++ delimit b))
    (caseBit₀ (ltBits e e')
      (pair [true] (acc ++ caseBit₀ (isZeroInt c) [] (delimit (pair c e)) ++ delimit b))
      (caseBit₀ (eqBits e e')
        (pair [true] (acc ++ caseBit₀ (isZeroInt (addInt c c')) []
          (delimit (pair (addInt c c') e))))
        (pair [false] (acc ++ delimit b))))

/-- Insert the signed term `(c, e)` into a sorted framed accumulator. -/
def insertZStr (c e acc : List Bool) : List Bool :=
  let r := foldBlocks (insertStepZ c e) (pair [false] []) acc
  caseBit₀ (pairFst r) (pairSnd r)
    (pairSnd r ++ caseBit₀ (isZeroInt c) [] (delimit (pair c e)))

/-- Normalization of an encoded signed term list: left fold of `insertZStr`. -/
def normalizeZStr (s : List Bool) : List Bool :=
  foldBlocks (fun acc b ↦ insertZStr (coefZ b) (expZ b) acc) [] s

/-- The degree numeral of an encoded term list: running maximum of the exponents. -/
def degreeStr (s : List Bool) : List Bool :=
  foldBlocks (fun acc b ↦ caseBit₀ (ltBits acc (expZ b)) (expZ b) acc) [] s

/-- The content numeral (gcd of the absolute coefficients) of an encoded term list. -/
def contentStr (s : List Bool) : List Bool :=
  foldBlocks (fun acc b ↦ gcdBits (magOf (coefZ b)) acc) [] s

/-- Flag: the numeral `c` divides the numeral `m` (a zero `c` divides only `0`). -/
def dvdFlag (c m : List Bool) : List Bool :=
  caseBit₀ (isZeroBits c) (isZeroBits m) (dvdBits m c)

/-- Flag: the numeral `c` divides every coefficient of the encoded term list. -/
def dvdAllStr (c s : List Bool) : List Bool :=
  foldBlocks (fun acc b ↦ andBit acc (dvdFlag c (magOf (coefZ b)))) [true] s

/-- Divide every coefficient of the encoded term list by the numeral `c`. -/
def divCoeffsStr (c s : List Bool) : List Bool :=
  mapBlocks (fun b ↦ pair (divInt (coefZ b) c) (expZ b)) s

/-- The boundary decision on an encoded instance `pair g f`: `[true]` (decided YES),
`[false]` (decided NO), `[]` (main branch needed or malformed). -/
def boundaryDecideStr (s : List Bool) : List Bool :=
  let g' := normalizeZStr (pairFst s)
  let f' := normalizeZStr (pairSnd s)
  caseBit₀ (nonemptyFlag g')
    (caseBit₀ (nonemptyFlag f')
      (caseBit₀ (andBit (isZeroBits (expZ (pairFst g'))) (notBit (nonemptyFlag (pairSnd g'))))
        (notBit (dvdAllStr (magOf (coefZ (pairFst g'))) f'))
        (caseBit₀ (ltBits (degreeStr f') (degreeStr g')) [true] []))
      [false])
    (caseBit₀ (nonemptyFlag f') [true] [false])

/-! ### Insertion -/

/-- Selecting on a flag. -/
private theorem caseBit₀_of_flag {x : List Bool} (hx : x = [true] ∨ x = [false])
    (u v : List Bool) : caseBit₀ x u v = if x = [true] then u else v := by
  rcases hx with rfl | rfl <;> simp

/-- The optional block of the inserted term. -/
private theorem append_caseBit₀_isZeroInt (ts : List (List Bool × List Bool))
    (c e : List Bool) :
    frameTerms ts ++ caseBit₀ (isZeroInt c) [] (delimit (pair c e)) =
      frameTerms (ts ++ if isZeroInt c = [true] then [] else [(c, e)]) := by
  rw [caseBit₀_of_flag (isZeroInt_flag c)]
  split_ifs <;> simp [frameTerms_append, frameTerms_singleton, blk]

/-- String-level copy of `insertTermZ` on lists of numeral pairs. -/
private def insertTermS (c e : List Bool) :
    List (List Bool × List Bool) → List (List Bool × List Bool)
  | [] => if isZeroInt c = [true] then [] else [(c, e)]
  | (c', e') :: rest =>
    if ltBits e e' = [true] then
      (if isZeroInt c = [true] then (c', e') :: rest else (c, e) :: (c', e') :: rest)
    else if eqBits e e' = [true] then
      (if isZeroInt (addInt c c') = [true] then rest else (addInt c c', e) :: rest)
    else (c', e') :: insertTermS c e rest

/-- Once the term has been inserted, the remaining blocks are copied. -/
private theorem foldl_insertStepZ_true (c e : List Bool) (ts₀ ts : List (List Bool × List Bool)) :
    ts.foldl (fun st t ↦ insertStepZ c e st (blk t)) (pair [true] (frameTerms ts₀)) =
      pair [true] (frameTerms (ts₀ ++ ts)) := by
  induction ts generalizing ts₀ with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons]
    have hstep : insertStepZ c e (pair [true] (frameTerms ts₀)) (blk t) =
        pair [true] (frameTerms (ts₀ ++ [t])) := by
      simp [insertStepZ, frameTerms_append, frameTerms_singleton]
    rw [hstep, ih, List.append_assoc, List.singleton_append]

/-- The fold state before the term has been inserted. -/
private def insFold (c e : List Bool) (ts₀ ts : List (List Bool × List Bool)) : List Bool :=
  ts.foldl (fun st t ↦ insertStepZ c e st (blk t)) (pair [false] (frameTerms ts₀))

/-- Finishing the insertion from the fold state (the body of `insertZStr`). -/
private def insFinish (c e r : List Bool) : List Bool :=
  caseBit₀ (pairFst r) (pairSnd r) (pairSnd r ++ caseBit₀ (isZeroInt c) [] (delimit (pair c e)))

private theorem insFinish_true (c e x : List Bool) : insFinish c e (pair [true] x) = x := by
  simp [insFinish]

private theorem delimit_pair_eq_frameTerms (c e : List Bool) :
    delimit (pair c e) = frameTerms [(c, e)] :=
  (frameTerms_singleton (c, e)).symm

/-- Before the term has been inserted, the fold behaves as `insertTermS`. -/
private theorem insFinish_insFold (c e : List Bool) (ts₀ ts : List (List Bool × List Bool)) :
    insFinish c e (insFold c e ts₀ ts) = frameTerms (ts₀ ++ insertTermS c e ts) := by
  induction ts generalizing ts₀ with
  | nil =>
    simp only [insFold, List.foldl_nil, insFinish, pairFst_pair, pairSnd_pair, caseBit₀_cons,
      Bool.cond_false, insertTermS]
    exact append_caseBit₀_isZeroInt ts₀ c e
  | cons t ts ih =>
    obtain ⟨c', e'⟩ := t
    have hstep : insertStepZ c e (pair [false] (frameTerms ts₀)) (blk (c', e')) =
        caseBit₀ (ltBits e e')
          (pair [true] (frameTerms ts₀ ++ caseBit₀ (isZeroInt c) [] (delimit (pair c e)) ++
            delimit (pair c' e')))
          (caseBit₀ (eqBits e e')
            (pair [true] (frameTerms ts₀ ++ caseBit₀ (isZeroInt (addInt c c')) []
              (delimit (pair (addInt c c') e))))
            (pair [false] (frameTerms ts₀ ++ delimit (pair c' e')))) := by
      simp only [insertStepZ, blk, coefZ, expZ, pairFst_pair, pairSnd_pair, caseBit₀_cons,
        Bool.cond_false]
    rw [insFold, List.foldl_cons, hstep, caseBit₀_of_flag (ltBits_flag e e'),
      caseBit₀_of_flag (eqBits_flag e e'), append_caseBit₀_isZeroInt,
      append_caseBit₀_isZeroInt, delimit_pair_eq_frameTerms c' e']
    simp only [insertTermS]
    split_ifs with h₁ h₂ h₃ h₄
    · rw [← frameTerms_append, foldl_insertStepZ_true, insFinish_true]
      simp
    · rw [← frameTerms_append, foldl_insertStepZ_true, insFinish_true]
      simp
    · rw [foldl_insertStepZ_true, insFinish_true]
      simp
    · rw [foldl_insertStepZ_true, insFinish_true]
      simp
    · have := ih (ts₀ ++ [(c', e')])
      rw [insFold] at this
      rw [← frameTerms_append, this]
      simp

/-- `insertZStr` acts on framed lists as `insertTermS`. -/
private theorem insertZStr_frameTerms (c e : List Bool) (ts : List (List Bool × List Bool)) :
    insertZStr c e (frameTerms ts) = frameTerms (insertTermS c e ts) := by
  have := insFinish_insFold c e [] ts
  rw [insFold, insFinish, frameTerms_nil, List.nil_append] at this
  rw [insertZStr, foldBlocks_frameTerms]
  exact this

/-- The decoding of `insertTermS` is `insertTermZ`. -/
private theorem decodeTerms_insertTermS (c e : List Bool) (ts : List (List Bool × List Bool)) :
    decodeTerms (insertTermS c e ts) = insertTermZ (decInt c) (decNat e) (decodeTerms ts) := by
  induction ts with
  | nil =>
    simp only [insertTermS, decodeTerms_nil, insertTermZ, isZeroInt_eq_true_iff]
    split_ifs <;> rfl
  | cons t ts ih =>
    obtain ⟨c', e'⟩ := t
    simp only [insertTermS, decodeTerms_cons, insertTermZ, ltBits_eq_true_iff, eqBits_eq_true_iff,
      isZeroInt_eq_true_iff, decInt_addInt]
    split_ifs <;> simp [decodeTerms_cons, ih, decInt_addInt]

/-! ### Normalization -/

/-- The string normalization on lists of numeral pairs: a left fold of `insertTermS`. -/
private def normalizeS (ts : List (List Bool × List Bool)) : List (List Bool × List Bool) :=
  ts.foldl (fun acc t ↦ insertTermS t.1 t.2 acc) []

private theorem foldl_insertZStr_frameTerms (ts₀ ts : List (List Bool × List Bool)) :
    ts.foldl (fun acc t ↦ insertZStr t.1 t.2 acc) (frameTerms ts₀) =
      frameTerms (ts.foldl (fun acc t ↦ insertTermS t.1 t.2 acc) ts₀) := by
  induction ts generalizing ts₀ with
  | nil => rfl
  | cons t ts ih => rw [List.foldl_cons, List.foldl_cons, insertZStr_frameTerms, ih]

/-- `normalizeZStr` acts on framed lists as `normalizeS`. -/
private theorem normalizeZStr_frameTerms (ts : List (List Bool × List Bool)) :
    normalizeZStr (frameTerms ts) = frameTerms (normalizeS ts) := by
  rw [normalizeZStr, foldBlocks_frameTerms]
  simp only [coefZ_blk, expZ_blk]
  exact foldl_insertZStr_frameTerms [] ts

/-- The left fold of `insertTermZ` over a term list. -/
private def normalizeL (l : ITerms) : ITerms :=
  l.foldl (fun acc t ↦ insertTermZ t.1 t.2 acc) []

private theorem decodeTerms_foldl_insertTermS (ts₀ ts : List (List Bool × List Bool)) :
    decodeTerms (ts.foldl (fun acc t ↦ insertTermS t.1 t.2 acc) ts₀) =
      (decodeTerms ts).foldl (fun acc t ↦ insertTermZ t.1 t.2 acc) (decodeTerms ts₀) := by
  induction ts generalizing ts₀ with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons, decodeTerms_cons, List.foldl_cons, ih, decodeTerms_insertTermS]

/-- The decoding of `normalizeS` is the left fold of `insertTermZ`. -/
private theorem decodeTerms_normalizeS (ts : List (List Bool × List Bool)) :
    decodeTerms (normalizeS ts) = normalizeL (decodeTerms ts) :=
  decodeTerms_foldl_insertTermS [] ts

/-- **Uniqueness of canonical forms**: a canonical list is determined by its polynomial. -/
private theorem eq_of_normalizedZ_of_toPolyZ_eq {l₁ : ITerms} :
    ∀ {l₂ : ITerms}, NormalizedZ l₁ → NormalizedZ l₂ → toPolyZ l₁ = toPolyZ l₂ → l₁ = l₂ := by
  induction l₁ with
  | nil =>
    intro l₂ _ h₂ h
    have := card_support_toPolyZ_of_normalizedZ h₂
    rw [← h, toPolyZ_nil, Polynomial.support_zero, Finset.card_empty] at this
    exact (List.length_eq_zero_iff.mp this.symm).symm
  | cons t₁ l₁ ih =>
    intro l₂ h₁ h₂ h
    cases l₂ with
    | nil =>
      have := card_support_toPolyZ_of_normalizedZ h₁
      rw [h, toPolyZ_nil, Polynomial.support_zero, Finset.card_empty] at this
      simp at this
    | cons t₂ l₂ =>
      obtain ⟨c₁, e₁⟩ := t₁
      obtain ⟨c₂, e₂⟩ := t₂
      have hs := support_toPolyZ_of_normalizedZ h₁
      rw [h, support_toPolyZ_of_normalizedZ h₂] at hs
      obtain ⟨hpw₁, hb₁⟩ := h₁
      obtain ⟨hpw₂, hb₂⟩ := h₂
      rw [List.pairwise_cons] at hpw₁ hpw₂
      have he₁ : e₁ = e₂ ∨ e₂ < e₁ := by
        have : e₁ ∈ (((c₂, e₂) :: l₂).map Prod.snd).toFinset := by
          rw [hs]; simp
        simp only [List.mem_toFinset, List.map_cons, List.mem_cons, List.mem_map] at this
        rcases this with h | ⟨t, ht, rfl⟩
        · exact Or.inl h
        · exact Or.inr (hpw₂.1 t ht)
      have he₂ : e₂ = e₁ ∨ e₁ < e₂ := by
        have : e₂ ∈ (((c₁, e₁) :: l₁).map Prod.snd).toFinset := by
          rw [← hs]; simp
        simp only [List.mem_toFinset, List.map_cons, List.mem_cons, List.mem_map] at this
        rcases this with h | ⟨t, ht, rfl⟩
        · exact Or.inl h
        · exact Or.inr (hpw₁.1 t ht)
      have he : e₁ = e₂ := by omega
      subst he
      have hc : c₁ = c₂ := by
        have h1 := coeff_toPolyZ_of_normalizedZ_mem ⟨List.pairwise_cons.mpr hpw₁, hb₁⟩
          (List.mem_cons_self (a := (c₁, e₁)) (l := l₁))
        have h2 := coeff_toPolyZ_of_normalizedZ_mem ⟨List.pairwise_cons.mpr hpw₂, hb₂⟩
          (List.mem_cons_self (a := (c₂, e₁)) (l := l₂))
        simp only at h1 h2
        rw [← h1, ← h2, h]
      subst hc
      congr 1
      refine ih ⟨hpw₁.2, fun t ht ↦ hb₁ t (List.mem_cons_of_mem _ ht)⟩
        ⟨hpw₂.2, fun t ht ↦ hb₂ t (List.mem_cons_of_mem _ ht)⟩ ?_
      rw [toPolyZ_cons, toPolyZ_cons] at h
      exact add_left_cancel h

/-- Folding `insertTermZ` from a canonical accumulator stays canonical and adds the polynomial. -/
private theorem normalizedZ_foldl_insertTermZ (l : ITerms) {acc : ITerms}
    (hacc : NormalizedZ acc) :
    NormalizedZ (l.foldl (fun acc t ↦ insertTermZ t.1 t.2 acc) acc) ∧
      toPolyZ (l.foldl (fun acc t ↦ insertTermZ t.1 t.2 acc) acc) = toPolyZ acc + toPolyZ l := by
  induction l generalizing acc with
  | nil => simp [hacc]
  | cons t l ih =>
    obtain ⟨h1, h2⟩ := ih (normalizedZ_insertTermZ t.1 t.2 hacc)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, toPolyZ_insertTermZ, toPolyZ_cons]
    ring

/-- **The left fold of `insertTermZ` is `normalizeZ`** (uniqueness of canonical forms). -/
private theorem normalizeL_eq_normalizeZ (l : ITerms) : normalizeL l = normalizeZ l := by
  obtain ⟨h1, h2⟩ := normalizedZ_foldl_insertTermZ l (acc := []) ⟨List.Pairwise.nil, by simp⟩
  rw [toPolyZ_nil, zero_add] at h2
  exact eq_of_normalizedZ_of_toPolyZ_eq h1 (normalizedZ_normalizeZ l)
    (by rw [toPolyZ_normalizeZ]; exact h2)

/-- The decoding of the string normalization of a framed list. -/
private theorem decodeTerms_normalizeS_eq (ts : List (List Bool × List Bool)) :
    decodeTerms (normalizeS ts) = normalizeZ (decodeTerms ts) := by
  rw [decodeTerms_normalizeS, normalizeL_eq_normalizeZ]

theorem decITerms_normalizeZStr (l : ITerms) :
    decITerms (normalizeZStr (encITerms l)) = some (normalizeZ l) := by
  rw [encITerms_eq_frameTerms, normalizeZStr_frameTerms, decITerms_frameTerms,
    decodeTerms_normalizeS_eq, decodeTerms_encPairs]

/-! ### Degree -/

/-- One step of the running maximum. -/
private theorem decNat_maxStep (acc e : List Bool) :
    decNat (caseBit₀ (ltBits acc e) e acc) = max (decNat acc) (decNat e) := by
  rcases ltBits_flag acc e with h | h
  · have := (ltBits_eq_true_iff _ _).1 h
    rw [h, caseBit₀_cons, Bool.cond_true]
    omega
  · have := (ltBits_eq_false_iff _ _).1 h
    rw [h, caseBit₀_cons, Bool.cond_false]
    omega

/-- The running maximum of the exponents over a list of numeral pairs. -/
private theorem decNat_foldl_maxStep (ts : List (List Bool × List Bool)) (init : List Bool) :
    decNat (ts.foldl (fun acc t ↦ caseBit₀ (ltBits acc t.2) t.2 acc) init) =
      max (decNat init) (degreeZ (decodeTerms ts)) := by
  induction ts generalizing init with
  | nil => simp [decodeTerms_nil, degreeZ]
  | cons t ts ih =>
    rw [List.foldl_cons, ih, decNat_maxStep, decodeTerms_cons]
    simp only [degreeZ, List.map_cons, List.foldr_cons]
    omega

/-- `degreeStr` on a framed list denotes the degree of the decoded list. -/
private theorem decNat_degreeStr_frameTerms (ts : List (List Bool × List Bool)) :
    decNat (degreeStr (frameTerms ts)) = degreeZ (decodeTerms ts) := by
  rw [degreeStr, foldBlocks_frameTerms]
  simp only [expZ_blk]
  rw [decNat_foldl_maxStep, decNat_nil, Nat.zero_max]

theorem decNat_degreeStr (l : ITerms) : decNat (degreeStr (encITerms l)) = degreeZ l := by
  rw [encITerms_eq_frameTerms, decNat_degreeStr_frameTerms, decodeTerms_encPairs]

/-! ### Content -/

/-- The running gcd of the magnitudes over a list of numeral pairs. -/
private theorem decNat_foldl_gcdStep (ts : List (List Bool × List Bool)) (init : List Bool) :
    decNat (ts.foldl (fun acc t ↦ gcdBits (magOf t.1) acc) init) =
      Nat.gcd (decNat init) (contentZ (decodeTerms ts)) := by
  induction ts generalizing init with
  | nil => simp [decodeTerms_nil]
  | cons t ts ih =>
    rw [List.foldl_cons, ih, decNat_gcdBits, ← natAbs_decInt, decodeTerms_cons, contentZ_cons,
      Nat.gcd_comm (decInt t.1).natAbs, Nat.gcd_assoc]

/-- `contentStr` on a framed list denotes the content of the decoded list. -/
private theorem decNat_contentStr_frameTerms (ts : List (List Bool × List Bool)) :
    decNat (contentStr (frameTerms ts)) = contentZ (decodeTerms ts) := by
  rw [contentStr, foldBlocks_frameTerms]
  simp only [coefZ_blk]
  rw [decNat_foldl_gcdStep, decNat_nil, Nat.gcd_zero_left]

theorem decNat_contentStr (l : ITerms) : decNat (contentStr (encITerms l)) = contentZ l := by
  rw [encITerms_eq_frameTerms, decNat_contentStr_frameTerms, decodeTerms_encPairs]

/-! ### Coefficient divisibility -/

/-- The divisibility flag is a flag. -/
private theorem dvdFlag_flag (c m : List Bool) : dvdFlag c m = [true] ∨ dvdFlag c m = [false] := by
  unfold dvdFlag
  rcases isZeroBits_flag c with h | h <;> rw [h, caseBit₀_cons]
  · exact isZeroBits_flag m
  · exact dvdBits_flag m c

/-- The divisibility flag denotes divisibility of the numerals (also for a zero divisor). -/
private theorem dvdFlag_eq_true_iff (c m : List Bool) :
    dvdFlag c m = [true] ↔ decNat c ∣ decNat m := by
  unfold dvdFlag
  rcases isZeroBits_flag c with h | h <;> rw [h, caseBit₀_cons]
  · rw [(isZeroBits_eq_true_iff c).1 h, Bool.cond_true, isZeroBits_eq_true_iff, zero_dvd_iff]
  · have hc : decNat c ≠ 0 := fun h0 ↦ by
      have := (isZeroBits_eq_true_iff c).2 h0
      rw [h] at this
      simp at this
    rw [Bool.cond_false, dvdBits_eq_true_iff _ _ hc]

/-- A left fold of `andBit` from a flag is a flag. -/
private theorem foldl_andBit_flag (g : List Bool → List Bool) :
    ∀ (bs : List (List Bool)) (init : List Bool), (init = [true] ∨ init = [false]) →
      (bs.foldl (fun acc b ↦ andBit acc (g b)) init = [true] ∨
        bs.foldl (fun acc b ↦ andBit acc (g b)) init = [false])
  | [], _, h => h
  | _ :: bs, _, _ => foldl_andBit_flag g bs _ (andBit_flag _ _)

/-- A left fold of `andBit` over flags is `[true]` iff all the flags are. -/
private theorem foldl_andBit_eq_true_iff (g : List Bool × List Bool → List Bool)
    (hg : ∀ t, g t = [true] ∨ g t = [false]) :
    ∀ (ts : List (List Bool × List Bool)) (init : List Bool), (init = [true] ∨ init = [false]) →
      (ts.foldl (fun acc t ↦ andBit acc (g t)) init = [true] ↔
        init = [true] ∧ ∀ t ∈ ts, g t = [true])
  | [], _, _ => by simp
  | t :: ts, init, hinit => by
    rw [List.foldl_cons, foldl_andBit_eq_true_iff g hg ts _ (andBit_flag _ _),
      Cobham.andBit_eq_true_iff hinit (hg t), List.forall_mem_cons]
    tauto

/-- `dvdAllStr` is a flag. -/
private theorem dvdAllStr_flag (c s : List Bool) :
    dvdAllStr c s = [true] ∨ dvdAllStr c s = [false] :=
  foldl_andBit_flag (fun b ↦ dvdFlag c (magOf (coefZ b))) (blocks s) [true] (Or.inl rfl)

/-- `dvdAllStr` on a framed list denotes `dvdAllZ` of the decoded list. -/
private theorem dvdAllStr_frameTerms_eq_true_iff (c : List Bool)
    (ts : List (List Bool × List Bool)) :
    dvdAllStr c (frameTerms ts) = [true] ↔ dvdAllZ (decNat c) (decodeTerms ts) = true := by
  rw [dvdAllStr, foldBlocks_frameTerms]
  simp only [coefZ_blk]
  rw [foldl_andBit_eq_true_iff (fun t ↦ dvdFlag c (magOf t.1)) (fun t ↦ dvdFlag_flag _ _) ts
    [true] (Or.inl rfl), dvdAllZ_iff_forall_mem]
  simp only [true_and, decodeTerms, List.forall_mem_map, dvdFlag_eq_true_iff, Int.natCast_dvd,
    natAbs_decInt]

theorem dvdAllStr_eq_true_iff (c : List Bool) (l : ITerms) :
    dvdAllStr c (encITerms l) = [true] ↔ dvdAllZ (decNat c) l = true := by
  rw [encITerms_eq_frameTerms, dvdAllStr_frameTerms_eq_true_iff, decodeTerms_encPairs]

/-! ### Division of the coefficients -/

/-- `divCoeffsStr` on a framed list divides the coefficient strings. -/
private theorem divCoeffsStr_frameTerms (c : List Bool) (ts : List (List Bool × List Bool)) :
    divCoeffsStr c (frameTerms ts) = frameTerms (ts.map fun t ↦ (divInt t.1 c, t.2)) := by
  rw [divCoeffsStr, mapBlocks_frameTerms]
  simp only [coefZ_blk, expZ_blk, frameTerms, List.map_map]
  rfl

private theorem decodeTerms_map_divInt (c : List Bool) (ts : List (List Bool × List Bool)) :
    decodeTerms (ts.map fun t ↦ (divInt t.1 c, t.2)) = divCoeffsZ (decNat c) (decodeTerms ts) := by
  simp [decodeTerms, divCoeffsZ, List.map_map, Function.comp_def, decInt_divInt]

theorem decITerms_divCoeffsStr (c : List Bool) (l : ITerms) :
    decITerms (divCoeffsStr c (encITerms l)) = some (divCoeffsZ (decNat c) l) := by
  rw [encITerms_eq_frameTerms, divCoeffsStr_frameTerms, decITerms_frameTerms,
    decodeTerms_map_divInt, decodeTerms_encPairs]

/-! ### The boundary decision -/

private theorem nonemptyFlag_frameTerms_cons (t : List Bool × List Bool)
    (ts : List (List Bool × List Bool)) : nonemptyFlag (frameTerms (t :: ts)) = [true] := by
  rw [frameTerms_cons]
  exact nonemptyFlag_of_ne_nil (pair_ne_nil _ _)

private theorem pairFst_frameTerms_cons (t : List Bool × List Bool)
    (ts : List (List Bool × List Bool)) : pairFst (frameTerms (t :: ts)) = blk t := by
  rw [frameTerms_cons, pairFst_pair]

private theorem pairSnd_frameTerms_cons (t : List Bool × List Bool)
    (ts : List (List Bool × List Bool)) : pairSnd (frameTerms (t :: ts)) = frameTerms ts := by
  rw [frameTerms_cons, pairSnd_pair]

/-- The flag "the remainder is empty", as a flag. -/
private theorem notBit_nonemptyFlag_frameTerms (ts : List (List Bool × List Bool)) :
    notBit (nonemptyFlag (frameTerms ts)) = if ts = [] then [true] else [false] := by
  cases ts with
  | nil => simp [frameTerms_nil, notBit]
  | cons t ts => simp [nonemptyFlag_frameTerms_cons, notBit]

/-- Divisibility by an integer is divisibility by its absolute value. -/
private theorem dvdAllZ_natAbs (c : ℤ) (l : ITerms) : dvdAllZ (c.natAbs : ℤ) l = dvdAllZ c l := by
  rw [Bool.eq_iff_iff, dvdAllZ_iff_forall_mem, dvdAllZ_iff_forall_mem]
  simp only [Int.natAbs_dvd]

theorem boundaryDecideStr_spec (f g : ITerms) :
    boundaryDecideStr (pair (encITerms g) (encITerms f)) =
      match boundaryDecide f g with
      | some true => [true]
      | some false => [false]
      | none => [] := by
  have hf : normalizeZ f = decodeTerms (normalizeS (encPairs f)) := by
    rw [decodeTerms_normalizeS_eq, decodeTerms_encPairs]
  have hg : normalizeZ g = decodeTerms (normalizeS (encPairs g)) := by
    rw [decodeTerms_normalizeS_eq, decodeTerms_encPairs]
  simp only [boundaryDecideStr, boundaryDecide, pairFst_pair, pairSnd_pair]
  rw [encITerms_eq_frameTerms, encITerms_eq_frameTerms, normalizeZStr_frameTerms,
    normalizeZStr_frameTerms, hf, hg]
  generalize normalizeS (encPairs f) = tf
  generalize normalizeS (encPairs g) = tg
  rcases tg with _ | ⟨⟨cg, eg⟩, rg⟩
  · rw [frameTerms_nil, nonemptyFlag_nil, caseBit₀_nil, decodeTerms_nil]
    rcases tf with _ | ⟨t, tf⟩
    · simp [frameTerms_nil, decodeTerms_nil]
    · rw [nonemptyFlag_frameTerms_cons, caseBit₀_cons, Bool.cond_true, decodeTerms_cons]
      simp
  · rw [nonemptyFlag_frameTerms_cons, caseBit₀_cons, Bool.cond_true, decodeTerms_cons]
    rcases tf with _ | ⟨t, tf⟩
    · simp [frameTerms_nil, decodeTerms_nil]
    · have hd : ltBits (degreeStr (frameTerms (t :: tf))) (degreeStr (frameTerms ((cg, eg) :: rg)))
          = [true] ↔ degreeZ (decodeTerms (t :: tf)) < degreeZ (decodeTerms ((cg, eg) :: rg)) := by
        rw [ltBits_eq_true_iff, decNat_degreeStr_frameTerms, decNat_degreeStr_frameTerms]
      have hdv : dvdAllStr (magOf cg) (frameTerms (t :: tf)) = [true] ↔
          dvdAllZ (decInt cg) (decodeTerms (t :: tf)) = true := by
        rw [dvdAllStr_frameTerms_eq_true_iff, ← natAbs_decInt, dvdAllZ_natAbs]
      have hcond : andBit (isZeroBits eg) (notBit (nonemptyFlag (frameTerms rg))) = [true] ↔
          decNat eg = 0 ∧ decodeTerms rg = [] := by
        rw [Cobham.andBit_eq_true_iff (isZeroBits_flag eg) (by
            rw [notBit_nonemptyFlag_frameTerms]; split_ifs <;> simp),
          isZeroBits_eq_true_iff, notBit_nonemptyFlag_frameTerms, decodeTerms_eq_nil_iff]
        split_ifs <;> simp_all
      rw [nonemptyFlag_frameTerms_cons, caseBit₀_cons, Bool.cond_true, pairFst_frameTerms_cons,
        pairSnd_frameTerms_cons, expZ_blk, coefZ_blk]
      simp only [decodeTerms_cons, List.cons_ne_nil, ite_false] at hd hdv ⊢
      by_cases hc : decNat eg = 0 ∧ decodeTerms rg = []
      · rw [hcond.2 hc, caseBit₀_cons, Bool.cond_true]
        rcases dvdAllStr_flag (magOf cg) (frameTerms (t :: tf)) with h | h
        · simp [h, hdv.1 h, hc, notBit]
        · have : dvdAllZ (decInt cg) ((decInt t.1, decNat t.2) :: decodeTerms tf) = false := by
            rw [Bool.eq_false_iff, ne_eq, ← hdv, h]
            simp
          simp [h, this, hc, notBit]
      · have hcf : andBit (isZeroBits eg) (notBit (nonemptyFlag (frameTerms rg))) = [false] := by
          rcases andBit_flag (isZeroBits eg) (notBit (nonemptyFlag (frameTerms rg))) with h | h
          · exact absurd (hcond.1 h) hc
          · exact h
        rw [hcf, caseBit₀_cons, Bool.cond_false]
        rcases ltBits_flag (degreeStr (frameTerms (t :: tf)))
          (degreeStr (frameTerms ((cg, eg) :: rg))) with h | h
        · simp [h, hd.1 h, hc]
        · have : ¬ degreeZ ((decInt t.1, decNat t.2) :: decodeTerms tf) <
              degreeZ ((decInt cg, decNat eg) :: decodeTerms rg) := fun hlt ↦ by
            have := hd.2 hlt
            rw [h] at this
            simp at this
          simp [h, this, hc]

/-! ## Polynomial-time computability

Cobham membership is assembled as in `BridgeString/Complexity.lean`: the loops are instances of
`cobham_mapBlocks` / `cobham_foldBlocks`, whose growth bounds must be uniform in the loop
parameters, so the parameters of the inner insertion fold are packed into the blocks. -/

/-! ### Elementary length facts -/

/-- `pairFst` consumes two input bits per output bit. -/
private theorem two_mul_length_pairFst_le : ∀ z : List Bool, 2 * (pairFst z).length ≤ z.length
  | [] => by simp [pairFst]
  | [b] => by cases b <;> simp [pairFst]
  | false :: false :: z => by
    have := two_mul_length_pairFst_le z
    simp [pairFst]
    omega
  | true :: true :: z => by
    have := two_mul_length_pairFst_le z
    simp [pairFst]
    omega
  | false :: true :: z => by simp [pairFst]
  | true :: false :: z => by simp [pairFst]

/-- The two components read by `pairFst`/`pairSnd` fit in the string (with the separator). -/
private theorem two_mul_length_pairFst_add_length_pairSnd_le (z : List Bool) :
    2 * (pairFst z).length + (pairSnd z).length ≤ z.length := by
  rcases hu : unpair? z with _ | ⟨x, y⟩
  · have h : pairSnd z = [] := by simp [pairSnd, hu]
    rw [h, List.length_nil, add_zero]
    exact two_mul_length_pairFst_le z
  · rw [eq_pair_of_unpair?_eq_some hu, pairFst_pair, pairSnd_pair, pair_length]
    omega

private theorem length_pairFst_le (z : List Bool) : (pairFst z).length ≤ z.length := by
  have := two_mul_length_pairFst_le z
  omega

private theorem length_coefZ_le (b : List Bool) : (coefZ b).length ≤ b.length :=
  length_pairFst_le b

private theorem length_expZ_le (b : List Bool) : (expZ b).length ≤ b.length :=
  pairSnd_length_le b

/-- The framed inserted term `(c, e)` (or nothing when `c = 0`). -/
private theorem length_insBlockZ_le (c e : List Bool) :
    (caseBit₀ (isZeroInt c) [] (delimit (pair c e))).length ≤
      4 * c.length + 2 * e.length + 6 := by
  refine caseBit₀_length_le_of (by simp) ?_
  rw [delimit_length, pair_length]
  omega

/-! ### Cobham membership of the pieces -/

private theorem cobham_delimit_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ delimit (g v) :=
  (cobham_pair_comp hg (Cobham.const [])).of_eq fun v ↦ by simp [pair]

private theorem cobham_coefZ_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ coefZ (g v) :=
  cobham_pairFst_comp hg

private theorem cobham_expZ_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ expZ (g v) :=
  cobham_pairSnd_comp hg

/-- `insertStepZ` as a Cobham function of Cobham arguments (parameters `c e`, state, block). -/
private theorem cobham_insertStepZ_comp {n : ℕ} {gc ge gst gb : (Fin n → List Bool) → List Bool}
    (hc : Cobham gc) (he : Cobham ge) (hst : Cobham gst) (hb : Cobham gb) :
    Cobham fun v : Fin n → List Bool ↦ insertStepZ (gc v) (ge v) (gst v) (gb v) := by
  have hins := cobham_pairFst_comp hst
  have hacc := cobham_pairSnd_comp hst
  have hc' := cobham_coefZ_comp hb
  have he' := cobham_expZ_comp hb
  have hdb := cobham_delimit_comp hb
  have hX := Cobham.iteFn (cobham_isZeroInt_comp hc) (Cobham.const [])
    (cobham_delimit_comp (cobham_pair_comp hc he))
  have hm := cobham_addInt_comp hc hc'
  have hY := Cobham.iteFn (cobham_isZeroInt_comp hm) (Cobham.const [])
    (cobham_delimit_comp (cobham_pair_comp hm he))
  exact Cobham.iteFn hins (cobham_pair_comp hins (Cobham.appendFn hacc hdb))
    (Cobham.iteFn (cobham_ltBits_comp he he')
      (cobham_pair_comp (Cobham.const [true]) (Cobham.appendFn (Cobham.appendFn hacc hX) hdb))
      (Cobham.iteFn (cobham_eqBits_comp he he')
        (cobham_pair_comp (Cobham.const [true]) (Cobham.appendFn hacc hY))
        (cobham_pair_comp (Cobham.const [false]) (Cobham.appendFn hacc hdb))))

/-! ### The insertion step: crude growth bound and packed form -/

/-- Crude growth of one insertion step, uniform in the state shape. -/
private theorem length_insertStepZ_le (c e st b : List Bool) :
    (insertStepZ c e st b).length ≤
      st.length + 4 * b.length + 4 * c.length + 2 * e.length + 34 := by
  have h1 := two_mul_length_pairFst_add_length_pairSnd_le st
  have h2 := pairSnd_length_le st
  have h3 := two_mul_length_pairFst_le b
  have h4 := length_insBlockZ_le c e
  have h5 := length_insBlockZ_le (addInt c (coefZ b)) e
  have h6 := length_addInt_le c (coefZ b)
  have h7 := length_coefZ_le b
  simp only [insertStepZ]
  refine caseBit₀_length_le_of ?_ (caseBit₀_length_le_of ?_ (caseBit₀_length_le_of ?_ ?_))
  · rw [pair_length, List.length_append, delimit_length]
    omega
  · rw [pair_length, List.length_append, List.length_append, delimit_length]
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [pair_length, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [pair_length, List.length_append, delimit_length]
    simp only [List.length_cons, List.length_nil]
    omega

/-- The insertion step reading its parameters from the packed block `pair b (pair c e)`. -/
private def insertStepZPacked (st b' : List Bool) : List Bool :=
  insertStepZ (pairFst (pairSnd b')) (pairSnd (pairSnd b')) st (pairFst b')

private theorem insertStepZPacked_pair (c e st b : List Bool) :
    insertStepZPacked st (pair b (pair c e)) = insertStepZ c e st b := by
  simp [insertStepZPacked]

private theorem length_insertStepZPacked_le (st b' : List Bool) :
    (insertStepZPacked st b').length ≤ st.length + 34 * (b'.length + 1) := by
  unfold insertStepZPacked
  refine (length_insertStepZ_le _ _ _ _).trans ?_
  have h1 := length_pairFst_le b'
  have h2 := pairSnd_length_le b'
  have h3 := length_pairFst_le (pairSnd b')
  have h4 := pairSnd_length_le (pairSnd b')
  omega

private theorem cobham_insertStepZPacked :
    Cobham fun w : Fin 2 → List Bool ↦ insertStepZPacked (w 0) (w 1) := by
  have h1 : Cobham fun w : Fin 2 → List Bool ↦ w 1 := Cobham.proj 1
  exact cobham_insertStepZ_comp (cobham_pairFst_comp (cobham_pairSnd_comp h1))
    (cobham_pairSnd_comp (cobham_pairSnd_comp h1)) (Cobham.proj 0) (cobham_pairFst_comp h1)

/-- The inner fold of `insertZStr` equals the packed fold over the packed blocks. -/
private theorem foldBlocks_insertStepZ_eq (c e init acc : List Bool) :
    foldBlocks (insertStepZ c e) init acc =
      foldBlocks insertStepZPacked init (mapBlocks (fun b ↦ pair b (pair c e)) acc) := by
  simp only [foldBlocks, mapBlocks, blocks_frame, List.foldl_map, insertStepZPacked_pair]

/-- The inner fold of `insertZStr` is Cobham in its parameters and the accumulator. -/
private theorem cobham_foldBlocks_insertStepZ_comp {n : ℕ}
    {gc ge gacc : (Fin n → List Bool) → List Bool}
    (hc : Cobham gc) (he : Cobham ge) (hacc : Cobham gacc) :
    Cobham fun v : Fin n → List Bool ↦
      foldBlocks (insertStepZ (gc v) (ge v)) (pair [false] []) (gacc v) := by
  have hpack : Cobham fun w : Fin 3 → List Bool ↦ pair (w 0) (pair (w 1) (w 2)) :=
    cobham_pair_comp (Cobham.proj 0) (cobham_pair_comp (Cobham.proj 1) (Cobham.proj 2))
  have hM : Cobham fun v : Fin 3 → List Bool ↦
      mapBlocks (fun b ↦ pair b (pair (v 1) (v 2))) (v 0) :=
    (cobham_mapBlocks (n := 2) hpack (2 * Polynomial.X + 6) fun w ↦ by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat, pair_length]
      simp
      omega).of_eq fun v ↦ rfl
  have hF : Cobham fun v : Fin 1 → List Bool ↦
      foldBlocks insertStepZPacked (pair [false] []) (v 0) :=
    (cobham_foldBlocks (n := 0) cobham_insertStepZPacked (init := fun _ ↦ pair [false] [])
      (Cobham.const _) 34 fun w ↦ length_insertStepZPacked_le (w 0) (w 1)).of_eq fun v ↦ rfl
  have hM' : Cobham fun v : Fin n → List Bool ↦
      mapBlocks (fun b ↦ pair b (pair (gc v) (ge v))) (gacc v) :=
    (Cobham.comp₃ hM hacc hc he).of_eq fun v ↦ by simp
  exact (Cobham.comp hF fun _ : Fin 1 ↦ hM').of_eq fun v ↦ (foldBlocks_insertStepZ_eq _ _ _ _).symm

/-- `insertZStr` as a Cobham function of Cobham arguments. -/
private theorem cobham_insertZStr_comp {n : ℕ} {gc ge gacc : (Fin n → List Bool) → List Bool}
    (hc : Cobham gc) (he : Cobham ge) (hacc : Cobham gacc) :
    Cobham fun v : Fin n → List Bool ↦ insertZStr (gc v) (ge v) (gacc v) := by
  have hr := cobham_foldBlocks_insertStepZ_comp hc he hacc
  have hX := Cobham.iteFn (cobham_isZeroInt_comp hc) (Cobham.const [])
    (cobham_delimit_comp (cobham_pair_comp hc he))
  exact Cobham.iteFn (cobham_pairFst_comp hr) (cobham_pairSnd_comp hr)
    (Cobham.appendFn (cobham_pairSnd_comp hr) hX)

/-! ### Length of one insertion -/

/-- The one-time budget of an insertion: the framed inserted term, or the growth of a merged
coefficient (`addInt` adds at most six bits to the two magnitudes). -/
private def insBudgetZ (c e : List Bool) : ℕ := 4 * c.length + 2 * e.length + 28

/-- The framed merged term replaces the framed block `b` (of length `≥ 4 |coefZ b| + 2`) at the
cost of the budget. -/
private theorem length_mergeBlockZ_le (c c' e : List Bool) :
    (caseBit₀ (isZeroInt (addInt c c')) [] (delimit (pair (addInt c c') e))).length ≤
      4 * c'.length + 2 + insBudgetZ c e := by
  refine (length_insBlockZ_le _ _).trans ?_
  have := length_addInt_le c c'
  unfold insBudgetZ
  omega

private theorem insertStepZ_pair_true (c e acc b : List Bool) :
    insertStepZ c e (pair [true] acc) b = pair [true] (acc ++ delimit b) := by
  simp [insertStepZ]

private theorem insertStepZ_pair_false (c e acc b : List Bool) :
    insertStepZ c e (pair [false] acc) b =
      caseBit₀ (ltBits e (expZ b))
        (pair [true] (acc ++ caseBit₀ (isZeroInt c) [] (delimit (pair c e)) ++ delimit b))
        (caseBit₀ (eqBits e (expZ b))
          (pair [true] (acc ++ caseBit₀ (isZeroInt (addInt c (coefZ b))) []
            (delimit (pair (addInt c (coefZ b)) e))))
          (pair [false] (acc ++ delimit b))) := by
  simp [insertStepZ]

/-- **Fold invariant of the insertion.** The state stays a flagged pair; the accumulator grows by
the framed processed blocks plus (once, when the flag flips) the insertion budget. -/
private theorem foldl_insertStepZ_length (c e : List Bool) :
    ∀ (bs : List (List Bool)) (i : Bool) (acc₀ : List Bool),
      ∃ (i' : Bool) (acc' : List Bool),
        bs.foldl (insertStepZ c e) (pair [i] acc₀) = pair [i'] acc' ∧
          acc'.length + (bif i' then 0 else insBudgetZ c e) ≤
            acc₀.length + (frame bs).length + (bif i then 0 else insBudgetZ c e)
  | [], i, acc₀ => ⟨i, acc₀, rfl, by simp [frame_nil]⟩
  | b :: bs, i, acc₀ => by
    rw [List.foldl_cons, frame_cons, List.length_append, delimit_length]
    cases i with
    | true =>
      rw [insertStepZ_pair_true]
      obtain ⟨i', acc', h1, h2⟩ := foldl_insertStepZ_length c e bs true (acc₀ ++ delimit b)
      refine ⟨i', acc', h1, ?_⟩
      rw [List.length_append, delimit_length] at h2
      simp only [Bool.cond_true] at h2 ⊢
      omega
    | false =>
      rw [insertStepZ_pair_false]
      have hX := length_insBlockZ_le c e
      have hY := length_mergeBlockZ_le c (coefZ b) e
      have hb : 2 * (coefZ b).length ≤ b.length := two_mul_length_pairFst_le b
      rcases ltBits_flag e (expZ b) with hlt | hlt <;> rw [hlt, caseBit₀_cons]
      · rw [Bool.cond_true]
        obtain ⟨i', acc', h1, h2⟩ := foldl_insertStepZ_length c e bs true
          (acc₀ ++ caseBit₀ (isZeroInt c) [] (delimit (pair c e)) ++ delimit b)
        refine ⟨i', acc', h1, ?_⟩
        rw [List.length_append, List.length_append, delimit_length] at h2
        simp only [Bool.cond_true, Bool.cond_false] at h2 ⊢
        unfold insBudgetZ at *
        omega
      · rw [Bool.cond_false]
        rcases eqBits_flag e (expZ b) with heq | heq <;> rw [heq, caseBit₀_cons]
        · rw [Bool.cond_true]
          obtain ⟨i', acc', h1, h2⟩ := foldl_insertStepZ_length c e bs true
            (acc₀ ++ caseBit₀ (isZeroInt (addInt c (coefZ b))) []
              (delimit (pair (addInt c (coefZ b)) e)))
          refine ⟨i', acc', h1, ?_⟩
          rw [List.length_append] at h2
          simp only [Bool.cond_true, Bool.cond_false] at h2 ⊢
          omega
        · rw [Bool.cond_false]
          obtain ⟨i', acc', h1, h2⟩ := foldl_insertStepZ_length c e bs false (acc₀ ++ delimit b)
          refine ⟨i', acc', h1, ?_⟩
          rw [List.length_append, delimit_length] at h2
          simp only [Bool.cond_false] at h2 ⊢
          omega

/-- **One insertion grows the accumulator by at most its budget.** -/
private theorem length_insertZStr_le (c e acc : List Bool) :
    (insertZStr c e acc).length ≤ acc.length + insBudgetZ c e := by
  have hX := length_insBlockZ_le c e
  obtain ⟨bs, rem, hs, hrem⟩ := exists_frame_append acc
  by_cases hne : rem = []
  · subst hne
    rw [List.append_nil] at hs
    subst hs
    obtain ⟨i', acc', h1, h2⟩ := foldl_insertStepZ_length c e bs false []
    simp only [insertZStr, foldBlocks, blocks_frame, h1, pairFst_pair, pairSnd_pair, caseBit₀_cons,
      List.length_nil, zero_add, Bool.cond_false] at h2 ⊢
    cases i'
    · simp only [Bool.cond_false, List.length_append] at h2 ⊢
      unfold insBudgetZ at *
      omega
    · simp only [Bool.cond_true] at h2 ⊢
      omega
  · have hbad := hrem.resolve_left hne
    have hb : blocks acc = [] := by
      rw [hs]
      exact blocks_frame_append_of_bad bs hne hbad
    simp only [insertZStr, foldBlocks, hb, List.foldl_nil, pairFst_pair, pairSnd_pair,
      caseBit₀_cons, Bool.cond_false, List.nil_append]
    unfold insBudgetZ at *
    omega

/-! ### `normalizeZStr` -/

private theorem length_normStepZ_le (acc b : List Bool) :
    (insertZStr (coefZ b) (expZ b) acc).length ≤ acc.length + 28 * (b.length + 1) := by
  refine (length_insertZStr_le _ _ _).trans ?_
  unfold insBudgetZ
  have h1 : 2 * (coefZ b).length + (expZ b).length ≤ b.length :=
    two_mul_length_pairFst_add_length_pairSnd_le b
  omega

private theorem cobham_normStepZ :
    Cobham fun w : Fin 2 → List Bool ↦ insertZStr (coefZ (w 1)) (expZ (w 1)) (w 0) :=
  cobham_insertZStr_comp (cobham_coefZ_comp (Cobham.proj 1)) (cobham_expZ_comp (Cobham.proj 1))
    (Cobham.proj 0)

/-- `normalizeZStr` as a Cobham function of a Cobham argument. -/
private theorem cobham_normalizeZStr_comp {n : ℕ} {gs : (Fin n → List Bool) → List Bool}
    (hs : Cobham gs) : Cobham fun v : Fin n → List Bool ↦ normalizeZStr (gs v) := by
  have hF : Cobham fun v : Fin 1 → List Bool ↦ normalizeZStr (v 0) :=
    (cobham_foldBlocks (n := 0) cobham_normStepZ (init := fun _ ↦ []) Cobham.empty 28
      fun w ↦ length_normStepZ_le (w 0) (w 1)).of_eq fun v ↦ rfl
  exact (Cobham.comp hF fun _ : Fin 1 ↦ hs).of_eq fun v ↦ rfl

theorem normalizeZStr_mem_FP : normalizeZStr ∈ FP := by
  refine CobhamFP_subset_FP ?_
  show Cobham fun v : Fin 1 → List Bool ↦ normalizeZStr (v 0)
  exact cobham_normalizeZStr_comp (Cobham.proj 0)

/-! ### `degreeStr` -/

/-- `degreeStr` as a Cobham function of a Cobham argument. -/
private theorem cobham_degreeStr_comp {n : ℕ} {gs : (Fin n → List Bool) → List Bool}
    (hs : Cobham gs) : Cobham fun v : Fin n → List Bool ↦ degreeStr (gs v) := by
  have hstep : Cobham fun w : Fin 2 → List Bool ↦
      caseBit₀ (ltBits (w 0) (expZ (w 1))) (expZ (w 1)) (w 0) :=
    Cobham.iteFn (cobham_ltBits_comp (Cobham.proj 0) (cobham_expZ_comp (Cobham.proj 1)))
      (cobham_expZ_comp (Cobham.proj 1)) (Cobham.proj 0)
  have hgrow : ∀ w : Fin 2 → List Bool,
      (caseBit₀ (ltBits (w 0) (expZ (w 1))) (expZ (w 1)) (w 0)).length ≤
        (w 0).length + 1 * ((w 1).length + 1) := by
    intro w
    have := length_expZ_le (w 1)
    exact caseBit₀_length_le_of (by omega) (by omega)
  have hF : Cobham fun v : Fin 1 → List Bool ↦ degreeStr (v 0) :=
    (cobham_foldBlocks (n := 0) hstep (init := fun _ ↦ []) Cobham.empty 1 hgrow).of_eq
      fun v ↦ rfl
  exact (Cobham.comp hF fun _ : Fin 1 ↦ hs).of_eq fun v ↦ rfl

theorem degreeStr_mem_FP : degreeStr ∈ FP := by
  refine CobhamFP_subset_FP ?_
  show Cobham fun v : Fin 1 → List Bool ↦ degreeStr (v 0)
  exact cobham_degreeStr_comp (Cobham.proj 0)

/-! ### `contentStr` -/

/-- `contentStr` as a Cobham function of a Cobham argument. -/
private theorem cobham_contentStr_comp {n : ℕ} {gs : (Fin n → List Bool) → List Bool}
    (hs : Cobham gs) : Cobham fun v : Fin n → List Bool ↦ contentStr (gs v) := by
  have hstep : Cobham fun w : Fin 2 → List Bool ↦ gcdBits (magOf (coefZ (w 1))) (w 0) :=
    cobham_gcdBits_comp (cobham_magOf_comp (cobham_coefZ_comp (Cobham.proj 1))) (Cobham.proj 0)
  have hgrow : ∀ w : Fin 2 → List Bool,
      (gcdBits (magOf (coefZ (w 1))) (w 0)).length ≤ (w 0).length + 2 * ((w 1).length + 1) := by
    intro w
    have h1 := length_gcdBits_le (magOf (coefZ (w 1))) (w 0)
    have h2 := length_magOf_le (coefZ (w 1))
    have h3 := length_coefZ_le (w 1)
    omega
  have hF : Cobham fun v : Fin 1 → List Bool ↦ contentStr (v 0) :=
    (cobham_foldBlocks (n := 0) hstep (init := fun _ ↦ []) Cobham.empty 2 hgrow).of_eq
      fun v ↦ rfl
  exact (Cobham.comp hF fun _ : Fin 1 ↦ hs).of_eq fun v ↦ rfl

theorem contentStr_mem_FP : contentStr ∈ FP := by
  refine CobhamFP_subset_FP ?_
  show Cobham fun v : Fin 1 → List Bool ↦ contentStr (v 0)
  exact cobham_contentStr_comp (Cobham.proj 0)

/-! ### `dvdAllStr` -/

private theorem cobham_dvdFlag_comp {n : ℕ} {gc gm : (Fin n → List Bool) → List Bool}
    (hc : Cobham gc) (hm : Cobham gm) :
    Cobham fun v : Fin n → List Bool ↦ dvdFlag (gc v) (gm v) :=
  Cobham.iteFn (cobham_isZeroBits_comp hc) (cobham_isZeroBits_comp hm)
    (cobham_dvdBits_comp hm hc)

/-- `dvdAllStr` as a Cobham function of Cobham arguments. -/
private theorem cobham_dvdAllStr_comp {n : ℕ} {gc gs : (Fin n → List Bool) → List Bool}
    (hc : Cobham gc) (hs : Cobham gs) :
    Cobham fun v : Fin n → List Bool ↦ dvdAllStr (gc v) (gs v) := by
  have hstep : Cobham fun w : Fin 3 → List Bool ↦
      andBit (w 0) (dvdFlag (w 2) (magOf (coefZ (w 1)))) :=
    Cobham.andFn (Cobham.proj 0)
      (cobham_dvdFlag_comp (Cobham.proj 2) (cobham_magOf_comp (cobham_coefZ_comp (Cobham.proj 1))))
  have hgrow : ∀ w : Fin 3 → List Bool,
      (andBit (w 0) (dvdFlag (w 2) (magOf (coefZ (w 1))))).length ≤
        (w 0).length + 1 * ((w 1).length + 1) := by
    intro w
    rcases andBit_flag (w 0) (dvdFlag (w 2) (magOf (coefZ (w 1)))) with h | h <;> rw [h] <;>
      simp only [List.length_singleton] <;> omega
  have hF : Cobham fun v : Fin 2 → List Bool ↦ dvdAllStr (v 1) (v 0) :=
    (cobham_foldBlocks (n := 1) hstep (init := fun _ ↦ [true]) (Cobham.const _) 1 hgrow).of_eq
      fun v ↦ rfl
  exact (Cobham.comp₂ hF hs hc).of_eq fun v ↦ by simp

theorem dvdAllStr_mem_FP : (fun z ↦ dvdAllStr (pairFst z) (pairSnd z)) ∈ FP := by
  refine CobhamFP_subset_FP ?_
  show Cobham fun v : Fin 1 → List Bool ↦ dvdAllStr (pairFst (v 0)) (pairSnd (v 0))
  exact cobham_dvdAllStr_comp (cobham_pairFst_comp (Cobham.proj 0))
    (cobham_pairSnd_comp (Cobham.proj 0))

/-! ### `divCoeffsStr` -/

/-- `divCoeffsStr` as a Cobham function of Cobham arguments. -/
private theorem cobham_divCoeffsStr_comp {n : ℕ} {gc gs : (Fin n → List Bool) → List Bool}
    (hc : Cobham gc) (hs : Cobham gs) :
    Cobham fun v : Fin n → List Bool ↦ divCoeffsStr (gc v) (gs v) := by
  have hf : Cobham fun w : Fin 2 → List Bool ↦ pair (divInt (coefZ (w 0)) (w 1)) (expZ (w 0)) :=
    cobham_pair_comp (cobham_divInt_comp (cobham_coefZ_comp (Cobham.proj 0)) (Cobham.proj 1))
      (cobham_expZ_comp (Cobham.proj 0))
  have hM : Cobham fun v : Fin 2 → List Bool ↦
      mapBlocks (fun b ↦ pair (divInt (coefZ b) (v 1)) (expZ b)) (v 0) :=
    (cobham_mapBlocks (n := 1) hf (3 * Polynomial.X + 16) fun w ↦ by
      rw [Fin.sum_univ_two]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat, pair_length]
      have h1 := length_divInt_le (coefZ (w 0)) (w 1)
      have h2 := length_expZ_le (w 0)
      have h3 := length_coefZ_le (w 0)
      omega).of_eq fun v ↦ rfl
  exact (Cobham.comp₂ hM hs hc).of_eq fun v ↦ by simp [divCoeffsStr]

theorem divCoeffsStr_mem_FP : (fun z ↦ divCoeffsStr (pairFst z) (pairSnd z)) ∈ FP := by
  refine CobhamFP_subset_FP ?_
  show Cobham fun v : Fin 1 → List Bool ↦ divCoeffsStr (pairFst (v 0)) (pairSnd (v 0))
  exact cobham_divCoeffsStr_comp (cobham_pairFst_comp (Cobham.proj 0))
    (cobham_pairSnd_comp (Cobham.proj 0))

/-! ### `boundaryDecideStr` -/

theorem boundaryDecideStr_mem_FP : boundaryDecideStr ∈ FP := by
  refine CobhamFP_subset_FP ?_
  show Cobham fun v : Fin 1 → List Bool ↦ boundaryDecideStr (v 0)
  have hs : Cobham fun v : Fin 1 → List Bool ↦ v 0 := Cobham.proj 0
  have hg := cobham_normalizeZStr_comp (cobham_pairFst_comp hs)
  have hf := cobham_normalizeZStr_comp (cobham_pairSnd_comp hs)
  have hng := Cobham.nonemptyFn hg
  have hnf := Cobham.nonemptyFn hf
  have hg1 := cobham_pairFst_comp hg
  exact Cobham.iteFn hng
    (Cobham.iteFn hnf
      (Cobham.iteFn
        (Cobham.andFn (cobham_isZeroBits_comp (cobham_expZ_comp hg1))
          (Cobham.notFn (Cobham.nonemptyFn (cobham_pairSnd_comp hg))))
        (Cobham.notFn (cobham_dvdAllStr_comp (cobham_magOf_comp (cobham_coefZ_comp hg1)) hf))
        (Cobham.iteFn (cobham_ltBits_comp (cobham_degreeStr_comp hf) (cobham_degreeStr_comp hg))
          (Cobham.const [true]) (Cobham.const [])))
      (Cobham.const [false]))
    (Cobham.iteFn hnf (Cobham.const [true]) (Cobham.const [false]))

end SparseDiv.Appendix
