import SparseIrred.Machine.DataCorrect

/-!
# Size bounds for the data-level algorithm

The notes (p. 7, "polynomial sparse-bit cost"): "Let `Q = max_i q_i`.  Each `C_j` expands from at
most `Q³` raw terms, so `S` from at most `s Q⁶` raw terms, each exponent of `S` has absolute value
less than `3N`, and each coefficient has absolute value at most `s Q⁶`.  Consequently `A` and the
numerical sum of its squared coefficients have polynomial size in the formula length."

The consequence used by the string implementation is `twenty_mul_wD_succ_le`: the number
`20 (w + 1)`, which the implementation converts from binary to unary in order to write
`2^{20(w+1)}` in binary, is at most `wBound |x|`, an explicit polynomial in the input length.  The
chain is

  `#S_raw ≤ s·Q⁶` (`length_sRawD_le`), `Q ≤ 64 (n+1)²` (`Qmax_oddPrimeList_le`),
  `n ≤ |x| + 1`, `s ≤ |x|`, raw coefficients are `±1` (`unitCoeffs_sRawD`),
  `∑|c|` does not grow under `normalizeZ` (`absSum_normalizeZ_le`),
  `w = 4 + 9 ∑ c² + #A ≤ 4 + 9 R² + R` with `R = #S_raw` and `c` ranging over the coefficients
  of `S` (`wD_hmA_le`).

Each size claim of the notes has a counterpart: `length_clauseTermsD_le_cube` (`Q³`),
`length_sRawD_le` (`s Q⁶`), `natAbs_coeff_Spoly_le` (coefficients of `S` at most `s Q⁶`),
`Dexp_lt_three_mul_bigN` (exponents of `S` below `3N`) and `wParam_le_wBound` (`w` polynomial in
the input length).
-/

open Polynomial LaurentPolynomial Complexity.SAT SparseDiv.Appendix

namespace SparseIrred.Machine

open SparseIrred

/-! ### `Q` and raw term counts -/

/-- `Q = max_i q_i` (with floor `2`, so that `#P⁺ = 2 ≤ Q`). -/
def Qmax (qs : List ℕ) : ℕ := qs.foldr max 2

theorem two_le_Qmax (qs : List ℕ) : 2 ≤ Qmax qs := by
  induction qs with
  | nil => simp [Qmax]
  | cons q qs ih =>
    simp only [Qmax, List.foldr_cons] at *
    omega

theorem getD_le_Qmax (qs : List ℕ) (i : ℕ) : qs.getD i 0 ≤ Qmax qs := by
  induction qs generalizing i with
  | nil => simp
  | cons q qs ih =>
    have h := two_le_Qmax qs
    cases i with
    | zero => simp [Qmax]
    | succ i =>
      have := ih i
      simp only [List.getD_cons_succ, Qmax, List.foldr_cons] at *
      omega

theorem length_litTermsD_le (qs : List ℕ) (N : ℕ) (l : Lit) :
    (litTermsD qs N l).length ≤ Qmax qs := by
  unfold litTermsD
  split
  · simpa [posLitTerms] using two_le_Qmax qs
  · simpa [negLitTerms] using getD_le_Qmax qs l.var

/-- Each `C_j` has at most `Q^{|c|}` raw terms. -/
theorem length_clauseTermsD_le (qs : List ℕ) (N : ℕ) (c : Clause) :
    (clauseTermsD qs N c).length ≤ Qmax qs ^ c.length := by
  induction c with
  | nil => simp [clauseTermsD]
  | cons l c ih =>
    rw [clauseTermsD, List.foldr_cons, ← clauseTermsD, length_mulITerms, List.length_cons, pow_succ,
      mul_comm (Qmax qs ^ c.length)]
    exact Nat.mul_le_mul (length_litTermsD_le qs N l) ih

/-- Notes: each `C_j` expands from at most `Q³` raw terms. -/
theorem length_clauseTermsD_le_cube (qs : List ℕ) (N : ℕ) {c : Clause} (hc : c.length ≤ 3) :
    (clauseTermsD qs N c).length ≤ Qmax qs ^ 3 := by
  exact (length_clauseTermsD_le qs N c).trans
    (Nat.pow_le_pow_right (by have := two_le_Qmax qs; omega) hc)

theorem length_sRawD (K : ℕ) (Cs : List ITerms) :
    (sRawD K Cs).length = (Cs.map fun C => C.length ^ 2).sum := by
  induction Cs with
  | nil => simp [sRawD]
  | cons C Cs ih =>
    rw [sRawD, List.flatMap_cons, List.length_append, length_mulITerms, length_reflectITerms,
      ← sRawD, ih, List.map_cons, List.sum_cons]
    ring

/-- Notes: `S` expands from at most `s Q⁶` raw terms. -/
theorem length_sRawD_le (qs : List ℕ) (Ψ : CNF) (K : ℕ) (h3 : ∀ c ∈ Ψ, c.length ≤ 3) :
    (sRawD K (clauseListD qs Ψ)).length ≤ Ψ.length * Qmax qs ^ 6 := by
  rw [length_sRawD, clauseListD]
  induction Ψ with
  | nil => simp
  | cons c Ψ ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.length_cons]
    have h1 : (clauseTermsD qs qs.prod c).length ≤ Qmax qs ^ 3 :=
      length_clauseTermsD_le_cube qs qs.prod (h3 c List.mem_cons_self)
    have h2 : (clauseTermsD qs qs.prod c).length ^ 2 ≤ Qmax qs ^ 6 := by
      calc (clauseTermsD qs qs.prod c).length ^ 2 ≤ (Qmax qs ^ 3) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = Qmax qs ^ 6 := by rw [← pow_mul]
    have h4 := ih fun c hc => h3 c (List.mem_cons_of_mem _ hc)
    rw [Nat.succ_mul]
    omega

/-! ### Coefficient sizes -/

/-- All coefficients are `±1`. -/
def UnitCoeffs (l : ITerms) : Prop := ∀ t ∈ l, t.1.natAbs = 1

/-- `∑ |c|` over a term list. -/
def absSum (l : ITerms) : ℕ := (l.map fun t => t.1.natAbs).sum

theorem unitCoeffs_litTermsD (qs : List ℕ) (N : ℕ) (l : Lit) : UnitCoeffs (litTermsD qs N l) := by
  unfold litTermsD
  split
  · intro t ht
    simp only [posLitTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> rfl
  · intro t ht
    simp only [negLitTerms, List.mem_map] at ht
    obtain ⟨r, -, rfl⟩ := ht
    rfl

theorem unitCoeffs_mulITerms {l₁ l₂ : ITerms} (h₁ : UnitCoeffs l₁) (h₂ : UnitCoeffs l₂) :
    UnitCoeffs (mulITerms l₁ l₂) := by
  intro t ht
  simp only [mulITerms, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  simp [Int.natAbs_mul, h₁ a ha, h₂ b hb]

theorem unitCoeffs_clauseTermsD (qs : List ℕ) (N : ℕ) (c : Clause) :
    UnitCoeffs (clauseTermsD qs N c) := by
  induction c with
  | nil =>
    intro t ht
    simp only [clauseTermsD, List.foldr_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
    rw [ht]
    rfl
  | cons l c ih =>
    rw [clauseTermsD, List.foldr_cons, ← clauseTermsD]
    exact unitCoeffs_mulITerms (unitCoeffs_litTermsD qs N l) ih

theorem unitCoeffs_sRawD (qs : List ℕ) (Ψ : CNF) (K : ℕ) :
    UnitCoeffs (sRawD K (clauseListD qs Ψ)) := by
  intro t ht
  simp only [sRawD, clauseListD, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨C, ⟨c, -, rfl⟩, ht⟩ := ht
  refine unitCoeffs_mulITerms (unitCoeffs_clauseTermsD qs qs.prod c) ?_ t ht
  intro u hu
  simp only [reflectITerms, List.mem_map] at hu
  obtain ⟨u', hu', rfl⟩ := hu
  exact unitCoeffs_clauseTermsD qs qs.prod c u' hu'

theorem absSum_of_unitCoeffs {l : ITerms} (h : UnitCoeffs l) : absSum l = l.length := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [absSum, List.map_cons, List.sum_cons] at *
    rw [h t List.mem_cons_self, ih fun u hu => h u (List.mem_cons_of_mem _ hu), List.length_cons]
    ring

theorem absSum_cons (t : ℤ × ℕ) (l : ITerms) : absSum (t :: l) = t.1.natAbs + absSum l := by
  simp [absSum]

theorem absSum_insertTermZ_le (c : ℤ) (e : ℕ) (l : ITerms) :
    absSum (insertTermZ c e l) ≤ c.natAbs + absSum l := by
  induction l with
  | nil =>
    simp only [insertTermZ]
    split_ifs <;> simp [absSum]
  | cons t rest ih =>
    obtain ⟨c', e'⟩ := t
    simp only [insertTermZ]
    split_ifs with h1 h2 h3 h4
    · simp [absSum_cons]
    · simp [absSum_cons]
    · simp only [absSum_cons]
      omega
    · simp only [absSum_cons]
      have := Int.natAbs_add_le c c'
      omega
    · simp only [absSum_cons]
      omega

/-- Collecting like terms does not increase `∑ |c|` (triangle inequality). -/
theorem absSum_normalizeZ_le (l : ITerms) : absSum (normalizeZ l) ≤ absSum l := by
  induction l with
  | nil => simp [normalizeZ]
  | cons t l ih =>
    obtain ⟨c, e⟩ := t
    simp only [normalizeZ]
    have := absSum_insertTermZ_le c e (normalizeZ l)
    rw [absSum_cons]
    omega

theorem natAbs_coeff_toPolyZ_le (l : ITerms) (j : ℕ) :
    ((toPolyZ l).coeff j).natAbs ≤ absSum l := by
  induction l with
  | nil => simp [absSum]
  | cons t l ih =>
    rw [toPolyZ_cons, coeff_add, coeff_C_mul, coeff_X_pow, absSum_cons]
    have := Int.natAbs_add_le (t.1 * if j = t.2 then 1 else 0) ((toPolyZ l).coeff j)
    have h2 : (t.1 * if j = t.2 then 1 else 0).natAbs ≤ t.1.natAbs := by
      split_ifs <;> simp
    omega

theorem sqSumD_le (l : ITerms) : sqSumD l ≤ absSum l ^ 2 := by
  induction l with
  | nil => simp [sqSumD, absSum]
  | cons t l ih =>
    simp only [sqSumD, absSum, List.map_cons, List.sum_cons] at *
    have e : (t.1.natAbs + (l.map fun t => t.1.natAbs).sum) ^ 2 =
        t.1.natAbs ^ 2 + 2 * (t.1.natAbs * (l.map fun t => t.1.natAbs).sum) +
          (l.map fun t => t.1.natAbs).sum ^ 2 := by
      ring
    rw [e]
    omega

theorem sqSumD_aTermsD (s : ITerms) : sqSumD (aTermsD s) = 9 * sqSumD s := by
  unfold aTermsD
  generalize headExpD s = h
  induction s with
  | nil => simp [sqSumD]
  | cons t s ih =>
    simp only [sqSumD, List.map_cons, List.sum_cons] at *
    rw [ih, Int.natAbs_mul]
    simp only [Int.reduceAbs]
    ring

theorem length_aTermsD (s : ITerms) : (aTermsD s).length = s.length := by
  simp [aTermsD]

/-- `w ≤ 4 + 9 R² + R` with `R = s Q⁶` (a bound on the number of raw terms of `S`). -/
theorem wD_hmA_le (qs : List ℕ) (Ψ : CNF) (h3 : ∀ c ∈ Ψ, c.length ≤ 3) :
    wD (hmA qs Ψ) ≤ 4 + 9 * (Ψ.length * Qmax qs ^ 6) ^ 2 + Ψ.length * Qmax qs ^ 6 := by
  have hR := length_sRawD_le qs Ψ (offsetD (clauseListD qs Ψ)) h3
  set raw := sRawD (offsetD (clauseListD qs Ψ)) (clauseListD qs Ψ) with hraw
  have hab : absSum (normalizeZ raw) ≤ raw.length :=
    (absSum_normalizeZ_le raw).trans (absSum_of_unitCoeffs (unitCoeffs_sRawD qs Ψ _)).le
  have hsq : sqSumD (normalizeZ raw) ≤ raw.length ^ 2 :=
    (sqSumD_le _).trans (Nat.pow_le_pow_left hab 2)
  have hlen : (normalizeZ raw).length ≤ raw.length := length_normalizeZ_le raw
  have hR2 : raw.length ^ 2 ≤ (Ψ.length * Qmax qs ^ 6) ^ 2 := Nat.pow_le_pow_left hR 2
  have e : hmA qs Ψ = aTermsD (normalizeZ raw) := rfl
  rw [e, wD, sqSumD_aTermsD, length_aTermsD]
  omega

/-! ### In terms of the input length -/

theorem Qmax_le {qs : List ℕ} {B : ℕ} (h2 : 2 ≤ B) (h : ∀ q ∈ qs, q ≤ B) : Qmax qs ≤ B := by
  induction qs with
  | nil => simpa [Qmax] using h2
  | cons q qs ih =>
    have h1 := h q List.mem_cons_self
    have h3 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [Qmax, List.foldr_cons] at *
    omega

/-- `Q ≤ 64 (n+1)²` for the first `n` odd primes. -/
theorem Qmax_oddPrimeList_le (n : ℕ) : Qmax (oddPrimeList n) ≤ 64 * (n + 1) ^ 2 := by
  refine Qmax_le (by have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega) fun q hq => ?_
  simp only [oddPrimeList, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  have h1 := oddPrime_le i
  have h2 : (i + 2) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem length_le_encode_length (Φ : CNF) : Φ.length ≤ Φ.encode.length := by
  induction Φ with
  | nil => simp
  | cons c Φ ih =>
    simp only [CNF.encode, List.length_append, List.length_cons, List.length_nil]
    omega

/-- The bound on the number of raw terms of `S`, as a polynomial in the input length `L`. -/
def rawBound (L : ℕ) : ℕ := L * (64 * (L + 2) ^ 2) ^ 6

/-- The length of the unary ruler used to convert `20 (w+1)` to unary, a polynomial in the input
length `L`. -/
def wBound (L : ℕ) : ℕ := 20 * (5 + 9 * rawBound L ^ 2 + rawBound L)

/-- The notes' bound `s Q⁶` on the number of raw terms of `S` is at most `rawBound` of the input
length. -/
theorem length_mul_Qmax_pow_six_le_rawBound (Φ : CNF) :
    Φ.length * Qmax (oddPrimeList (numVars Φ)) ^ 6 ≤ rawBound Φ.encode.length := by
  have hQ := Qmax_oddPrimeList_le (numVars Φ)
  have hn := numVars_le_encode_length Φ
  unfold rawBound
  refine Nat.mul_le_mul (length_le_encode_length Φ) (Nat.pow_le_pow_left (hQ.trans ?_) 6)
  have : (numVars Φ + 1) ^ 2 ≤ (Φ.encode.length + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

/-- The number of raw terms of `X^K S` is at most `rawBound` of the input length. -/
theorem length_sRawD_encode_le (Φ : CNF) (h3 : Φ.Is3CNF) (K : ℕ) :
    (sRawD K (clauseListD (oddPrimeList (numVars Φ)) (renumber Φ))).length ≤
      rawBound Φ.encode.length := by
  have h3' : ∀ c ∈ renumber Φ, c.length ≤ 3 := clause_length_le_of_is3CNF (is3CNF_renumber h3)
  have hR := length_sRawD_le (oddPrimeList (numVars Φ)) (renumber Φ) K h3'
  rw [length_renumber] at hR
  exact hR.trans (length_mul_Qmax_pow_six_le_rawBound Φ)

/-- **`20 (w + 1)` is polynomially bounded in the input length** (data level). -/
theorem twenty_mul_wD_succ_le (Φ : CNF) (h3 : Φ.Is3CNF) :
    20 * (wD (hmA (oddPrimeList (numVars Φ)) (renumber Φ)) + 1) ≤ wBound Φ.encode.length := by
  have h3' : ∀ c ∈ renumber Φ, c.length ≤ 3 := clause_length_le_of_is3CNF (is3CNF_renumber h3)
  have hw := wD_hmA_le (oddPrimeList (numVars Φ)) (renumber Φ) h3'
  rw [length_renumber] at hw
  have hR := length_mul_Qmax_pow_six_le_rawBound Φ
  have hR2 := Nat.pow_le_pow_left hR 2
  unfold wBound
  omega

/-! ### The size claims of the notes in the notes' notation -/

/-- The notes' `Q = max_i q_i` (floor `2`). -/
noncomputable def Qnotes (Φ : CNF) : ℕ := Qmax (oddPrimeList (numVars Φ))

theorem Qnotes_le (Φ : CNF) : Qnotes Φ ≤ 64 * (numVars Φ + 1) ^ 2 :=
  Qmax_oddPrimeList_le _

/-- The notes' `w` is polynomially bounded in the input length. -/
theorem wParam_le_wBound (Φ : CNF) (h3 : Φ.Is3CNF) (hΦ : Φ ≠ []) :
    20 * (wParam Φ + 1) ≤ wBound Φ.encode.length := by
  rw [wParam_eq Φ hΦ]
  exact twenty_mul_wD_succ_le Φ h3

/-- Each coefficient of `S` has absolute value at most `s Q⁶`. -/
theorem natAbs_coeff_Spoly_le (Φ : CNF) (h3 : ∀ c ∈ Φ, c.length ≤ 3) (e : ℤ) :
    ((Spoly Φ).coeff e).natAbs ≤ Φ.length * Qnotes Φ ^ 6 := by
  set K := offsetD (clauseListD (oddPrimeList (numVars Φ)) (renumber Φ)) with hK
  set raw := sRawD K (clauseListD (oddPrimeList (numVars Φ)) (renumber Φ)) with hraw
  have hL := toLaurent_toPolyZ_sNormD Φ
  have hS : (Spoly Φ).coeff e = (toLaurent (toPolyZ (normalizeZ raw))).coeff (e + K) := by
    have : sNormD (oddPrimeList (numVars Φ)) (renumber Φ) = normalizeZ raw := rfl
    rw [← this, hL, coeff_T_mul, add_sub_cancel_right]
  have h3' : ∀ c ∈ renumber Φ, c.length ≤ 3 := by
    intro c hc
    rw [renumber, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    rw [List.length_map]
    exact h3 c' hc'
  have hR := length_sRawD_le (oddPrimeList (numVars Φ)) (renumber Φ) K h3'
  rw [length_renumber, ← hraw] at hR
  have hab : absSum (normalizeZ raw) ≤ raw.length :=
    (absSum_normalizeZ_le raw).trans (absSum_of_unitCoeffs (unitCoeffs_sRawD _ _ _)).le
  rw [hS]
  by_cases he : 0 ≤ e + K
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = e + K := ⟨(e + K).toNat, Int.toNat_of_nonneg he⟩
    rw [← hj, coeff_toLaurent_natCast]
    exact (natAbs_coeff_toPolyZ_le _ j).trans (hab.trans hR)
  · rw [coeff_toLaurent_of_neg _ (by omega)]
    simp

theorem exists_of_mem_mulITerms {l₁ l₂ : ITerms} {t : ℤ × ℕ} (ht : t ∈ mulITerms l₁ l₂) :
    ∃ a ∈ l₁, ∃ b ∈ l₂, t.2 = a.2 + b.2 := by
  simp only [mulITerms, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  exact ⟨a, ha, b, hb, rfl⟩

/-- Every raw exponent of a literal of `Φ` is `≤ N - 1`. -/
theorem snd_le_of_mem_litTermsD (Φ : CNF) {l : Lit} (hl : Occurs Φ l.var) {t : ℤ × ℕ}
    (ht : t ∈ litTermsD (oddPrimeList (numVars Φ)) (bigN Φ) (renumLit Φ l)) :
    t.2 ≤ bigN Φ - 1 := by
  have hi := varIdx_lt_numVars Φ hl
  have hq := three_le_oddPrime (varIdx Φ l.var)
  have hmq := mExp_mul_oddPrime Φ hi
  have hN := bigN_pos Φ
  unfold litTermsD renumLit at ht
  simp only [getD_oddPrimeList hi] at ht
  have hm : bigN Φ / oddPrime (varIdx Φ l.var) = mExp Φ (varIdx Φ l.var) := rfl
  rw [hm] at ht
  set m := mExp Φ (varIdx Φ l.var)
  set q := oddPrime (varIdx Φ l.var)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, zero_mul] at hmq
      omega
    · exact h0
  split_ifs at ht
  · simp only [posLitTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp
    · show m ≤ bigN Φ - 1
      have : m * 3 ≤ m * q := Nat.mul_le_mul_left m hq
      omega
  · simp only [negLitTerms, List.mem_map, List.mem_range] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    show r * m ≤ bigN Φ - 1
    have : r * m ≤ (q - 1) * m := Nat.mul_le_mul_right m (by omega)
    have h2 : (q - 1) * m + m = q * m := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    rw [mul_comm q m] at h2
    omega

theorem snd_le_of_mem_clauseTermsD (Φ : CNF) {c : Clause} (hc : ∀ l ∈ c, Occurs Φ l.var)
    {t : ℤ × ℕ}
    (ht : t ∈ clauseTermsD (oddPrimeList (numVars Φ)) (bigN Φ) (c.map (renumLit Φ))) :
    t.2 ≤ c.length * (bigN Φ - 1) := by
  induction c generalizing t with
  | nil =>
    simp only [List.map_nil, clauseTermsD, List.foldr_nil, List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rw [ht]
    simp
  | cons l c ih =>
    rw [List.map_cons, clauseTermsD, List.foldr_cons, ← clauseTermsD] at ht
    obtain ⟨a, ha, b, hb, hab⟩ := exists_of_mem_mulITerms ht
    have h1 := snd_le_of_mem_litTermsD Φ (hc l List.mem_cons_self) ha
    have h2 := ih (fun l' hl' => hc l' (List.mem_cons_of_mem _ hl')) hb
    rw [hab, List.length_cons, Nat.succ_mul]
    omega

/-- Every raw exponent of every `C_j` is `< 3N`, so the offset satisfies `K < 3N`. -/
theorem offsetD_lt_three_mul_bigN (Φ : CNF) (h3 : ∀ c ∈ Φ, c.length ≤ 3) :
    offsetD (clauseListD (oddPrimeList (numVars Φ)) (renumber Φ)) < 3 * bigN Φ := by
  have hN := bigN_pos Φ
  have hle : offsetD (clauseListD (oddPrimeList (numVars Φ)) (renumber Φ)) ≤ 3 * (bigN Φ - 1) := by
    rw [offsetD, degreeZ_le_iff]
    intro t ht
    rw [List.mem_flatten, clauseListD_renumber] at ht
    obtain ⟨C, hC, ht⟩ := ht
    rw [List.mem_map] at hC
    obtain ⟨c, hc, rfl⟩ := hC
    have := snd_le_of_mem_clauseTermsD Φ (fun l hl => ⟨c, hc, l, hl, rfl⟩) ht
    exact this.trans (Nat.mul_le_mul_right _ (h3 c hc))
  omega

/-- Each exponent of `S` has absolute value `< 3N`. -/
theorem Dexp_lt_three_mul_bigN (Φ : CNF) (h3 : ∀ c ∈ Φ, c.length ≤ 3) :
    Dexp Φ < 3 * bigN Φ := by
  have hN := bigN_pos Φ
  by_cases hΦ : Φ = []
  · subst hΦ
    simp [Dexp, Spoly]
    omega
  · have h1 := headExpD_sNormD_add_Dexp Φ hΦ
    have h2 := offsetD_lt_three_mul_bigN Φ h3
    omega

end SparseIrred.Machine
