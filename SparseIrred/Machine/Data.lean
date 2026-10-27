import SparseIrred.Machine.Primes
import SparseIrred.Sparse.Canonical

/-!
# The data-level algorithm computing `canonTerms (H_M)`

Everything here is a plain computable function on sparse term lists
`ITerms = List (ℤ × ℕ)` (coefficient, exponent); no list is ever indexed by `N`, `M` or a numerical
degree, and the number of terms stays polynomial in the input length (`Machine/Bounds.lean`).
The pipeline, for a CNF `Φ`:

1. `renumber Φ` — each literal's variable `v` is replaced by its index `varIdx Φ v`
   (`< numVars Φ` for occurring variables);
2. `qs = firstOddPrimes T n` — the first `n = numVars Φ` odd primes (trial division below `T`);
3. `N = qs.prod`, `m_i = N / q_i`;
4. literal raw lists `posLitTerms m = [(-1,0),(1,m)]`, `negLitTerms q m = [(1, r m) | r < q]`;
5. clause raw lists `clauseTermsD` = raw products (`mulITerms`, no merging);
6. Laurent exponents are avoided by the offset trick: `K = offsetD Cs` is the largest raw exponent
   of all `C_j`, and `sRawD K Cs = ∑_j C_j(X) · X^K C_j(X⁻¹)` (raw, via `reflectITerms`), which
   denotes `X^K S(X)` with natural exponents;
7. `sNormD` — `normalizeZ` (sort, combine like terms, drop zeros);
8. `aTermsD` — `A = 3 X^D S`: multiply coefficients by `3` and subtract the smallest exponent
   (`headExpD`, which equals `K - D`);
9. `wD`, `mD`, `MD` — `w = ‖c‖ + ‖A‖ + #c + #A = 4 + ∑ a² + #A` (`‖·‖` the sum of the squared
   coefficients, `#` the number of terms, `c = 1 - X^N`, `a` ranging over the coefficients of
   `A`), `m = max(N, deg A)` and `M = 2^{20(w+1)} (m+1)^6`;
10. `outTermsD N A = A ++ [(-1, M), (1, M + N)]` — canonical list of `H_M = A - X^M + X^{M+N}`.

`reduceTerms` adds the branch structure of `reducePoly`.  That this computes the canonical term
list of the mathematical construction, `canonTerms (reducePoly x) = reduceTerms x`, is proved in
`Machine/DataCorrect.lean`.
-/

open Polynomial Complexity.SAT SparseDiv.Appendix

namespace SparseIrred.Machine

open SparseIrred

/-! ### Raw term-list operations -/

/-- All pairwise products (no merging); order: for each `s ∈ l₁`, for each `t ∈ l₂`. -/
def mulITerms (l₁ l₂ : ITerms) : ITerms :=
  l₁.flatMap fun s => l₂.map fun t => (s.1 * t.1, s.2 + t.2)

/-- Exponent reflection `e ↦ K - e` (truncated; exact when every exponent is `≤ K`). -/
def reflectITerms (K : ℕ) (l : ITerms) : ITerms := l.map fun t => (t.1, K - t.2)

/-- Raw terms of `P⁺ = X^m - 1`. -/
def posLitTerms (m : ℕ) : ITerms := [(-1, 0), (1, m)]

/-- Raw terms of `P⁻ = ∑_{r<q} X^{r m}`. -/
def negLitTerms (q m : ℕ) : ITerms := (List.range q).map fun r => (1, r * m)

/-- Raw terms of a literal whose variable field is already an index into the prime list `qs`
(out-of-range indices read the prime `0`, mirroring `nthBlockStr`'s default `[]`). -/
def litTermsD (qs : List ℕ) (N : ℕ) (l : Lit) : ITerms :=
  if l.sign then posLitTerms (N / qs.getD l.var 0)
  else negLitTerms (qs.getD l.var 0) (N / qs.getD l.var 0)

/-- Raw terms of a clause: the product of its literal lists, as a `foldr` from `[(1, 0)]`. -/
def clauseTermsD (qs : List ℕ) (N : ℕ) (c : Clause) : ITerms :=
  c.foldr (fun l acc => mulITerms (litTermsD qs N l) acc) [(1, 0)]

/-- Renumber one literal: its variable `v` becomes `varIdx Φ v`. -/
def renumLit (Φ : CNF) (l : Lit) : Lit := { sign := l.sign, var := varIdx Φ l.var }

/-- Renumber the variables of `Φ` by `varIdx Φ`. -/
def renumber (Φ : CNF) : CNF := Φ.map (List.map (renumLit Φ))

/-- The clause raw lists, with `N = qs.prod`. -/
def clauseListD (qs : List ℕ) (Ψ : CNF) : List ITerms := Ψ.map (clauseTermsD qs qs.prod)

/-- The offset `K`: the largest raw exponent occurring in any clause list. -/
def offsetD (Cs : List ITerms) : ℕ := degreeZ Cs.flatten

/-- `X^K S(X)` as a raw list: `∑_j C_j(X) · X^K C_j(X⁻¹)`. -/
def sRawD (K : ℕ) (Cs : List ITerms) : ITerms :=
  Cs.flatMap fun C => mulITerms C (reflectITerms K C)

/-- The collected (canonical) list of `X^K S(X)`. -/
def sNormD (qs : List ℕ) (Ψ : CNF) : ITerms :=
  normalizeZ (sRawD (offsetD (clauseListD qs Ψ)) (clauseListD qs Ψ))

/-- The exponent of the first term (`0` for the empty list). -/
def headExpD (l : ITerms) : ℕ := (l.headD (0, 0)).2

/-- `A = 3 X^D S` from the canonical list of `X^K S`: scale by `3`, shift down by the smallest
exponent. -/
def aTermsD (s : ITerms) : ITerms := s.map fun t => (3 * t.1, t.2 - headExpD s)

/-- `∑ c²` over a term list. -/
def sqSumD (l : ITerms) : ℕ := (l.map fun t => t.1.natAbs ^ 2).sum

/-- `w = ‖c‖ + ‖A‖ + #c + #A` with `‖c‖ = #c = 2` for `c = 1 - X^N`. -/
def wD (A : ITerms) : ℕ := 4 + sqSumD A + A.length

/-- `m = max (deg c, deg A) = max (N, deg A)`. -/
def mD (N : ℕ) (A : ITerms) : ℕ := max N (degreeZ A)

/-- `M = 2^{20(w+1)} (m+1)^6`. -/
def MD (N : ℕ) (A : ITerms) : ℕ := 2 ^ (20 * (wD A + 1)) * (mD N A + 1) ^ 6

/-- The canonical list of `H_M = A + X^M (X^N - 1)`. -/
def outTermsD (N : ℕ) (A : ITerms) : ITerms := A ++ [(-1, MD N A), (1, MD N A + N)]

/-- The `A`-terms computed from a prime list and a renumbered CNF. -/
def hmA (qs : List ℕ) (Ψ : CNF) : ITerms := aTermsD (sNormD qs Ψ)

/-- The output list computed from a prime list and a renumbered CNF. -/
def hmCore (qs : List ℕ) (Ψ : CNF) : ITerms := outTermsD qs.prod (hmA qs Ψ)

/-- The whole data-level construction, with prime candidates below `T`. -/
def hmTerms (T : ℕ) (Φ : CNF) : ITerms := hmCore (firstOddPrimes T (numVars Φ)) (renumber Φ)

/-- The data-level reduction, mirroring the branches of `reducePoly`. -/
def reduceTerms (x : List Bool) : ITerms :=
  match CNF.decode3? x with
  | none => [(1, 1)]
  | some Φ => if Φ = [] then [(-1, 0), (1, 2)] else hmTerms (primeBound x.length) Φ

/-! ### Structural lemmas -/

theorem toPolyZ_append (l₁ l₂ : ITerms) : toPolyZ (l₁ ++ l₂) = toPolyZ l₁ + toPolyZ l₂ := by
  simp [toPolyZ]

theorem toPolyZ_flatMap {α : Type*} (L : List α) (f : α → ITerms) :
    toPolyZ (L.flatMap f) = (L.map fun a => toPolyZ (f a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, toPolyZ_append, ih]

theorem toPolyZ_map_mul (s : ℤ × ℕ) (l : ITerms) :
    toPolyZ (l.map fun t => (s.1 * t.1, s.2 + t.2)) = C s.1 * X ^ s.2 * toPolyZ l := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, toPolyZ_cons, ih, C_mul, pow_add]
    ring

theorem toPolyZ_mulITerms (l₁ l₂ : ITerms) :
    toPolyZ (mulITerms l₁ l₂) = toPolyZ l₁ * toPolyZ l₂ := by
  induction l₁ with
  | nil => simp [mulITerms]
  | cons s l ih =>
    rw [mulITerms, List.flatMap_cons, toPolyZ_append, toPolyZ_map_mul, ← mulITerms, ih,
      toPolyZ_cons]
    ring

theorem length_mulITerms (l₁ l₂ : ITerms) :
    (mulITerms l₁ l₂).length = l₁.length * l₂.length := by
  induction l₁ with
  | nil => simp [mulITerms]
  | cons s l ih =>
    rw [mulITerms, List.flatMap_cons, List.length_append, List.length_map, ← mulITerms, ih,
      List.length_cons]
    ring

theorem length_reflectITerms (K : ℕ) (l : ITerms) : (reflectITerms K l).length = l.length := by
  simp [reflectITerms]

theorem toPolyZ_posLitTerms (m : ℕ) : toPolyZ (posLitTerms m) = X ^ m - 1 := by
  simp [posLitTerms, toPolyZ]
  ring

theorem toPolyZ_negLitTerms (q m : ℕ) :
    toPolyZ (negLitTerms q m) = ∑ r ∈ Finset.range q, (X : ℤ[X]) ^ (r * m) := by
  induction q with
  | zero => simp [negLitTerms]
  | succ q ih =>
    rw [negLitTerms, List.range_succ, List.map_append, toPolyZ_append, ← negLitTerms, ih,
      Finset.sum_range_succ]
    simp

/-- Every exponent occurring in one of the clause lists `Cs` is at most the offset `offsetD Cs`. -/
theorem le_offsetD {Cs : List ITerms} {C : ITerms} (hC : C ∈ Cs) {t : ℤ × ℕ} (ht : t ∈ C) :
    t.2 ≤ offsetD Cs :=
  snd_le_degreeZ (List.mem_flatten.2 ⟨C, hC, ht⟩)

theorem headExpD_cons (t : ℤ × ℕ) (l : ITerms) : headExpD (t :: l) = t.2 := rfl

theorem headExpD_nil : headExpD [] = 0 := rfl

theorem normalizedZ_aTermsD {s : ITerms} (hs : NormalizedZ s) : NormalizedZ (aTermsD s) := by
  obtain ⟨hpw, hnz⟩ := hs
  have hle : ∀ t ∈ s, headExpD s ≤ t.2 := by
    cases s with
    | nil => simp
    | cons t₀ rest =>
      intro t ht
      rw [headExpD_cons]
      rcases List.mem_cons.1 ht with rfl | h
      · exact le_rfl
      · exact ((List.pairwise_cons.1 hpw).1 t h).le
  refine ⟨?_, ?_⟩
  · rw [aTermsD, List.pairwise_map]
    refine hpw.imp_of_mem fun ha hb hab => ?_
    have := hle _ ha
    have := hle _ hb
    simp only
    omega
  · intro t ht
    rw [aTermsD, List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    simp [hnz t' ht']

theorem degreeZ_lt_MD (N : ℕ) (A : ITerms) : degreeZ A < MD N A := by
  unfold MD mD
  have h1 : max N (degreeZ A) + 1 ≤ (max N (degreeZ A) + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have h2 : 1 ≤ 2 ^ (20 * (wD A + 1)) := Nat.one_le_two_pow
  have h3 : (max N (degreeZ A) + 1) ^ 6 ≤
      2 ^ (20 * (wD A + 1)) * (max N (degreeZ A) + 1) ^ 6 := Nat.le_mul_of_pos_left _ h2
  have h4 := le_max_right N (degreeZ A)
  omega

theorem normalizedZ_outTermsD {N : ℕ} {A : ITerms} (hA : NormalizedZ A) (hN : 0 < N) :
    NormalizedZ (outTermsD N A) := by
  obtain ⟨hpw, hnz⟩ := hA
  have hlt := degreeZ_lt_MD N A
  refine ⟨?_, ?_⟩
  · rw [outTermsD, List.pairwise_append]
    refine ⟨hpw, by simp; omega, ?_⟩
    intro a ha b hb
    have := snd_le_degreeZ ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only <;> omega
  · intro t ht
    rw [outTermsD, List.mem_append] at ht
    rcases ht with ht | ht
    · exact hnz t ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp

theorem toPolyZ_outTermsD (N : ℕ) (A : ITerms) :
    toPolyZ (outTermsD N A) = toPolyZ A + X ^ MD N A * (X ^ N - 1) := by
  rw [outTermsD, toPolyZ_append]
  simp [toPolyZ]
  ring

theorem length_renumber (Φ : CNF) : (renumber Φ).length = Φ.length := by
  simp [renumber]

theorem is3CNF_renumber {Φ : CNF} (h : Φ.Is3CNF) : (renumber Φ).Is3CNF := by
  intro c hc
  rw [renumber, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  rw [List.length_map]
  exact h c' hc'

theorem clause_length_le_of_is3CNF {Φ : CNF} (h : Φ.Is3CNF) : ∀ c ∈ Φ, c.length ≤ 3 :=
  fun c hc => (h c hc).le

end SparseIrred.Machine
