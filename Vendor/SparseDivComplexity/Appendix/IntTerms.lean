import Mathlib
import SparseDivComplexity.Appendix.Content

/-!
# Appendix A.1 — sparse integer polynomials: normalization and the preliminary reductions

The integer side of Appendix A works with sparse polynomials in `ℤ[X]` given as lists of signed
coefficient–exponent pairs. This module provides the term-list layer over `ℤ` (the analogue of
`Terms.lean` over `𝔽_p`) and the decision procedure of Appendix A.1:

* `normalizeZ` merges equal exponents and deletes zero coefficients;
* the boundary cases `g = 0`, `f = 0`, constant `g` (coefficient divisibility), `deg g > deg f`
  (`boundaryDecide`, correct by `boundaryDecide_correct`);
* the content split `c = cont g`, `G = g / c` and the reduction of `g ∣ f` to
  `c ∣ every coefficient of f` and `G ∣ f / c` (`main_branch_iff`), with Gauss's lemma connecting
  divisibility in `ℤ[X]` and `ℚ[X]` for the primitive `G` (`Appendix/Content.lean`).

The bit complexity of these operations on the binary encoding is the subject of
`StringArith/DivMod.lean`, `StringArith/Gcd.lean` and `Appendix/IntTermsString.lean`.
-/

open Polynomial

namespace SparseDiv.Appendix

/-- Integer sparse term lists: signed coefficients, natural exponents. -/
abbrev ITerms := List (ℤ × ℕ)

/-- The integer polynomial denoted by a term list. -/
noncomputable def toPolyZ (l : ITerms) : ℤ[X] := (l.map fun t ↦ C t.1 * X ^ t.2).sum

@[simp] theorem toPolyZ_nil : toPolyZ [] = 0 := by simp [toPolyZ]

@[simp] theorem toPolyZ_cons (t : ℤ × ℕ) (l : ITerms) :
    toPolyZ (t :: l) = C t.1 * X ^ t.2 + toPolyZ l := by simp [toPolyZ]

theorem coeff_toPolyZ (l : ITerms) (n : ℕ) :
    (toPolyZ l).coeff n = ((l.filter fun t ↦ t.2 = n).map Prod.fst).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [toPolyZ_cons, coeff_add, ih, coeff_C_mul, coeff_X_pow]
    by_cases h : t.2 = n
    · simp [h]
    · simp [h, Ne.symm h]

/-- Insert a term into a list kept strictly sorted by exponent, merging like terms and dropping
zero coefficients. -/
def insertTermZ (c : ℤ) (e : ℕ) : ITerms → ITerms
  | [] => if c = 0 then [] else [(c, e)]
  | (c', e') :: rest =>
    if e < e' then (if c = 0 then (c', e') :: rest else (c, e) :: (c', e') :: rest)
    else if e = e' then (if c + c' = 0 then rest else (c + c', e) :: rest)
    else (c', e') :: insertTermZ c e rest

/-- Collect like terms. -/
def normalizeZ : ITerms → ITerms
  | [] => []
  | (c, e) :: rest => insertTermZ c e (normalizeZ rest)

/-- Canonical integer term lists: strictly increasing exponents, nonzero coefficients. -/
def NormalizedZ (l : ITerms) : Prop := l.Pairwise (fun s t ↦ s.2 < t.2) ∧ ∀ t ∈ l, t.1 ≠ 0

theorem toPolyZ_insertTermZ (c : ℤ) (e : ℕ) (l : ITerms) :
    toPolyZ (insertTermZ c e l) = C c * X ^ e + toPolyZ l := by
  induction l with
  | nil =>
    simp only [insertTermZ]
    split_ifs with h
    · rw [toPolyZ_nil, h]; simp
    · simp
  | cons t l ih =>
    obtain ⟨c', e'⟩ := t
    simp only [insertTermZ]
    split_ifs with h₁ h₂ h₃ h₄
    · rw [h₂]; simp
    · rw [toPolyZ_cons]
    · rw [toPolyZ_cons]
      dsimp only
      rw [← h₃, ← add_assoc, ← add_mul, ← C_add, h₄]
      simp
    · simp only [toPolyZ_cons]
      rw [C_add, add_mul, add_assoc, h₃]
    · rw [toPolyZ_cons, ih, toPolyZ_cons, add_left_comm]

theorem toPolyZ_normalizeZ (l : ITerms) : toPolyZ (normalizeZ l) = toPolyZ l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    obtain ⟨c, e⟩ := t
    simp only [normalizeZ]
    rw [toPolyZ_insertTermZ, ih, toPolyZ_cons]

/-- Every exponent occurring in `insertTermZ c e l` is either `e` or an exponent of `l`. -/
private theorem snd_of_mem_insertTermZ {c : ℤ} {e : ℕ} {l : ITerms} {t : ℤ × ℕ}
    (ht : t ∈ insertTermZ c e l) : t.2 = e ∨ ∃ s ∈ l, t.2 = s.2 := by
  induction l with
  | nil =>
    simp only [insertTermZ] at ht
    split_ifs at ht
    · simp at ht
    · simp only [List.mem_singleton] at ht
      exact Or.inl (by rw [ht])
  | cons s l ih =>
    obtain ⟨c', e'⟩ := s
    simp only [insertTermZ] at ht
    split_ifs at ht
    · exact Or.inr ⟨t, ht, rfl⟩
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl rfl
      · exact Or.inr ⟨t, ht, rfl⟩
    · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, rfl⟩
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl rfl
      · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, rfl⟩
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inr ⟨_, List.mem_cons_self .., rfl⟩
      · rcases ih ht with h | ⟨u, hu, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, h⟩

/-- Insertion preserves canonicity. -/
theorem normalizedZ_insertTermZ (c : ℤ) (e : ℕ) {l : ITerms} (h : NormalizedZ l) :
    NormalizedZ (insertTermZ c e l) := by
  induction l with
  | nil =>
    simp only [insertTermZ]
    split_ifs with h0
    · exact ⟨List.Pairwise.nil, by simp⟩
    · exact ⟨List.pairwise_singleton _ _, by simp [h0]⟩
  | cons t l ih =>
    obtain ⟨c', e'⟩ := t
    obtain ⟨hpw, hb⟩ := h
    rw [List.pairwise_cons] at hpw
    obtain ⟨hlt, hpw⟩ := hpw
    have hl : NormalizedZ l := ⟨hpw, fun t ht ↦ hb t (List.mem_cons_of_mem _ ht)⟩
    have hb' := hb (c', e') (List.mem_cons_self ..)
    simp only [insertTermZ]
    split_ifs with h₁ h₂ h₃ h₄
    · exact ⟨List.pairwise_cons.mpr ⟨hlt, hpw⟩, hb⟩
    · refine ⟨List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨hlt, hpw⟩⟩, ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact h₁
        · exact h₁.trans (hlt s hs)
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact h₂
        · exact hb s hs
    · exact hl
    · refine ⟨List.pairwise_cons.mpr ⟨fun s hs ↦ h₃ ▸ hlt s hs, hpw⟩, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact h₄
      · exact hb s (List.mem_cons_of_mem _ hs)
    · obtain ⟨hpw', hb''⟩ := ih hl
      refine ⟨List.pairwise_cons.mpr ⟨?_, hpw'⟩, ?_⟩
      · intro s hs
        rcases snd_of_mem_insertTermZ hs with hs | ⟨u, hu, hs⟩
        · show e' < s.2
          rw [hs]; omega
        · show e' < s.2
          rw [hs]; exact hlt u hu
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hb'
        · exact hb'' s hs

theorem normalizedZ_normalizeZ (l : ITerms) : NormalizedZ (normalizeZ l) := by
  induction l with
  | nil => exact ⟨List.Pairwise.nil, by simp [normalizeZ]⟩
  | cons t l ih =>
    obtain ⟨c, e⟩ := t
    exact normalizedZ_insertTermZ c e ih

/-- Insertion adds at most one term. -/
theorem length_insertTermZ_le (c : ℤ) (e : ℕ) (l : ITerms) :
    (insertTermZ c e l).length ≤ l.length + 1 := by
  induction l with
  | nil =>
    simp only [insertTermZ]
    split_ifs <;> simp
  | cons t l ih =>
    obtain ⟨c', e'⟩ := t
    simp only [insertTermZ]
    split_ifs <;> simp only [List.length_cons] <;> omega

theorem length_normalizeZ_le (l : ITerms) : (normalizeZ l).length ≤ l.length := by
  induction l with
  | nil => simp [normalizeZ]
  | cons t l ih =>
    obtain ⟨c, e⟩ := t
    simp only [normalizeZ, List.length_cons]
    exact (length_insertTermZ_le c e _).trans (Nat.succ_le_succ ih)

/-- In a list with strictly increasing exponents, at most one term has a given exponent. -/
private theorem filter_snd_eq_of_pairwiseZ {l : ITerms} (hl : l.Pairwise fun s t ↦ s.2 < t.2)
    (n : ℕ) :
    l.filter (fun t ↦ t.2 = n) = [] ∨ ∃ t ∈ l, t.2 = n ∧ l.filter (fun t ↦ t.2 = n) = [t] := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨ht, hl⟩ := hl
    by_cases h : t.2 = n
    · right
      refine ⟨t, List.mem_cons_self .., h, ?_⟩
      rw [List.filter_cons_of_pos (by simpa using h), List.filter_eq_nil_iff.mpr]
      intro s hs
      have := ht s hs
      simp only [decide_eq_true_eq]
      omega
    · rw [List.filter_cons_of_neg (by simpa using h)]
      rcases ih hl with h' | ⟨s, hs, hsn, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, hsn, h'⟩

theorem support_toPolyZ_of_normalizedZ {l : ITerms} (h : NormalizedZ l) :
    (toPolyZ l).support = (l.map Prod.snd).toFinset := by
  ext n
  rw [mem_support_iff, coeff_toPolyZ, List.mem_toFinset, List.mem_map]
  rcases filter_snd_eq_of_pairwiseZ h.1 n with h' | ⟨t, ht, htn, h'⟩
  · rw [h']
    simp only [List.map_nil, List.sum_nil, ne_eq, not_true_eq_false, false_iff, not_exists,
      not_and]
    intro t ht htn
    have : t ∈ l.filter (fun t ↦ t.2 = n) := List.mem_filter.mpr ⟨ht, by simpa using htn⟩
    rw [h'] at this
    exact List.not_mem_nil this
  · rw [h']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact ⟨fun _ ↦ ⟨t, ht, htn⟩, fun _ ↦ h.2 t ht⟩

/-- A canonical list has exactly as many entries as its polynomial has nonzero terms. -/
theorem card_support_toPolyZ_of_normalizedZ {l : ITerms} (h : NormalizedZ l) :
    (toPolyZ l).support.card = l.length := by
  rw [support_toPolyZ_of_normalizedZ h, List.toFinset_card_of_nodup, List.length_map]
  exact ((List.pairwise_map (R := (· < ·))).mpr h.1).nodup

theorem card_support_toPolyZ_eq_length_normalizeZ (l : ITerms) :
    (toPolyZ l).support.card = (normalizeZ l).length := by
  rw [← toPolyZ_normalizeZ, card_support_toPolyZ_of_normalizedZ (normalizedZ_normalizeZ l)]

theorem toPolyZ_eq_zero_iff_normalizeZ_eq_nil (l : ITerms) :
    toPolyZ l = 0 ↔ normalizeZ l = [] := by
  rw [← Polynomial.support_eq_empty, ← Finset.card_eq_zero,
    card_support_toPolyZ_eq_length_normalizeZ, List.length_eq_zero_iff]

/-- A canonical list denotes the zero polynomial iff it is empty. -/
theorem toPolyZ_eq_zero_iff_of_normalizedZ {l : ITerms} (h : NormalizedZ l) :
    toPolyZ l = 0 ↔ l = [] := by
  rw [← Polynomial.support_eq_empty, ← Finset.card_eq_zero,
    card_support_toPolyZ_of_normalizedZ h, List.length_eq_zero_iff]

/-- The coefficient of a canonical list at a listed exponent is the listed coefficient. -/
theorem coeff_toPolyZ_of_normalizedZ_mem {l : ITerms} (h : NormalizedZ l) {t : ℤ × ℕ}
    (ht : t ∈ l) : (toPolyZ l).coeff t.2 = t.1 := by
  rw [coeff_toPolyZ]
  have hmem : t ∈ l.filter (fun s ↦ s.2 = t.2) := List.mem_filter.mpr ⟨ht, by simp⟩
  rcases filter_snd_eq_of_pairwiseZ h.1 t.2 with h' | ⟨s, _, _, h'⟩
  · rw [h'] at hmem
    exact absurd hmem List.not_mem_nil
  · rw [h'] at hmem ⊢
    rw [List.mem_singleton] at hmem
    subst hmem
    simp

/-- The degree of a term list: the largest listed exponent. -/
def degreeZ (l : ITerms) : ℕ := (l.map Prod.snd).foldr max 0

/-- `degreeZ l ≤ m` iff every listed exponent is at most `m`. -/
theorem degreeZ_le_iff {l : ITerms} {m : ℕ} : degreeZ l ≤ m ↔ ∀ t ∈ l, t.2 ≤ m := by
  unfold degreeZ
  induction l with
  | nil => simp
  | cons t l ih => simp [ih]

/-- Every listed exponent is at most `degreeZ l`. -/
theorem snd_le_degreeZ {l : ITerms} {t : ℤ × ℕ} (ht : t ∈ l) : t.2 ≤ degreeZ l :=
  degreeZ_le_iff.mp le_rfl t ht

/-- The largest listed exponent bounds the degree. -/
theorem natDegree_toPolyZ_le (l : ITerms) : (toPolyZ l).natDegree ≤ degreeZ l := by
  unfold degreeZ
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [toPolyZ_cons, List.map_cons, List.foldr_cons]
    exact (natDegree_add_le _ _).trans (max_le_max (natDegree_C_mul_X_pow_le _ _) ih)

/-- Every exponent of a canonical list is at most the degree of its polynomial. -/
theorem exponent_le_natDegree_of_normalizedZ {l : ITerms} (h : NormalizedZ l) {t : ℤ × ℕ}
    (ht : t ∈ l) : t.2 ≤ (toPolyZ l).natDegree :=
  le_natDegree_of_mem_supp _ (by
    rw [support_toPolyZ_of_normalizedZ h]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩))

theorem natDegree_toPolyZ_of_normalizedZ {l : ITerms} (h : NormalizedZ l) :
    (toPolyZ l).natDegree = degreeZ l :=
  le_antisymm (natDegree_toPolyZ_le l)
    (degreeZ_le_iff.mpr fun _ ht ↦ exponent_le_natDegree_of_normalizedZ h ht)

/-- In a strictly sorted list every exponent is at most the last one. -/
private theorem snd_le_getLast_of_pairwise : ∀ {l : ITerms} (hl : l ≠ [])
    (_ : l.Pairwise (fun s t ↦ s.2 < t.2)), ∀ t ∈ l, t.2 ≤ (l.getLast hl).2
  | [], hl, _ => absurd rfl hl
  | [_], _, _ => by simp
  | a :: b :: rest, _, hpw => by
    rw [List.pairwise_cons] at hpw
    intro t ht
    rw [List.getLast_cons (List.cons_ne_nil b rest)]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (hpw.1 _ (List.getLast_mem _)).le
    · exact snd_le_getLast_of_pairwise (List.cons_ne_nil b rest) hpw.2 t ht

/-- The degree of a strictly sorted nonempty list is its last exponent. -/
theorem degreeZ_eq_snd_getLast {l : ITerms} (hpw : l.Pairwise (fun s t ↦ s.2 < t.2))
    (hl : l ≠ []) : degreeZ l = (l.getLast hl).2 :=
  le_antisymm (degreeZ_le_iff.mpr (snd_le_getLast_of_pairwise hl hpw))
    (snd_le_degreeZ (List.getLast_mem hl))

/-- A strictly sorted list `(c, e) :: rest` has degree `0` iff it is the singleton `[(c, 0)]`. -/
theorem degreeZ_cons_eq_zero_iff {c : ℤ} {e : ℕ} {rest : ITerms}
    (hpw : ((c, e) :: rest).Pairwise (fun s t ↦ s.2 < t.2)) :
    degreeZ ((c, e) :: rest) = 0 ↔ e = 0 ∧ rest = [] := by
  rw [List.pairwise_cons] at hpw
  constructor
  · intro h0
    have hall : ∀ t ∈ (c, e) :: rest, t.2 ≤ 0 := degreeZ_le_iff.mp h0.le
    refine ⟨Nat.le_zero.mp (hall _ (List.mem_cons_self ..)), ?_⟩
    cases rest with
    | nil => rfl
    | cons s rest =>
      have h1 := hpw.1 s (List.mem_cons_self ..)
      have h2 := hall s (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      omega
  · rintro ⟨rfl, rfl⟩
    simp [degreeZ]

/-- The content of a term list: the gcd of the absolute values of the listed coefficients. -/
def contentZ (l : ITerms) : ℕ := l.foldr (fun t acc ↦ Nat.gcd t.1.natAbs acc) 0

@[simp] theorem contentZ_nil : contentZ [] = 0 := rfl

@[simp] theorem contentZ_cons (t : ℤ × ℕ) (l : ITerms) :
    contentZ (t :: l) = Nat.gcd t.1.natAbs (contentZ l) := rfl

/-- `contentZ l` divides every listed coefficient. -/
theorem contentZ_dvd_of_mem {l : ITerms} {t : ℤ × ℕ} (ht : t ∈ l) : (contentZ l : ℤ) ∣ t.1 := by
  induction l with
  | nil => exact absurd ht List.not_mem_nil
  | cons s l ih =>
    rw [contentZ_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (ih ht)

/-- Every common divisor of the listed coefficients divides `contentZ l`. -/
theorem dvd_contentZ {l : ITerms} {d : ℤ} (hd : ∀ t ∈ l, d ∣ t.1) : d ∣ (contentZ l : ℤ) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [contentZ_cons, Int.dvd_natCast]
    exact Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr (hd t (List.mem_cons_self ..)))
      (Int.dvd_natCast.mp (ih fun s hs ↦ hd s (List.mem_cons_of_mem _ hs)))

/-- `contentZ l` divides every coefficient of the polynomial (no canonicity needed). -/
theorem contentZ_dvd_coeff (l : ITerms) (n : ℕ) : (contentZ l : ℤ) ∣ (toPolyZ l).coeff n := by
  rw [coeff_toPolyZ]
  refine List.dvd_sum fun x hx ↦ ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact contentZ_dvd_of_mem (List.mem_filter.mp ht).1

/-- For canonical lists, `contentZ` is Mathlib's `Polynomial.content`. -/
theorem contentZ_eq_content {l : ITerms} (h : NormalizedZ l) :
    (contentZ l : ℤ) = (toPolyZ l).content := by
  refine Int.dvd_antisymm (Int.natCast_nonneg _) ?_ ?_ ?_
  · rw [← normalize_content, ← Int.abs_eq_normalize]
    exact abs_nonneg _
  · exact dvd_content_iff_C_dvd.mpr ((C_dvd_iff_dvd_coeff _ _).mpr (contentZ_dvd_coeff l))
  · refine dvd_contentZ fun t ht ↦ ?_
    have := content_dvd_coeff (p := toPolyZ l) t.2
    rwa [coeff_toPolyZ_of_normalizedZ_mem h ht] at this

/-- Does `c` divide every listed coefficient? -/
def dvdAllZ (c : ℤ) (l : ITerms) : Bool := l.all fun t ↦ decide (c ∣ t.1)

/-- `dvdAllZ c l` holds iff `c` divides every listed coefficient. -/
theorem dvdAllZ_iff_forall_mem {c : ℤ} {l : ITerms} :
    dvdAllZ c l = true ↔ ∀ t ∈ l, c ∣ t.1 := by
  simp [dvdAllZ, List.all_eq_true]

theorem dvdAllZ_iff_forall_coeff {c : ℤ} {l : ITerms} (h : NormalizedZ l) :
    dvdAllZ c l = true ↔ ∀ n, c ∣ (toPolyZ l).coeff n := by
  rw [dvdAllZ_iff_forall_mem]
  constructor
  · intro hall n
    rw [coeff_toPolyZ]
    refine List.dvd_sum fun x hx ↦ ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact hall t (List.mem_filter.mp ht).1
  · intro hall t ht
    have := hall t.2
    rwa [coeff_toPolyZ_of_normalizedZ_mem h ht] at this

/-- Divide every coefficient by `c`. -/
def divCoeffsZ (c : ℤ) (l : ITerms) : ITerms := l.map fun t ↦ (t.1 / c, t.2)

@[simp] theorem divCoeffsZ_nil (c : ℤ) : divCoeffsZ c [] = [] := rfl

@[simp] theorem divCoeffsZ_cons (c : ℤ) (t : ℤ × ℕ) (l : ITerms) :
    divCoeffsZ c (t :: l) = (t.1 / c, t.2) :: divCoeffsZ c l := rfl

-- `hc` is not needed: if `c = 0` then `dvdAllZ 0 l` forces every listed coefficient to be `0`.
set_option linter.unusedVariables false in
theorem C_mul_toPolyZ_divCoeffsZ {c : ℤ} {l : ITerms} (hc : c ≠ 0) (h : dvdAllZ c l = true) :
    C c * toPolyZ (divCoeffsZ c l) = toPolyZ l := by
  rw [dvdAllZ_iff_forall_mem] at h
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [divCoeffsZ_cons, toPolyZ_cons, toPolyZ_cons, mul_add, ← mul_assoc, ← C_mul,
      Int.mul_ediv_cancel' (h t (List.mem_cons_self ..)),
      ih fun s hs ↦ h s (List.mem_cons_of_mem _ hs)]

/-- The primitive part of a term list. -/
def primPartZ (l : ITerms) : ITerms := divCoeffsZ (contentZ l) l

theorem toPolyZ_primPartZ {l : ITerms} (h : NormalizedZ l) (hl : l ≠ []) :
    toPolyZ (primPartZ l) = (toPolyZ l).primPart := by
  have h0 : toPolyZ l ≠ 0 := (toPolyZ_eq_zero_iff_of_normalizedZ h).not.mpr hl
  have hc : (contentZ l : ℤ) ≠ 0 := by
    rw [contentZ_eq_content h]
    exact content_eq_zero_iff.not.mpr h0
  refine mul_left_cancel₀ (C_ne_zero.mpr hc) ?_
  rw [primPartZ, C_mul_toPolyZ_divCoeffsZ hc
    (dvdAllZ_iff_forall_mem.mpr fun t ht ↦ contentZ_dvd_of_mem ht),
    contentZ_eq_content h, ← eq_C_content_mul_primPart]

theorem isPrimitive_toPolyZ_primPartZ {l : ITerms} (h : NormalizedZ l) (hl : l ≠ []) :
    (toPolyZ (primPartZ l)).IsPrimitive := by
  rw [toPolyZ_primPartZ h hl]
  exact isPrimitive_primPart _

/-- The leading coefficient of a canonical nonempty list is its last coefficient. -/
theorem leadingCoeff_toPolyZ_of_normalizedZ {l : ITerms} (h : NormalizedZ l) (hl : l ≠ []) :
    (toPolyZ l).leadingCoeff = (l.getLast hl).1 := by
  rw [leadingCoeff, natDegree_toPolyZ_of_normalizedZ h, degreeZ_eq_snd_getLast h.1 hl]
  exact coeff_toPolyZ_of_normalizedZ_mem h (List.getLast_mem hl)

/-- **The boundary cases of Appendix A.1.** Returns `some true` for a decided NON-divisibility
(YES instance), `some false` for a decided divisibility (NO instance), and `none` when the main
primitive branch is required. -/
def boundaryDecide (f g : ITerms) : Option Bool :=
  let f' := normalizeZ f
  let g' := normalizeZ g
  match g' with
  | [] => some (decide (f' ≠ []))
  | (c, e) :: rest =>
    if f' = [] then some false
    else if e = 0 ∧ rest = [] then some (!dvdAllZ c f')
    else if degreeZ f' < degreeZ g' then some true
    else none

/-- **Correctness of the boundary cases.** -/
theorem boundaryDecide_correct {f g : ITerms} {b : Bool} (h : boundaryDecide f g = some b) :
    (b = true ↔ ¬ toPolyZ g ∣ toPolyZ f) := by
  rw [← toPolyZ_normalizeZ f, ← toPolyZ_normalizeZ g]
  have hf := normalizedZ_normalizeZ f
  have hg := normalizedZ_normalizeZ g
  unfold boundaryDecide at h
  dsimp only at h
  generalize normalizeZ f = f' at h hf ⊢
  generalize normalizeZ g = g' at h hg ⊢
  rcases g' with _ | ⟨⟨c, e⟩, rest⟩
  · simp only at h
    rw [Option.some.injEq] at h
    subst h
    rw [toPolyZ_nil, zero_dvd_iff, toPolyZ_eq_zero_iff_of_normalizedZ hf]
    simp
  · simp only at h
    split_ifs at h with h1 h2 h3
    · rw [Option.some.injEq] at h
      subst h
      simp [h1]
    · rw [Option.some.injEq] at h
      subst h
      obtain ⟨rfl, rfl⟩ := h2
      rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, dvdAllZ_iff_forall_coeff hf,
        ← C_dvd_iff_forall_coeff]
      simp
    · rw [Option.some.injEq] at h
      subst h
      simp only [true_iff]
      refine not_dvd_of_natDegree_lt ((toPolyZ_eq_zero_iff_of_normalizedZ hf).not.mpr h1) ?_
      rwa [natDegree_toPolyZ_of_normalizedZ hf, natDegree_toPolyZ_of_normalizedZ hg]

/-- When `boundaryDecide` defers, `g` is nonzero of positive degree and `f` is nonzero of degree at
least `deg g`. -/
theorem boundaryDecide_eq_none_iff (f g : ITerms) :
    boundaryDecide f g = none ↔
      normalizeZ f ≠ [] ∧ normalizeZ g ≠ [] ∧ 0 < degreeZ (normalizeZ g) ∧
        degreeZ (normalizeZ g) ≤ degreeZ (normalizeZ f) := by
  have hg := normalizedZ_normalizeZ g
  unfold boundaryDecide
  dsimp only
  generalize normalizeZ f = f'
  generalize normalizeZ g = g' at hg ⊢
  rcases g' with _ | ⟨⟨c, e⟩, rest⟩
  · simp
  · have hdeg : 0 < degreeZ ((c, e) :: rest) ↔ ¬ (e = 0 ∧ rest = []) := by
      rw [Nat.pos_iff_ne_zero, ne_eq, degreeZ_cons_eq_zero_iff hg.1]
    simp only
    split_ifs with h1 h2 h3
    · simp [h1]
    · obtain ⟨rfl, rfl⟩ := h2
      simp [degreeZ]
    · simp [h3]
    · simp [h1, hdeg, h2, not_lt.mp h3]

/-- **The main branch (content split + Gauss).** For a nonzero `g` of positive degree with content
`c` and primitive part `G`: `g ∤ f` iff some coefficient of `f` is not divisible by `c`, or
`G ∤ f / c` in `ℚ[X]`. -/
theorem main_branch_iff {f g : ITerms} (hg : normalizeZ g ≠ []) :
    ¬ toPolyZ g ∣ toPolyZ f ↔
      dvdAllZ (contentZ (normalizeZ g)) (normalizeZ f) = false ∨
        ¬ (toPolyZ (primPartZ (normalizeZ g))).map (Int.castRingHom ℚ) ∣
          (toPolyZ (divCoeffsZ (contentZ (normalizeZ g)) (normalizeZ f))).map
            (Int.castRingHom ℚ) := by
  have hnf := normalizedZ_normalizeZ f
  have hng := normalizedZ_normalizeZ g
  have hg0 : toPolyZ (normalizeZ g) ≠ 0 := (toPolyZ_eq_zero_iff_of_normalizedZ hng).not.mpr hg
  have hc : (contentZ (normalizeZ g) : ℤ) ≠ 0 := by
    rw [contentZ_eq_content hng]
    exact content_eq_zero_iff.not.mpr hg0
  rw [← toPolyZ_normalizeZ f, ← toPolyZ_normalizeZ g, dvd_iff_content_dvd_and_primPart_dvd hg0,
    ← contentZ_eq_content hng, ← toPolyZ_primPartZ hng hg,
    ← primitive_dvd_iff_map_dvd_map (isPrimitive_toPolyZ_primPartZ hng hg), Bool.eq_false_iff,
    ne_eq, dvdAllZ_iff_forall_coeff hnf]
  constructor
  · intro hne
    by_cases hall : ∀ n, (contentZ (normalizeZ g) : ℤ) ∣ (toPolyZ (normalizeZ f)).coeff n
    · right
      intro hdvd
      exact hne ⟨_, (C_mul_toPolyZ_divCoeffsZ hc ((dvdAllZ_iff_forall_coeff hnf).mpr hall)).symm,
        hdvd⟩
    · exact Or.inl hall
  · rintro (hall | hdvd) ⟨f₀, hf₀, hPf₀⟩
    · exact hall ((exists_eq_C_mul_iff _ _ hc).mp ⟨f₀, hf₀⟩)
    · apply hdvd
      have hall := (exists_eq_C_mul_iff _ _ hc).mp ⟨f₀, hf₀⟩
      have heq := C_mul_toPolyZ_divCoeffsZ hc ((dvdAllZ_iff_forall_coeff hnf).mpr hall)
      rw [hf₀] at heq
      rwa [mul_left_cancel₀ (C_ne_zero.mpr hc) heq]

end SparseDiv.Appendix
