import SparseDivComplexity.Appendix.IntTermsString
import Complexitylib.Models.TuringMachine

/-!
# Binary-sparse codes of integer polynomials and the target languages

Three levels are kept apart:

* **semantics** — `f : ℤ[X]` (mathlib polynomials);
* **canonical sparse lists** — `ITerms = List (ℤ × ℕ)` (coefficient, exponent) with exponents
  strictly increasing and all coefficients nonzero (`NormalizedZ`), interpreted by `toPolyZ`
  (both from `SparseDivComplexity.Appendix.IntTerms`);
* **bit strings** — `List Bool`, via `encITerms` from `SparseDivComplexity.Appendix.IntTermsString`:
  a term `(c, e)` is `pair (encInt c) (encNat e)` where `encInt c = pair [c < 0] (Nat.bits |c|)`
  and `encNat e = Nat.bits e` (binary, least significant bit first), and a list of terms is the
  concatenation of the `delimit`-framed term codes.  Coefficients *and* exponents are binary.

`encPoly f` is the code of the canonical list of `f`.  Distinct polynomials have distinct codes
(`encPoly_injective`).  `decodePoly` recognises exactly the canonical codes
(`decodePoly_eq_some_iff`); every other bit string (malformed framing, non-canonical numerals,
unsorted or repeated exponents, zero coefficients, negative zero, …) is a non-code and belongs to
neither `IrredLang` nor `RedLang`.

`Reducible f` means `f ≠ 0` and `f` is a product of two non-units of `ℤ[X]`.  It is *not* identified
with `¬ Irreducible f` in general (`0`, `±1` are neither); `reducible_iff_not_irreducible` proves
the equivalence for polynomials of positive degree, which is the range of the reduction.
-/

open Polynomial Complexity SparseDiv SparseDiv.Appendix

namespace SparseIrred

/-- The canonical sparse list of `f`: its nonzero coefficient–exponent pairs, exponents
increasing. -/
noncomputable def canonTerms (f : ℤ[X]) : ITerms :=
  (f.support.sort (· ≤ ·)).map fun e => (f.coeff e, e)

/-- The canonical binary-sparse code of `f`. -/
noncomputable def encPoly (f : ℤ[X]) : List Bool := encITerms (canonTerms f)

open Classical in
/-- Decoder: `some f` exactly on canonical codes, `none` on every other bit string. -/
noncomputable def decodePoly (x : List Bool) : Option ℤ[X] :=
  match decITerms x with
  | some l => if NormalizedZ l ∧ encITerms l = x then some (toPolyZ l) else none
  | none => none

/-- The canonical list of `f` is canonical. -/
theorem canonTerms_normalizedZ (f : ℤ[X]) : NormalizedZ (canonTerms f) := by
  refine ⟨?_, ?_⟩
  · rw [canonTerms, List.pairwise_map]
    exact (Finset.sortedLT_sort f.support).pairwise
  · intro t ht
    rw [canonTerms, List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    rw [Finset.mem_sort, mem_support_iff] at he
    exact he

/-- The canonical list of `f` represents `f`. -/
theorem toPolyZ_canonTerms (f : ℤ[X]) : toPolyZ (canonTerms f) = f := by
  conv_rhs => rw [as_sum_support f]
  rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq f.support (· ≤ ·), Multiset.map_coe,
    Multiset.sum_coe]
  simp only [canonTerms, toPolyZ, List.map_map, Function.comp_def, C_mul_X_pow_eq_monomial]

/-- Uniqueness of canonical forms: a canonical list is determined by its polynomial. -/
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

/-- A canonical list is the canonical list of the polynomial it represents. -/
theorem canonTerms_toPolyZ {l : ITerms} (hl : NormalizedZ l) : canonTerms (toPolyZ l) = l :=
  eq_of_normalizedZ_of_toPolyZ_eq (canonTerms_normalizedZ _) hl (toPolyZ_canonTerms _)

/-- Distinct polynomials have distinct codes (a code determines its polynomial). -/
theorem encPoly_injective : Function.Injective encPoly := by
  intro f g h
  have hf := SparseDiv.Appendix.decITerms_encITerms (canonTerms f)
  have hg := SparseDiv.Appendix.decITerms_encITerms (canonTerms g)
  have h' : encITerms (canonTerms f) = encITerms (canonTerms g) := h
  rw [h', hg] at hf
  have hc := (Option.some.inj hf).symm
  rw [← toPolyZ_canonTerms f, ← toPolyZ_canonTerms g, hc]

/-- `decodePoly` recognises exactly the canonical codes. -/
theorem decodePoly_eq_some_iff {x : List Bool} {f : ℤ[X]} :
    decodePoly x = some f ↔ encPoly f = x := by
  constructor
  · intro h
    unfold decodePoly at h
    split at h
    · rename_i l _
      split_ifs at h with hl
      obtain ⟨hn, he⟩ := hl
      cases h
      rw [encPoly, canonTerms_toPolyZ hn, he]
    · exact absurd h (by simp)
  · rintro rfl
    unfold decodePoly encPoly
    rw [SparseDiv.Appendix.decITerms_encITerms]
    simp [canonTerms_normalizedZ f, toPolyZ_canonTerms]

/-- Decoding inverts encoding. -/
theorem decodePoly_encPoly (f : ℤ[X]) : decodePoly (encPoly f) = some f :=
  decodePoly_eq_some_iff.2 rfl

/-! ### Irreducibility and reducibility -/

/-- `f` is reducible: nonzero and a product of two non-units of `ℤ[X]`. -/
def Reducible (f : ℤ[X]) : Prop := f ≠ 0 ∧ ∃ g h : ℤ[X], ¬IsUnit g ∧ ¬IsUnit h ∧ f = g * h

/-- `f` is reducible iff it is nonzero, not a unit and not irreducible. -/
theorem reducible_iff (f : ℤ[X]) : Reducible f ↔ f ≠ 0 ∧ ¬IsUnit f ∧ ¬Irreducible f := by
  constructor
  · rintro ⟨hf, g, h, hg, hh, rfl⟩
    refine ⟨hf, fun hu => hg (isUnit_of_mul_isUnit_left hu), fun hi => ?_⟩
    rcases hi.isUnit_or_isUnit rfl with hu | hu
    · exact hg hu
    · exact hh hu
  · rintro ⟨hf, hu, hi⟩
    refine ⟨hf, ?_⟩
    rw [irreducible_iff] at hi
    push Not at hi
    obtain ⟨g, h, he, hg, hh⟩ := hi hu
    exact ⟨g, h, hg, hh, he⟩

/-- On polynomials of positive degree, reducibility is exactly failure of irreducibility. -/
theorem reducible_iff_not_irreducible {f : ℤ[X]} (hf : 0 < f.natDegree) :
    Reducible f ↔ ¬Irreducible f := by
  rw [reducible_iff]
  have h0 : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hf
  have hu : ¬IsUnit f := Polynomial.not_isUnit_of_natDegree_pos f hf
  simp only [h0, hu, not_false_eq_true, ne_eq, true_and]

/-- Codes of irreducible polynomials of `ℤ[X]`. -/
def IrredLang : Language := {x | ∃ f : ℤ[X], encPoly f = x ∧ Irreducible f}

/-- Codes of reducible polynomials of `ℤ[X]`. -/
def RedLang : Language := {x | ∃ f : ℤ[X], encPoly f = x ∧ Reducible f}

/-- The code of `f` is in `IrredLang` iff `f` is irreducible. -/
theorem encPoly_mem_IrredLang_iff (f : ℤ[X]) : encPoly f ∈ IrredLang ↔ Irreducible f := by
  constructor
  · rintro ⟨g, hg, hi⟩
    rwa [← encPoly_injective hg]
  · intro h
    exact ⟨f, rfl, h⟩

/-- The code of `f` is in `RedLang` iff `f` is reducible. -/
theorem encPoly_mem_RedLang_iff (f : ℤ[X]) : encPoly f ∈ RedLang ↔ Reducible f := by
  constructor
  · rintro ⟨g, hg, hi⟩
    rwa [← encPoly_injective hg]
  · intro h
    exact ⟨f, rfl, h⟩

/-- Non-codes are not in `IrredLang`. -/
theorem not_mem_IrredLang_of_decodePoly_eq_none {x : List Bool} (hx : decodePoly x = none) :
    x ∉ IrredLang := by
  rintro ⟨f, hf, -⟩
  rw [decodePoly_eq_some_iff.2 hf] at hx
  exact Option.some_ne_none _ hx

/-- Non-codes are not in `RedLang`. -/
theorem not_mem_RedLang_of_decodePoly_eq_none {x : List Bool} (hx : decodePoly x = none) :
    x ∉ RedLang := by
  rintro ⟨f, hf, -⟩
  rw [decodePoly_eq_some_iff.2 hf] at hx
  exact Option.some_ne_none _ hx

end SparseIrred
