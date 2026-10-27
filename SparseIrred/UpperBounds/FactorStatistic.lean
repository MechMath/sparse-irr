import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-!
# The factor statistic detecting repeated irreducible factors

Section 3.2 of `1021-AI4Math_Irreducibility.pdf` counts every distinct irreducible factor
once, and every repeated factor a second time. The statistic below uses the actual
normalized factorization, including multiplicities; squarefreeness is not an assumption.
-/

namespace SparseIrred.UpperBounds

open Polynomial UniqueFactorizationMonoid

/-- Number of distinct factors plus number of factors occurring at least twice. -/
def multiplicityStatistic {α : Type*} [DecidableEq α] (s : Multiset α) : ℕ :=
  s.toFinset.card + (s.toFinset.filter fun a ↦ 2 ≤ s.count a).card

@[simp]
theorem multiplicityStatistic_zero {α : Type*} [DecidableEq α] :
    multiplicityStatistic (0 : Multiset α) = 0 := by
  simp [multiplicityStatistic]

@[simp]
theorem multiplicityStatistic_singleton {α : Type*} [DecidableEq α] (a : α) :
    multiplicityStatistic ({a} : Multiset α) = 1 := by
  simp [multiplicityStatistic]

/-- Each factor receives weight at most its multiplicity. -/
theorem multiplicityStatistic_le_card {α : Type*} [DecidableEq α] (s : Multiset α) :
    multiplicityStatistic s ≤ s.card := by
  classical
  calc
    multiplicityStatistic s = ∑ a ∈ s.toFinset, (1 + if 2 ≤ s.count a then 1 else 0) := by
      simp [multiplicityStatistic, Finset.sum_add_distrib, Finset.sum_boole]
    _ ≤ ∑ a ∈ s.toFinset, s.count a := by
      apply Finset.sum_le_sum
      intro a ha
      have hp := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp ha)
      split_ifs <;> omega
    _ = s.card := Multiset.toFinset_sum_count_eq _

theorem multiplicityStatistic_pos_iff {α : Type*} [DecidableEq α] (s : Multiset α) :
    0 < multiplicityStatistic s ↔ s ≠ 0 := by
  constructor
  · intro h he
    simp [he] at h
  · intro h
    have hc : 0 < s.toFinset.card := by simpa using h
    unfold multiplicityStatistic
    omega

/-- The repeated-factor correction rules out powers of a single irreducible factor. -/
theorem multiplicityStatistic_eq_one_iff {α : Type*} [DecidableEq α] (s : Multiset α) :
    multiplicityStatistic s = 1 ↔ s.card = 1 := by
  classical
  constructor
  · intro hs
    have hn : s ≠ 0 := by
      intro h
      simp [h] at hs
    have hc : s.toFinset.card = 1 := by
      have hp : 0 < s.toFinset.card := by simpa using hn
      unfold multiplicityStatistic at hs
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hr : s = Multiset.replicate s.card a := by
      apply Multiset.eq_replicate_of_mem
      intro b hb
      have : b ∈ s.toFinset := Multiset.mem_toFinset.mpr hb
      simpa [ha] using this
    have hcount : s.count a = s.card := by
      calc
        s.count a = (Multiset.replicate s.card a).count a := congrArg (Multiset.count a) hr
        _ = s.card := Multiset.count_replicate_self _ _
    have hlt : s.card < 2 := by
      by_contra h
      have hm : a ∈ s.toFinset.filter fun b ↦ 2 ≤ s.count b := by
        simp [ha, hcount, Nat.le_of_not_gt h]
      have hp := Finset.card_pos.mpr ⟨a, hm⟩
      unfold multiplicityStatistic at hs
      omega
    have hp := Multiset.card_pos.mpr hn
    omega
  · intro hs
    obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hs
    simp

/-- The paper's `ρ(f)`, with the normalized factor multiset over the coefficient field. -/
noncomputable def factorStatistic {K : Type*} [Field K] (f : K[X]) : ℕ := by
  classical
  exact multiplicityStatistic (normalizedFactors f)

/-- The bounds `1 ≤ ρ(f) ≤ deg f` for nonconstant polynomials. -/
theorem factorStatistic_bounds {K : Type*} [Field K] (f : K[X]) (hf : 0 < f.natDegree) :
    1 ≤ factorStatistic f ∧ factorStatistic f ≤ f.natDegree := by
  classical
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  have hnu : ¬IsUnit f := by
    intro hu
    have := natDegree_eq_zero_of_isUnit hu
    omega
  refine ⟨?_, ?_⟩
  · apply (multiplicityStatistic_pos_iff _).mpr
    exact (normalizedFactors_eq_zero_iff hf0).not.mpr hnu
  · calc
      factorStatistic f ≤ (normalizedFactors f).card := multiplicityStatistic_le_card _
      _ ≤ ((normalizedFactors f).map natDegree).sum := by
        have hdeg : ∀ d ∈ (normalizedFactors f).map natDegree, 1 ≤ d := by
          intro d hd
          obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hd
          exact (irreducible_of_normalized_factor g hg).natDegree_pos
        simpa using Multiset.card_nsmul_le_sum hdeg
      _ = (normalizedFactors f).prod.natDegree :=
        (natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)).symm
      _ = f.natDegree :=
        natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hf0))

/-- Equation (33), without any squarefreeness or nonzero-constant-term assumption. -/
theorem factorStatistic_eq_one_iff {K : Type*} [Field K] (f : K[X]) (hf : f ≠ 0) :
    factorStatistic f = 1 ↔ Irreducible f := by
  classical
  rw [factorStatistic, multiplicityStatistic_eq_one_iff]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
    have hirr : Irreducible a :=
      irreducible_of_normalized_factor (a := f) a (by rw [ha]; simp)
    have hassoc := prod_normalizedFactors hf
    rw [ha, Multiset.prod_singleton] at hassoc
    exact hassoc.irreducible_iff.mp hirr
  · intro h
    simp [normalizedFactors_irreducible h]

/-- Gauss's lemma transfers the criterion to a primitive integer polynomial. -/
theorem integer_factorStatistic_eq_one_iff (f : ℤ[X]) (hf : f.IsPrimitive) :
    factorStatistic (f.map (Int.castRingHom ℚ)) = 1 ↔ Irreducible f := by
  rw [factorStatistic_eq_one_iff _
    ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hf.ne_zero)]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hf).symm

end SparseIrred.UpperBounds
