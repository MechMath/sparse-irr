import SparseIrred.UpperBounds.FactorStatistic
import SparseIrred.UpperBounds.IntegerMahlerBounds
import Mathlib.RingTheory.Radical.Basic
import Mathlib.FieldTheory.Perfect

/-!
# The actual integer factor family

The factors and multiplicities in Section 2 of the standalone prime-counting note
are taken from the normalized factorization of the input in `ℤ[X]`. For primitive
inputs these factors are primitive and remain irreducible over `ℚ`. Their weighted
degree budget and the Mahler bound for their distinct-factor product are proved
from this factorization, rather than supplied as hypotheses.
-/

namespace SparseIrred.UpperBounds

open Polynomial UniqueFactorizationMonoid

noncomputable local instance (priority := 10000) rationalFieldDecidableEq : DecidableEq ℚ :=
  Classical.decEq ℚ

local instance (priority := 10000) rationalFieldSemiring : Semiring ℚ :=
  Rat.instField.toSemifield.toDivisionSemiring.toSemiring

local instance (priority := 10000) rationalFieldCommSemiring : CommSemiring ℚ :=
  Rat.instField.toCommRing.toCommSemiring

local instance (priority := 10000) rationalFieldRing : Ring ℚ :=
  Rat.instField.toDivisionRing.toRing

local instance (priority := 10000) rationalFieldCommRing : CommRing ℚ :=
  Rat.instField.toCommRing

local instance (priority := 10000) rationalFieldNonAssocRing : NonAssocRing ℚ :=
  Ring.toNonAssocRing

local instance (priority := 10000) rationalFieldCommGroupWithZero : CommGroupWithZero ℚ :=
  Rat.instField.toSemifield.toCommGroupWithZero

/-- The distinct normalized integer factors of the input. -/
noncomputable def integerFactors (f : ℤ[X]) : Finset ℤ[X] := by
  classical
  exact (normalizedFactors f).toFinset

/-- The multiplicity in the actual normalized integer factorization. -/
noncomputable def integerFactorMultiplicity (f h : ℤ[X]) : ℕ := by
  classical
  exact (normalizedFactors f).count h

/-- The weight is one, with one extra copy for a repeated factor. -/
noncomputable def integerFactorWeight (f h : ℤ[X]) : ℕ :=
  1 + if 2 ≤ integerFactorMultiplicity f h then 1 else 0

/-- The paper's squarefree part, formed before passing to a coefficient field. -/
noncomputable def integerSquarefreePart (f : ℤ[X]) : ℤ[X] :=
  ∏ h ∈ integerFactors f, h

theorem mem_integerFactors {f h : ℤ[X]} :
    h ∈ integerFactors f ↔ h ∈ normalizedFactors f := by
  classical
  simp only [integerFactors, Multiset.mem_toFinset]

theorem integerFactor_irreducible {f h : ℤ[X]} (hh : h ∈ integerFactors f) :
    Irreducible h :=
  irreducible_of_normalized_factor h (mem_integerFactors.mp hh)

theorem integerFactor_dvd {f h : ℤ[X]} (hh : h ∈ integerFactors f) : h ∣ f :=
  dvd_of_mem_normalizedFactors (mem_integerFactors.mp hh)

theorem integerFactor_primitive {f h : ℤ[X]} (hf : f.IsPrimitive)
    (hh : h ∈ integerFactors f) : h.IsPrimitive :=
  isPrimitive_of_dvd hf (integerFactor_dvd hh)

theorem integerFactor_rational_irreducible {f h : ℤ[X]} (hf : f.IsPrimitive)
    (hh : h ∈ integerFactors f) : Irreducible (h.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (integerFactor_primitive hf hh)).mp (integerFactor_irreducible hh)

theorem integerFactor_natDegree_pos {f h : ℤ[X]} (hf : f.IsPrimitive)
    (hh : h ∈ integerFactors f) : 0 < h.natDegree := by
  simpa only [natDegree_map_eq_of_injective
    (RingHom.injective_int (Int.castRingHom ℚ))] using
    (integerFactor_rational_irreducible hf hh).natDegree_pos

/-- Distinct normalized integer factors remain relatively prime over `ℚ`. -/
theorem integerFactors_rational_coprime {f h k : ℤ[X]} (hf : f.IsPrimitive)
    (hh : h ∈ integerFactors f) (hk : k ∈ integerFactors f) (hne : h ≠ k) :
    IsCoprime (h.map (Int.castRingHom ℚ)) (k.map (Int.castRingHom ℚ)) := by
  apply (integerFactor_rational_irreducible hf hh).coprime_iff_not_dvd.mpr
  intro hd
  have hi : h ∣ k :=
    (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast h k
      (integerFactor_primitive hf hh)).mpr hd
  exact hne (mem_normalizedFactors_eq_of_associated (mem_integerFactors.mp hh)
    (mem_integerFactors.mp hk)
    ((integerFactor_irreducible hh).associated_of_dvd (integerFactor_irreducible hk) hi))

theorem integerFactor_rational_separable {f h : ℤ[X]} (hf : f.IsPrimitive)
    (hh : h ∈ integerFactors f) : (h.map (Int.castRingHom ℚ)).Separable :=
  PerfectField.separable_of_irreducible (integerFactor_rational_irreducible hf hh)

theorem integerFactorMultiplicity_pos {f h : ℤ[X]} (hh : h ∈ integerFactors f) :
    0 < integerFactorMultiplicity f h := by
  classical
  exact Multiset.count_pos.mpr (mem_integerFactors.mp hh)

theorem integerFactorWeight_bounds (f h : ℤ[X]) :
    1 ≤ integerFactorWeight f h ∧ integerFactorWeight f h ≤ 2 := by
  unfold integerFactorWeight
  split_ifs <;> omega

theorem integerFactorWeight_le_multiplicity {f h : ℤ[X]}
    (hh : h ∈ integerFactors f) :
    integerFactorWeight f h ≤ integerFactorMultiplicity f h := by
  have := integerFactorMultiplicity_pos hh
  unfold integerFactorWeight
  split_ifs <;> omega

/-- The product including multiplicities equals the input up to its unit factor. -/
theorem integerFactorization_associated (f : ℤ[X]) (hf : f ≠ 0) :
    Associated (∏ h ∈ integerFactors f, h ^ integerFactorMultiplicity f h) f := by
  classical
  unfold integerFactors integerFactorMultiplicity
  rw [← Finset.prod_multiset_count]
  exact prod_normalizedFactors hf

/-- Multiplicities recover exactly the degree of the input. -/
theorem integerFactorMultiplicity_degree_sum (f : ℤ[X]) (hf : f ≠ 0) :
    (∑ h ∈ integerFactors f, integerFactorMultiplicity f h * h.natDegree) =
      f.natDegree := by
  classical
  calc
    _ = ((normalizedFactors f).map natDegree).sum := by
      simpa [integerFactors, integerFactorMultiplicity, nsmul_eq_mul] using
        (Finset.sum_multiset_map_count (normalizedFactors f) natDegree).symm
    _ = (normalizedFactors f).prod.natDegree :=
      (natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)).symm
    _ = f.natDegree :=
      natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hf))

/-- The degree budget `∑ w_i d_i ≤ n` for the actual factor family. -/
theorem integerFactorWeight_degree_sum_le (f : ℤ[X]) (hf : f ≠ 0) :
    (∑ h ∈ integerFactors f, integerFactorWeight f h * h.natDegree) ≤ f.natDegree := by
  calc
    _ ≤ ∑ h ∈ integerFactors f, integerFactorMultiplicity f h * h.natDegree := by
      exact Finset.sum_le_sum fun h hh ↦
        Nat.mul_le_mul_right h.natDegree (integerFactorWeight_le_multiplicity hh)
    _ = f.natDegree := integerFactorMultiplicity_degree_sum f hf

/-- The sum of weights is the factor statistic on the integer factor multiset. -/
theorem integerFactorWeight_sum (f : ℤ[X]) :
    (∑ h ∈ integerFactors f, integerFactorWeight f h) =
      multiplicityStatistic (normalizedFactors f) := by
  classical
  change (∑ h ∈ (normalizedFactors f).toFinset,
    (1 + if 2 ≤ (normalizedFactors f).count h then 1 else 0)) = _
  simp [multiplicityStatistic, Finset.sum_add_distrib, Finset.sum_boole]

/-- Normalization over `ℚ` does not identify two distinct primitive factors. -/
theorem integerFactors_normalize_rational_injOn (f : ℤ[X]) (hf : f.IsPrimitive) :
    Set.InjOn (fun h : ℤ[X] ↦ normalize (h.map (Int.castRingHom ℚ)))
      {h | h ∈ normalizedFactors f} := by
  intro h hh k hk he
  have ha : Associated (h.map (Int.castRingHom ℚ)) (k.map (Int.castRingHom ℚ)) :=
    normalize_eq_normalize_iff_associated.mp he
  have hp := integerFactor_primitive hf (mem_integerFactors.mpr hh)
  have kp := integerFactor_primitive hf (mem_integerFactors.mpr hk)
  exact mem_normalizedFactors_eq_of_associated hh hk (associated_of_dvd_dvd
    ((Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast h k hp).mpr ha.dvd)
    ((Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast k h kp).mpr ha.dvd'))

/-- The rational factor multiset is the image of the actual integer one. -/
theorem integer_normalizedFactors_map_rational (f : ℤ[X]) (hf : f.IsPrimitive) :
    normalizedFactors (f.map (Int.castRingHom ℚ)) =
      (normalizedFactors f).map (fun h ↦ normalize (h.map (Int.castRingHom ℚ))) := by
  have ha := (prod_normalizedFactors hf.ne_zero).map
    (Polynomial.mapRingHom (Int.castRingHom ℚ))
  change Associated ((normalizedFactors f).prod.map (Int.castRingHom ℚ))
    (f.map (Int.castRingHom ℚ)) at ha
  rw [Polynomial.map_multiset_prod] at ha
  rw [← ha.normalizedFactors_eq, normalizedFactors_prod_eq]
  · simp only [Multiset.map_map, Function.comp_def]
  · intro q hq
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hq
    exact integerFactor_rational_irreducible hf (mem_integerFactors.mpr hh)

private theorem multiplicityStatistic_eq_sum {γ : Type*} [DecidableEq γ] (t : Multiset γ) :
    multiplicityStatistic t = ∑ a ∈ t.toFinset, (1 + if 2 ≤ t.count a then 1 else 0) := by
  simp [multiplicityStatistic, Finset.sum_add_distrib, Finset.sum_boole]

private theorem multiplicityStatistic_map_injOn {α β : Type*} [DecidableEq α]
    [DecidableEq β] (s : Multiset α) (g : α → β)
    (hg : Set.InjOn g {a | a ∈ s}) :
    multiplicityStatistic (s.map g) = multiplicityStatistic s := by
  rw [multiplicityStatistic_eq_sum, multiplicityStatistic_eq_sum, Multiset.toFinset_map,
    Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Multiset.count_map_eq_count g s hg a (Multiset.mem_toFinset.mp ha)]
  · intro a ha b hb he
    exact hg (Multiset.mem_toFinset.mp ha) (Multiset.mem_toFinset.mp hb) he

set_option maxHeartbeats 4000000 in
/-- The actual integer weights sum to the existing rational factor statistic. -/
theorem integerFactorWeight_sum_eq_factorStatistic (f : ℤ[X]) (hf : f.IsPrimitive) :
    (∑ h ∈ integerFactors f, integerFactorWeight f h) =
      factorStatistic (f.map (Int.castRingHom ℚ)) := by
  classical
  calc
    _ = multiplicityStatistic (normalizedFactors f) := integerFactorWeight_sum f
    _ = multiplicityStatistic ((normalizedFactors f).map
        (fun h ↦ normalize (h.map (Int.castRingHom ℚ)))) :=
      (multiplicityStatistic_map_injOn _ _
        (integerFactors_normalize_rational_injOn f hf)).symm
    _ = multiplicityStatistic (normalizedFactors (f.map (Int.castRingHom ℚ))) :=
      congrArg multiplicityStatistic (integer_normalizedFactors_map_rational f hf).symm
    _ = _ := by
      unfold factorStatistic rationalFieldCommRing rationalFieldCommGroupWithZero
      rfl

theorem integerSquarefreePart_eq_radical (f : ℤ[X]) :
    integerSquarefreePart f = radical f := by
  simp only [integerSquarefreePart, integerFactors, toFinset_normalizedFactors, radical,
    id_eq]

theorem integerSquarefreePart_dvd (f : ℤ[X]) : integerSquarefreePart f ∣ f := by
  rw [integerSquarefreePart_eq_radical]
  exact radical_dvd_self

theorem integerSquarefreePart_ne_zero (f : ℤ[X]) : integerSquarefreePart f ≠ 0 := by
  rw [integerSquarefreePart_eq_radical]
  exact radical_ne_zero

theorem integerSquarefreePart_squarefree (f : ℤ[X]) :
    Squarefree (integerSquarefreePart f) := by
  rw [integerSquarefreePart_eq_radical]
  exact squarefree_radical

theorem integerSquarefreePart_primitive (f : ℤ[X]) (hf : f.IsPrimitive) :
    (integerSquarefreePart f).IsPrimitive :=
  isPrimitive_of_dvd hf (integerSquarefreePart_dvd f)

/-- In characteristic zero the actual squarefree part is separable. -/
theorem integerSquarefreePart_rational_separable (f : ℤ[X]) (hf : f.IsPrimitive) :
    ((integerSquarefreePart f).map (Int.castRingHom ℚ)).Separable := by
  classical
  rw [integerSquarefreePart, Polynomial.map_prod]
  exact separable_prod' (fun _ hh _ hk hne ↦ integerFactors_rational_coprime hf hh hk hne)
    (fun _ hh ↦ integerFactor_rational_separable hf hh)

theorem integerSquarefreePart_natDegree_le (f : ℤ[X]) (hf : f ≠ 0) :
    (integerSquarefreePart f).natDegree ≤ f.natDegree :=
  natDegree_le_of_dvd (integerSquarefreePart_dvd f) hf

/-- The Mahler bound for `F` follows from its proved divisibility into the input. -/
theorem integerSquarefreePart_mahler_bounds (f : ℤ[X]) (hf : f ≠ 0) :
    1 ≤ (integerSquarefreePart f).mapMahlerMeasure (Int.castRingHom ℂ) ∧
      (integerSquarefreePart f).mapMahlerMeasure (Int.castRingHom ℂ) ≤
        (integerL1 f : ℝ) := by
  obtain ⟨h₁, h₂, h₃⟩ := integer_divisor_mahler_bounds f (integerSquarefreePart f) hf
    (integerSquarefreePart_dvd f)
  exact ⟨h₁, h₂.trans h₃⟩

theorem integerFactor_mahler_bounds {f h : ℤ[X]} (hf : f ≠ 0)
    (hh : h ∈ integerFactors f) :
    1 ≤ h.mapMahlerMeasure (Int.castRingHom ℂ) ∧
      h.mapMahlerMeasure (Int.castRingHom ℂ) ≤ (integerL1 f : ℝ) := by
  obtain ⟨h₁, h₂, h₃⟩ := integer_divisor_mahler_bounds f h hf (integerFactor_dvd hh)
  exact ⟨h₁, h₂.trans h₃⟩

end SparseIrred.UpperBounds
