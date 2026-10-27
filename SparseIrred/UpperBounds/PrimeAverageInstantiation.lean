import SparseIrred.UpperBounds.PrimeAverage
import SparseIrred.UpperBounds.IntegerFactorFamily
import SparseIrred.UpperBounds.PolynomialRootField
import SparseIrred.UpperBounds.DegreeOneCounting
import SparseIrred.UpperBounds.ExternalPrimeIdealEstimate
import SparseIrred.UpperBounds.VandermondeDiscriminant
import SparseIrred.UpperBounds.PowerBasisDiscriminant
import SparseIrred.UpperBounds.GoodReductionRoots
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Instantiating the prime-root average with the actual factor fields

The finite family consists of the normalized integer factors of the input, with
their proved weights and their concrete scaled root fields. The degree budgets,
degree-one summation identity, and higher-residue-degree bound are derived for
this family. The final estimate retains the good-prime identity, exceptional
prime budget, and field-discriminant budget as explicit algebraic hypotheses.
-/

namespace SparseIrred.UpperBounds

open Polynomial NumberField
open scoped BigOperators

/-- The finite index type of actual normalized integer factors. -/
abbrev IntegerFactorIndex (f : ℤ[X]) := ↥(integerFactors f)

/-- The concrete scaled root field associated to an actual integer factor. -/
abbrev IntegerFactorRootField (f : ℤ[X]) (hf : f.IsPrimitive)
    (i : IntegerFactorIndex f) : Type :=
  PolynomialRootField i.val (integerFactor_natDegree_pos hf i.prop)
    (integerFactor_rational_irreducible hf i.prop)

theorem integerFactorRootField_finrank (f : ℤ[X]) (hf : f.IsPrimitive)
    (i : IntegerFactorIndex f) :
    Module.finrank ℚ (IntegerFactorRootField f hf i) = i.val.natDegree :=
  polynomialRootField_finrank _ _ _

/-- The finite family has exactly the rational factor statistic as total weight. -/
theorem integerFactorIndex_weight_sum (f : ℤ[X]) (hf : f.IsPrimitive) :
    (∑ i : IntegerFactorIndex f, integerFactorWeight f i.val) =
      factorStatistic (f.map (Int.castRingHom ℚ)) := by
  classical
  simpa only [IntegerFactorIndex, Finset.sum_coe_sort] using
    integerFactorWeight_sum_eq_factorStatistic f hf

/-- The actual field degrees satisfy the degree budget required by the average. -/
theorem integerFactorIndex_weighted_finrank_sum_le (f : ℤ[X]) (hf : f.IsPrimitive) :
    (∑ i : IntegerFactorIndex f,
      integerFactorWeight f i.val * Module.finrank ℚ (IntegerFactorRootField f hf i)) ≤
        f.natDegree := by
  classical
  simp_rw [integerFactorRootField_finrank]
  simp only [IntegerFactorIndex]
  rw [← Finset.sum_subtype (integerFactors f) (by simp)
    (fun h ↦ integerFactorWeight f h * h.natDegree)]
  exact integerFactorWeight_degree_sum_le f hf.ne_zero

/-- Positive degrees also bound the total weight by the input degree. -/
theorem integerFactorIndex_weight_sum_le (f : ℤ[X]) (hf : f.IsPrimitive) :
    (∑ i : IntegerFactorIndex f, integerFactorWeight f i.val) ≤ f.natDegree := by
  calc
    _ ≤ ∑ i : IntegerFactorIndex f, integerFactorWeight f i.val *
        Module.finrank ℚ (IntegerFactorRootField f hf i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [integerFactorRootField_finrank]
      exact Nat.le_mul_of_pos_right _ (integerFactor_natDegree_pos hf i.prop)
    _ ≤ _ := integerFactorIndex_weighted_finrank_sum_le f hf

/-- The distinct-factor product has positive degree when the input does. -/
theorem integerSquarefreePart_natDegree_pos (f : ℤ[X]) (hf : f.IsPrimitive)
    (hdegree : 1 ≤ f.natDegree) :
    1 ≤ (integerSquarefreePart f).natDegree := by
  classical
  have hsum := integerFactorMultiplicity_degree_sum f hf.ne_zero
  have hne : (integerFactors f).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty] at hsum
    omega
  obtain ⟨h, hh⟩ := hne
  have hhd := integerFactor_natDegree_pos hf hh
  have hdiv : h ∣ integerSquarefreePart f := by
    unfold integerSquarefreePart
    exact Finset.dvd_prod_of_mem _ hh
  have hF0 := integerSquarefreePart_ne_zero f
  have hle := natDegree_le_of_dvd hdiv hF0
  omega

/-- Separability of the actual squarefree part survives its embedding in `ℂ`. -/
theorem integerSquarefreePart_complex_separable (f : ℤ[X]) (hf : f.IsPrimitive) :
    ((integerSquarefreePart f).map (Int.castRingHom ℂ)).Separable := by
  have hq := integerSquarefreePart_rational_separable f hf
  have hc := hq.map (f := Rat.castHom ℂ)
  have hcomp : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) =
      Int.castRingHom ℂ := by
    ext z
    simp
  simpa only [Polynomial.map_map, hcomp] using hc

/-- The actual exceptional set attached to the distinct-factor product. -/
noncomputable def integerSquarefreeExceptionalPrimes (f : ℤ[X]) : Finset ℕ :=
  (exceptionalInteger (integerSquarefreePart f)).natAbs.primeFactors

/-- The constructed exceptional set has the Proposition 4.1 cardinality budget. -/
theorem integerSquarefreeExceptionalPrimes_card_le (f : ℤ[X]) (hf : f.IsPrimitive)
    (hdegree : 1 ≤ f.natDegree) :
    (integerSquarefreeExceptionalPrimes f).card ≤
      2 * f.natDegree * inputDelta f := by
  exact exceptionalInteger_primeFactors_card_le_of_dvd f (integerSquarefreePart f)
    hf.ne_zero (integerSquarefreePart_dvd f)
    (integerSquarefreePart_natDegree_pos f hf hdegree)
    (integerSquarefreePart_complex_separable f hf)

/-- A prime outside the constructed exceptional set does not divide the
distinct-factor exceptional integer. -/
theorem not_dvd_integerSquarefreeExceptionalInteger_of_not_mem
    (f : ℤ[X]) (hf : f.IsPrimitive) (p : ℕ) (hp : p.Prime)
    (hnot : p ∉ integerSquarefreeExceptionalPrimes f) :
    ¬(p : ℤ) ∣ exceptionalInteger (integerSquarefreePart f) := by
  intro hdiv
  have hdivNat : p ∣ (exceptionalInteger (integerSquarefreePart f)).natAbs :=
    Int.natCast_dvd.mp hdiv
  have hnonzero : (exceptionalInteger (integerSquarefreePart f)).natAbs ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr
      (exceptionalInteger_ne_zero (integerSquarefreePart f)
        (integerSquarefreePart_complex_separable f hf))
  apply hnot
  exact Nat.mem_primeFactors.mpr ⟨hp, hdivNat, hnonzero⟩

private theorem polynomial_discr_map_of_leadingCoeff_ne_zero
    {K : Type*} [Field K] (g : ℤ[X]) (φ : ℤ →+* K)
    (hdegree : 0 < g.degree) (hlc : φ g.leadingCoeff ≠ 0) :
    (g.map φ).discr = φ g.discr := by
  have hnat : 0 < g.natDegree := natDegree_pos_iff_degree_pos.mpr hdegree
  have hnat' : 0 < (g.map φ).natDegree := by
    rw [natDegree_map_of_leadingCoeff_ne_zero φ hlc]
    exact hnat
  have hdegree' : 0 < (g.map φ).degree :=
    natDegree_pos_iff_degree_pos.mp hnat'
  have hr := resultant_deriv (f := g) hdegree
  have hr' := resultant_deriv (f := g.map φ) hdegree'
  have hmap :
      resultant (g.map φ) (g.map φ).derivative (g.map φ).natDegree
          ((g.map φ).natDegree - 1) =
        φ (resultant g g.derivative g.natDegree (g.natDegree - 1)) := by
    rw [Polynomial.derivative_map, ← resultant_map_map]
    rw [natDegree_map_of_leadingCoeff_ne_zero φ hlc]
  rw [hmap] at hr'
  rw [natDegree_map_of_leadingCoeff_ne_zero φ hlc] at hr'
  have hm := congrArg φ hr
  rw [leadingCoeff_map_of_leadingCoeff_ne_zero φ hlc] at hr'
  simp only [map_mul, map_pow, map_neg, map_one] at hm
  have hs : (-1 : K) ^ (g.natDegree * (g.natDegree - 1) / 2) ≠ 0 := by
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hslc :
      (-1 : K) ^ (g.natDegree * (g.natDegree - 1) / 2) * φ g.leadingCoeff ≠ 0 :=
    mul_ne_zero hs hlc
  apply (mul_left_cancel₀ hslc)
  calc
    ((-1 : K) ^ (g.natDegree * (g.natDegree - 1) / 2) * φ g.leadingCoeff) *
          (g.map φ).discr =
        φ (resultant g g.derivative g.natDegree (g.natDegree - 1)) := by
      simpa only [mul_assoc] using hr'.symm
    _ = ((-1 : K) ^ (g.natDegree * (g.natDegree - 1) / 2) *
          φ g.leadingCoeff) * φ g.discr := by
      simpa only [mul_assoc] using hm

private theorem polynomial_discr_ne_zero_of_separable
    {K : Type*} [Field K] (g : K[X]) (hdegree : 0 < g.degree)
    (hlc : g.leadingCoeff ≠ 0) (hsep : g.Separable) : g.discr ≠ 0 := by
  have hnat : 0 < g.natDegree := natDegree_pos_iff_degree_pos.mpr hdegree
  have hg0 : g ≠ 0 := ne_zero_of_natDegree_gt hnat
  have hcop : IsCoprime g g.derivative := (Polynomial.separable_def g).mp hsep
  have hres : resultant g g.derivative ≠ 0 := by
    intro hz
    exact ((Polynomial.resultant_eq_zero_iff).mp hz).2 hcop
  have hn := natDegree_derivative_le g
  let k := g.natDegree - 1 - g.derivative.natDegree
  have hk : g.derivative.natDegree + k = g.natDegree - 1 := by
    dsimp [k]
    omega
  have hfixed := resultant_add_right_deg g g.derivative g.natDegree
    g.derivative.natDegree k
    (le_rfl : g.derivative.natDegree ≤ g.derivative.natDegree)
  rw [hk] at hfixed
  have hcoeff : g.coeff g.natDegree ^ k ≠ 0 := by
    rw [coeff_natDegree]
    exact pow_ne_zero _ hlc
  have hresfixed : resultant g g.derivative g.natDegree (g.natDegree - 1) ≠ 0 := by
    intro hz
    have hres' : resultant g g.derivative g.natDegree g.derivative.natDegree ≠ 0 := hres
    have hrhs : g.coeff g.natDegree ^ k *
        resultant g g.derivative g.natDegree g.derivative.natDegree ≠ 0 :=
      mul_ne_zero hcoeff hres'
    rw [hz] at hfixed
    exact hrhs hfixed.symm
  intro hdisc
  apply hresfixed
  rw [resultant_deriv hdegree]
  simp [hdisc]

/-- Away from the leading coefficient and discriminant, the reduction of the
actual distinct-factor product remains separable. -/
theorem integerSquarefreePart_good_prime_separable (f : ℤ[X]) (p : ℕ)
    (hf : f.IsPrimitive) (hdegree : 1 ≤ f.natDegree) [Fact p.Prime]
    (hgood : ¬(p : ℤ) ∣ exceptionalInteger (integerSquarefreePart f)) :
    ((integerSquarefreePart f).map (Int.castRingHom (ZMod p))).Separable := by
  classical
  let F := integerSquarefreePart f
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let G := F.map φ
  have hFdegree : 0 < F.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    exact integerSquarefreePart_natDegree_pos f hf hdegree
  have hbad : φ (F.leadingCoeff * F.discr) ≠ 0 := by
    intro hz
    apply hgood
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hbad' : φ F.leadingCoeff * φ F.discr ≠ 0 := by
    simpa only [map_mul] using hbad
  have hlc : φ F.leadingCoeff ≠ 0 := (mul_ne_zero_iff.mp hbad').1
  have hdisc : φ F.discr ≠ 0 := (mul_ne_zero_iff.mp hbad').2
  have hGdegree : G.natDegree = F.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero φ hlc
  have hresF := Polynomial.resultant_deriv (f := F) hFdegree
  have htrans :
      resultant G G.derivative F.natDegree (F.natDegree - 1) =
        φ (resultant F F.derivative F.natDegree (F.natDegree - 1)) := by
    dsimp [G]
    rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
  have hresmap := congrArg φ hresF
  have hneg : φ (-1 : ℤ) ≠ 0 := by
    change ((-1 : ℤ) : ZMod p) ≠ 0
    simpa using (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0))
  have hsign : φ ((-1 : ℤ) ^ (F.natDegree * (F.natDegree - 1) / 2)) ≠ 0 := by
    simpa only [map_pow] using
      (pow_ne_zero (F.natDegree * (F.natDegree - 1) / 2) hneg)
  have hresvalue :
      φ ((-1 : ℤ) ^ (F.natDegree * (F.natDegree - 1) / 2) *
        F.leadingCoeff * F.discr) ≠ 0 := by
    simpa only [map_mul] using mul_ne_zero (mul_ne_zero hsign hlc) hdisc
  have hresG : resultant G G.derivative G.natDegree (G.natDegree - 1) ≠ 0 := by
    rw [hGdegree, htrans, hresmap]
    exact hresvalue
  have hdefault : resultant G G.derivative ≠ 0 := by
    intro hz
    have hn := natDegree_derivative_le G
    let k := G.natDegree - 1 - G.derivative.natDegree
    have hk : G.derivative.natDegree + k = G.natDegree - 1 := by
      dsimp [k]
      omega
    have hfixed := resultant_add_right_deg G G.derivative G.natDegree
      G.derivative.natDegree k
      (le_rfl : G.derivative.natDegree ≤ G.derivative.natDegree)
    rw [hk] at hfixed
    rw [hz] at hfixed
    have : resultant G G.derivative G.natDegree (G.natDegree - 1) = 0 := by
      simpa using hfixed
    exact hresG this
  have hGnat : 0 < G.natDegree := by
    rw [hGdegree]
    exact natDegree_pos_iff_degree_pos.mpr hFdegree
  have hG0 : G ≠ 0 := ne_zero_of_natDegree_gt hGnat
  have hcop : IsCoprime G G.derivative := by
    by_contra hc
    exact hdefault ((Polynomial.resultant_eq_zero_iff).2 ⟨Or.inl hG0, hc⟩)
  exact (Polynomial.separable_def G).2 hcop

/-- Every actual factor reduction is separable at a prime good for the
distinct-factor product. -/
theorem integerFactorReduction_separable (f : ℤ[X]) (hf : f.IsPrimitive)
    (hdegree : 1 ≤ f.natDegree) (p : ℕ) [Fact p.Prime]
    (hgood : ¬(p : ℤ) ∣ exceptionalInteger (integerSquarefreePart f))
    (i : IntegerFactorIndex f) :
    (i.val.map (Int.castRingHom (ZMod p))).Separable := by
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hFsep := integerSquarefreePart_good_prime_separable f p hf hdegree hgood
  have hdiv : i.val ∣ integerSquarefreePart f := by
    unfold integerSquarefreePart
    exact Finset.dvd_prod_of_mem _ i.prop
  have hdivMap := Polynomial.map_dvd φ hdiv
  exact hFsep.of_dvd (by simpa only [Polynomial.map_mul] using hdivMap)

/-- Distinct actual factor reductions are pairwise coprime at a prime good
for the distinct-factor product. -/
theorem integerFactorReduction_pairwise_coprime (f : ℤ[X])
    (hf : f.IsPrimitive) (hdegree : 1 ≤ f.natDegree) (p : ℕ) [Fact p.Prime]
    (hgood : ¬(p : ℤ) ∣ exceptionalInteger (integerSquarefreePart f)) :
    Pairwise fun i j : IntegerFactorIndex f ↦
      IsCoprime (i.val.map (Int.castRingHom (ZMod p)))
        (j.val.map (Int.castRingHom (ZMod p))) := by
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hFsep := integerSquarefreePart_good_prime_separable f p hf hdegree hgood
  intro i j hij
  have hne : i.val ≠ j.val := fun h ↦ hij (Subtype.ext h)
  have hsubset : insert i.val ({j.val} : Finset ℤ[X]) ⊆ integerFactors f := by
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with hh | hh
    · subst h
      exact i.prop
    · subst h
      exact j.prop
  have hpairDiv : i.val * j.val ∣ integerSquarefreePart f := by
    have hdvd := Finset.prod_dvd_prod_of_subset (insert i.val {j.val})
      (integerFactors f) (fun h ↦ h) hsubset
    have hprod : (∏ h ∈ insert i.val {j.val}, h) = i.val * j.val := by
      simp [hne]
    have hdvd' : i.val * j.val ∣ ∏ h ∈ integerFactors f, h := by
      rw [← hprod]
      exact hdvd
    simpa only [integerSquarefreePart] using hdvd'
  have hpairMap := Polynomial.map_dvd φ hpairDiv
  have hsep :
      ((i.val.map φ) * (j.val.map φ)).Separable :=
    hFsep.of_dvd (by simpa only [Polynomial.map_mul] using hpairMap)
  exact hsep.isCoprime

private theorem associated_rootCount_eq {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {g h : K[X]} (hgh : Associated g h) :
    rootCount g = rootCount h := by
  classical
  obtain ⟨u, hu⟩ := hgh
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hc0 : c ≠ 0 := hc.ne_zero
  have heval (x : K) : g.eval x = 0 ↔ h.eval x = 0 := by
    rw [← hu, eval_mul, ← hcu, eval_C]
    simp [hc0]
  unfold rootCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact heval x

private theorem associated_multipleRootCount_eq {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {g h : K[X]} (hgh : Associated g h) :
    multipleRootCount g = multipleRootCount h := by
  classical
  obtain ⟨u, hu⟩ := hgh
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hc0 : c ≠ 0 := hc.ne_zero
  have heval (x : K) : g.eval x = 0 ↔ h.eval x = 0 := by
    rw [← hu, eval_mul, ← hcu, eval_C]
    simp [hc0]
  have hderiv : h.derivative = g.derivative * C c := by
    calc
      h.derivative = (g * (u : K[X])).derivative := by rw [hu]
      _ = (g * C c).derivative := by rw [← hcu]
      _ = g.derivative * C c := by rw [derivative_mul, derivative_C]; simp
  have hdeval (x : K) : g.derivative.eval x = 0 ↔ h.derivative.eval x = 0 := by
    rw [hderiv, eval_mul, eval_C]
    simp [hc0]
  unfold multipleRootCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨hx, hdx⟩ ↦ ⟨(heval x).mp hx, (hdeval x).mp hdx⟩,
    fun ⟨hx, hdx⟩ ↦ ⟨(heval x).mpr hx, (hdeval x).mpr hdx⟩⟩

private theorem integerFactorization_map_associated (f : ℤ[X]) (hf : f.IsPrimitive)
    (p : ℕ) :
    Associated
      (∏ i : IntegerFactorIndex f,
        (i.val.map (Int.castRingHom (ZMod p))) ^ integerFactorMultiplicity f i.val)
      (f.map (Int.castRingHom (ZMod p))) := by
  classical
  have h := Polynomial.associated_map_map (Int.castRingHom (ZMod p))
    (integerFactorization_associated f hf.ne_zero)
  have hprod :
      (∏ h ∈ integerFactors f, h ^ integerFactorMultiplicity f h).map
          (Int.castRingHom (ZMod p)) =
        ∏ i : IntegerFactorIndex f,
          (i.val.map (Int.castRingHom (ZMod p))) ^ integerFactorMultiplicity f i.val := by
    rw [Polynomial.map_prod]
    rw [← Finset.prod_subtype (integerFactors f) (by simp)
      (fun h ↦ (h.map (Int.castRingHom (ZMod p))) ^ integerFactorMultiplicity f h)]
    simp only [Polynomial.map_pow]
  rw [← hprod]
  exact h

/-- At a prime where the distinct-factor product has separable reduction, the
root and multiple-root counters split according to the actual integer-factor
multiplicities. -/
theorem integerFactorization_good_prime_root_weight (f : ℤ[X]) (hf : f.IsPrimitive)
    (hdegree : 1 ≤ f.natDegree) (p : ℕ) [Fact p.Prime] (hp : p.Prime)
    (hgood : ¬(p : ℤ) ∣ exceptionalInteger (integerSquarefreePart f)) :
    primeRootWeight f p =
      ∑ i : IntegerFactorIndex f,
        integerFactorWeight f i.val *
          rootCount (i.val.map (Int.castRingHom (ZMod p))) := by
  classical
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let h : IntegerFactorIndex f → (ZMod p)[X] := fun i ↦ i.val.map φ
  let m : IntegerFactorIndex f → ℕ := fun i ↦ integerFactorMultiplicity f i.val
  have hm : ∀ i, 0 < m i := fun i ↦ integerFactorMultiplicity_pos i.prop
  have hcop := integerFactorReduction_pairwise_coprime f hf hdegree p hgood
  have hsep (i : IntegerFactorIndex f) : (h i).Separable := by
    simpa [h] using integerFactorReduction_separable f hf hdegree p hgood i
  have hweighted := weighted_root_count h m hm hcop hsep
  have hassoc := integerFactorization_map_associated f hf p
  have hroot := associated_rootCount_eq hassoc.symm
  have hmult := associated_multipleRootCount_eq hassoc.symm
  have hfactor (i : IntegerFactorIndex f) :
      integerFactorWeight f i.val = 1 + if 2 ≤ m i then 1 else 0 := by
    rfl
  unfold primeRootWeight
  simp only [dif_pos hp]
  rw [hroot, hmult, hweighted]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfactor i]

/-- The actual weighted degree-one prime-ideal contribution at a rational prime. -/
noncomputable def integerFactorDegreeOneWeight (f : ℤ[X]) (hf : f.IsPrimitive)
    (p : ℕ) : ℕ :=
  ∑ i : IntegerFactorIndex f,
    integerFactorWeight f i.val * degreeOnePrimesOverCount (IntegerFactorRootField f hf i) p

/-- The weighted degree-one contribution is uniformly bounded, even at bad primes. -/
theorem integerFactorDegreeOneWeight_le (f : ℤ[X]) (hf : f.IsPrimitive) (p : ℕ) :
    integerFactorDegreeOneWeight f hf p ≤ f.natDegree := by
  apply le_trans _ (integerFactorIndex_weighted_finrank_sum_le f hf)
  exact Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_left _
    (degreeOnePrimesOverCount_le (IntegerFactorRootField f hf i) p)

/-- Summing the local degree-one contributions counts the actual bounded ideals. -/
theorem integerFactorDegreeOneWeight_sum (f : ℤ[X]) (hf : f.IsPrimitive) (X : ℕ) :
    (∑ p ∈ X.primesLE, integerFactorDegreeOneWeight f hf p) =
      ∑ i : IntegerFactorIndex f, integerFactorWeight f i.val *
        degreeOnePrimeIdealCountLE (IntegerFactorRootField f hf i) X := by
  simp only [integerFactorDegreeOneWeight, degreeOnePrimeIdealCountLE_eq_sum,
    Finset.mul_sum]
  exact Finset.sum_comm

private theorem integerFactor_exceptional_not_dvd
    (f : ℤ[X]) (hf : f.IsPrimitive) (hdegree : 1 ≤ f.natDegree)
    (p : ℕ) [Fact p.Prime]
    (hgood : ¬(p : ℤ) ∣ exceptionalInteger (integerSquarefreePart f))
    (i : IntegerFactorIndex f) :
    ¬(p : ℤ) ∣ exceptionalInteger i.val := by
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let h := i.val
  let F := integerSquarefreePart f
  have hdiv : h ∣ F := by
    dsimp [F, h]
    exact Finset.dvd_prod_of_mem _ i.prop
  have hlcdvd : h.leadingCoeff ∣ F.leadingCoeff := leadingCoeff_dvd_leadingCoeff hdiv
  have hFgood_lc : ¬(p : ℤ) ∣ F.leadingCoeff := by
    intro hpF
    apply hgood
    exact dvd_mul_of_dvd_left hpF F.discr
  have hlc : ¬(p : ℤ) ∣ h.leadingCoeff := by
    intro hph
    apply hFgood_lc
    exact dvd_trans hph hlcdvd
  have hmaplc : φ h.leadingCoeff ≠ 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).not.mpr hlc
  have hmapdeg : (h.map φ).natDegree = h.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero φ hmaplc
  have hdegreeh : 0 < h.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    exact integerFactor_natDegree_pos hf i.prop
  have hseph : (h.map φ).Separable :=
    integerFactorReduction_separable f hf hdegree p hgood i
  have hcop : IsCoprime (h.map φ) (h.map φ).derivative :=
    (Polynomial.separable_def (h.map φ)).mp hseph
  have hres : (h.map φ).resultant (h.map φ).derivative ≠ 0 :=
    Polynomial.resultant_ne_zero _ _ hcop
  have hGnat : 0 < (h.map φ).natDegree := by
    rw [hmapdeg]
    exact integerFactor_natDegree_pos hf i.prop
  have hG0 : h.map φ ≠ 0 := ne_zero_of_natDegree_gt hGnat
  have hres_index : (h.map φ).resultant (h.map φ).derivative
      (h.map φ).natDegree ((h.map φ).natDegree - 1) ≠ 0 := by
    let G := h.map φ
    let k := G.natDegree - 1 - G.derivative.natDegree
    have hn := natDegree_derivative_le G
    have hk : G.derivative.natDegree + k = G.natDegree - 1 := by
      dsimp [k]
      omega
    have hpadded := resultant_add_right_deg G G.derivative G.natDegree
      G.derivative.natDegree k (le_rfl : G.derivative.natDegree ≤ G.derivative.natDegree)
    rw [hk] at hpadded
    have hcoeff : G.coeff G.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hG0
    have hrhs : G.coeff G.natDegree ^ k * G.resultant G.derivative ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hcoeff) hres
    intro hz
    rw [hz] at hpadded
    exact hrhs hpadded.symm
  have htrans : (h.map φ).resultant (h.map φ).derivative
      h.natDegree (h.natDegree - 1) =
      φ (h.resultant h.derivative h.natDegree (h.natDegree - 1)) := by
    rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
  have hres_index' : (h.map φ).resultant (h.map φ).derivative
      h.natDegree (h.natDegree - 1) ≠ 0 := by
    simpa only [hmapdeg] using hres_index
  have hresmap : φ (h.resultant h.derivative h.natDegree (h.natDegree - 1)) ≠ 0 := by
    rw [← htrans]
    exact hres_index'
  have hres_int := Polynomial.resultant_deriv (f := h) hdegreeh
  have hprod : φ (h.leadingCoeff * h.discr) ≠ 0 := by
    intro hzero
    have hzerores : φ (h.resultant h.derivative h.natDegree (h.natDegree - 1)) = 0 := by
      rw [hres_int]
      rw [show (-1 : ℤ) ^ (h.natDegree * (h.natDegree - 1) / 2) *
          h.leadingCoeff * h.discr =
          (-1 : ℤ) ^ (h.natDegree * (h.natDegree - 1) / 2) *
            (h.leadingCoeff * h.discr) by ring]
      rw [map_mul, hzero, mul_zero]
    exact hresmap hzerores
  intro hpE
  apply hprod
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpE

/-- At primes outside the constructed exceptional set, the input root weight
equals the degree-one prime-ideal contribution of its actual irreducible factors. -/
theorem integerFactorization_good_prime_root_weight_eq_degreeOne
    (f : ℤ[X]) (hf : f.IsPrimitive) (hdegree : 1 ≤ f.natDegree)
    (p : ℕ) [Fact p.Prime] (hp : p.Prime)
    (hgood : p ∉ integerSquarefreeExceptionalPrimes f) :
    primeRootWeight f p = integerFactorDegreeOneWeight f hf p := by
  have hprod (i : IntegerFactorIndex f) :
      ¬(p : ℤ) ∣ i.val.leadingCoeff * i.val.discr := by
    simpa [exceptionalInteger] using integerFactor_exceptional_not_dvd
      f hf hdegree p
      (not_dvd_integerSquarefreeExceptionalInteger_of_not_mem f hf p hp hgood) i
  have hgood_i (i : IntegerFactorIndex f) :
      ¬(p : ℤ) ∣ i.val.leadingCoeff ∧ ¬(p : ℤ) ∣ i.val.discr := by
    constructor
    · intro h
      apply hprod i
      exact dvd_mul_of_dvd_left h _
    · intro h
      apply hprod i
      exact dvd_mul_of_dvd_right h _
  rw [integerFactorization_good_prime_root_weight f hf hdegree p hp
    (not_dvd_integerSquarefreeExceptionalInteger_of_not_mem f hf p hp hgood)]
  unfold integerFactorDegreeOneWeight
  apply Finset.sum_congr rfl
  intro i hi
  rw [polynomialRoot_nonmonic_rootCount_eq_degreeOnePrimesOver
    i.val (integerFactor_natDegree_pos hf i.prop)
    (integerFactor_rational_irreducible hf i.prop) p
    (hgood_i i).1 (hgood_i i).2]
  rw [degreeOnePrimesOverCount_eq_natCard _ p hp]

/-- The logarithm of a positive natural number is bounded by the binary ceiling
logarithm used in the sparse input parameter. -/
private theorem real_log_nat_le_clog (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ (Nat.clog 2 (n + 2) : ℝ) := by
  have hpow : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) :=
    Nat.le_pow_clog (by decide) _
  have hpow' : (n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (n + 2) := by
    exact_mod_cast (Nat.le_add_right n 2).trans hpow
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlog := Real.log_le_log hnpos hpow'
  rw [Real.log_pow] at hlog
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 :=
    (Real.log_two_lt_d9.trans_le (by norm_num)).le
  calc
    Real.log (n : ℝ) ≤ (Nat.clog 2 (n + 2) : ℝ) * Real.log 2 := hlog
    _ ≤ (Nat.clog 2 (n + 2) : ℝ) :=
      mul_le_of_le_one_right (by positivity) hlogtwo

/-- A concrete bound for each actual factor field, obtained from the integral
power-basis discriminant and the Mahler measure of the input. -/
theorem integerFactorRootField_logDiscriminant_le (f : ℤ[X])
    (hf : f.IsPrimitive) (i : IntegerFactorIndex f) :
    fieldLogDiscriminant (IntegerFactorRootField f hf i) ≤
      (i.val.natDegree : ℝ) * Real.log (i.val.natDegree : ℝ) +
        (i.val.natDegree : ℝ) * (i.val.natDegree - 1 : ℕ) *
          Real.log (integerL1 f : ℝ) := by
  let h := i.val
  let K := IntegerFactorRootField f hf i
  let φ : ℤ →+* ℂ := Int.castRingHom ℂ
  let g := h.map φ
  have hd : 1 ≤ h.natDegree := Nat.succ_le_of_lt (integerFactor_natDegree_pos hf i.prop)
  have hirr : Irreducible (h.map (Int.castRingHom ℚ)) :=
    integerFactor_rational_irreducible hf i.prop
  have hM : g.mahlerMeasure ≤ (integerL1 f : ℝ) := by
    exact (integerMahler_le_of_dvd f h hf.ne_zero (integerFactor_dvd i.prop)).trans
      (integerMahler_le_integerL1 f)
  have hS : 1 ≤ (integerL1 f : ℝ) := by
    have hm := integerMahler_one_le f hf.ne_zero
    exact hm.trans (integerMahler_le_integerL1 f)
  have hdiv : NumberField.discr K ∣ h.integralNormalization.discr := by
    simpa [K, IntegerFactorRootField] using
      polynomialRoot_numberField_discr_dvd h hd hirr
  have hnat : (NumberField.discr K).natAbs ∣ (h.integralNormalization.discr).natAbs := by
    rcases hdiv with ⟨c, hc⟩
    refine ⟨c.natAbs, ?_⟩
    rw [← Int.natAbs_mul, hc]
  have hsepQ : (h.integralNormalization.map (Int.castRingHom ℚ)).Separable := by
    exact PerfectField.separable_of_irreducible
      (monicScaling_irreducible_rat h hd hirr)
  have hsepC : (h.integralNormalization.map (Int.castRingHom ℂ)).Separable := by
    have hc := hsepQ.map (f := Rat.castHom ℂ)
    have hcomp : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
      ext z
      simp
    simpa only [Polynomial.map_map, hcomp] using hc
  have horder_ne : h.integralNormalization.discr ≠ 0 := by
    intro hz
    have hdisc := complex_discr_ne_zero_of_separable
      (h.integralNormalization.map (Int.castRingHom ℂ)) hsepC
    rw [← integer_discr_map_complex, hz, Int.cast_zero] at hdisc
    exact hdisc rfl
  have horder_le : (NumberField.discr K).natAbs ≤
      (h.integralNormalization.discr).natAbs := by
    apply Nat.le_of_dvd (Int.natAbs_pos.mpr horder_ne)
    exact hnat
  have hscaled : ((h.integralNormalization.discr).natAbs : ℝ) =
      ‖g.leadingCoeff‖ ^ ((h.natDegree - 1) * (h.natDegree - 2)) * ‖g.discr‖ := by
    have hscaleCast : (h.integralNormalization.discr : ℂ) =
        (h.leadingCoeff : ℂ) ^ ((h.natDegree - 1) * (h.natDegree - 2)) *
          (h.discr : ℂ) := by
      have hh := congrArg (Int.castRingHom ℂ) (monicScaling_discr h hd)
      simpa [φ] using hh
    calc
      _ = ‖(h.integralNormalization.discr : ℂ)‖ := by
        rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      _ = ‖(h.leadingCoeff : ℂ) ^ ((h.natDegree - 1) * (h.natDegree - 2)) *
          (h.discr : ℂ)‖ := by rw [hscaleCast]
      _ = _ := by
        rw [norm_mul, norm_pow]
        change ‖(h.leadingCoeff : ℂ)‖ ^ ((h.natDegree - 1) * (h.natDegree - 2)) *
          ‖(h.discr : ℂ)‖ =
          ‖(h.map φ).leadingCoeff‖ ^ ((h.natDegree - 1) * (h.natDegree - 2)) *
          ‖(h.map φ).discr‖
        rw [leadingCoeff_map_of_injective Int.cast_injective,
          ← integer_discr_map_complex]
        simp [φ]
  have horder : ((NumberField.discr K).natAbs : ℝ) ≤
      ‖g.leadingCoeff‖ ^ ((h.natDegree - 1) * (h.natDegree - 2)) * ‖g.discr‖ := by
    have hc : ((NumberField.discr K).natAbs : ℝ) ≤
        ((h.integralNormalization.discr).natAbs : ℝ) := by exact_mod_cast horder_le
    rw [hscaled] at hc
    exact hc
  have hD : 0 < ((NumberField.discr K).natAbs : ℝ) := by
    exact_mod_cast (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
  have hgd : g.natDegree = h.natDegree :=
    natDegree_map_eq_of_injective Int.cast_injective h
  have hdg : 1 ≤ g.natDegree := by omega
  have horderg : ((NumberField.discr K).natAbs : ℝ) ≤
      ‖g.leadingCoeff‖ ^ ((g.natDegree - 1) * (g.natDegree - 2)) * ‖g.discr‖ := by
    rw [hgd]
    exact horder
  have hlog := log_field_discriminant_le_of_order_bound g (integerL1 f)
    ((NumberField.discr K).natAbs : ℝ) hdg hS hD hM horderg
  rw [hgd] at hlog
  simpa [K, g, h, fieldLogDiscriminant] using hlog

/-- The actual weighted sum of field log-discriminants satisfies the bound used
in Proposition 4.1. -/
theorem integerFactorIndex_weighted_fieldLogDiscriminant_le (f : ℤ[X])
    (hf : f.IsPrimitive) (hdegree : 1 ≤ f.natDegree) :
    (∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
      fieldLogDiscriminant (IntegerFactorRootField f hf i)) ≤
        (f.natDegree : ℝ) ^ 2 * inputDelta f := by
  let n : ℝ := f.natDegree
  let S : ℝ := integerL1 f
  let u : ℝ := Nat.clog 2 (f.natDegree + 2)
  let v : ℝ := Nat.clog 2 (integerL1 f + 2)
  have hn : 1 ≤ n := by
    change (1 : ℝ) ≤ (f.natDegree : ℝ)
    exact_mod_cast hdegree
  have hS : 1 ≤ S := by
    have h := (integerMahler_one_le f hf.ne_zero).trans
      (integerMahler_le_integerL1 f)
    simpa [S] using h
  have hu : Real.log n ≤ u := by
    simpa [n, u] using real_log_nat_le_clog f.natDegree hdegree
  have hSpos := integerL1_pos f hf.ne_zero
  have hv : Real.log S ≤ v := by
    have hSone : 1 ≤ integerL1 f := by omega
    simpa [S, v] using real_log_nat_le_clog (integerL1 f) hSone
  have hΔ : u + v ≤ (inputDelta f : ℝ) := by
    simp [inputDelta, u, v]
  apply weighted_discriminant_sum_le
    (fun i : IntegerFactorIndex f ↦ (integerFactorWeight f i.val : ℝ))
    (fun i ↦ (Module.finrank ℚ (IntegerFactorRootField f hf i) : ℝ))
    (fun i ↦ fieldLogDiscriminant (IntegerFactorRootField f hf i))
    n S u v (inputDelta f)
  · intro i
    exact_mod_cast (integerFactorWeight_bounds f i.val).1
  · intro i
    rw [integerFactorRootField_finrank]
    exact_mod_cast Nat.succ_le_of_lt (integerFactor_natDegree_pos hf i.prop)
  · exact hn
  · exact hS
  · change (∑ i : IntegerFactorIndex f,
      (integerFactorWeight f i.val : ℝ) *
        (Module.finrank ℚ (IntegerFactorRootField f hf i) : ℝ)) ≤
      (f.natDegree : ℝ)
    exact_mod_cast (integerFactorIndex_weighted_finrank_sum_le f hf)
  · intro i
    have hi := integerFactorRootField_logDiscriminant_le f hf i
    simpa [integerFactorRootField_finrank, Nat.cast_sub (by
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (integerFactor_natDegree_pos hf i.prop)))]
      using hi
  · exact hu
  · exact hv
  · exact hΔ

/-- The aggregate higher-degree contribution has the proved square-root bound. -/
theorem integerFactor_higher_degree_bound (f : ℤ[X]) (hf : f.IsPrimitive) (X : ℕ) :
    let F := ∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
      primeIdealCountLE (IntegerFactorRootField f hf i) X
    let F₁ := ∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
      degreeOnePrimeIdealCountLE (IntegerFactorRootField f hf i) X
    0 ≤ F - F₁ ∧ F - F₁ ≤ f.natDegree * Real.sqrt X := by
  apply weighted_higher_degree_bound Finset.univ
    (fun i : IntegerFactorIndex f ↦ (integerFactorWeight f i.val : ℝ))
    (fun i ↦ (primeIdealCountLE (IntegerFactorRootField f hf i) X : ℝ))
    (fun i ↦ (degreeOnePrimeIdealCountLE (IntegerFactorRootField f hf i) X : ℝ))
    (fun i ↦ (Module.finrank ℚ (IntegerFactorRootField f hf i) : ℝ))
  · intros; positivity
  · exact_mod_cast integerFactorIndex_weighted_finrank_sum_le f hf
  · intro i _
    exact sub_nonneg.mpr (by exact_mod_cast
      degreeOnePrimeIdealCountLE_le (IntegerFactorRootField f hf i) X)
  · intro i _
    exact primeIdealCountLE_sub_degreeOne_le_real_sqrt (IntegerFactorRootField f hf i) X

/-- Equation (20) for the actual input counters and actual factor fields. Only the
good-prime identity and the size of the exceptional set are needed as inputs. -/
theorem integer_prime_root_field_comparison (f : ℤ[X]) (hf : f.IsPrimitive)
    (X Δ : ℕ) (bad : Finset ℕ)
    (hgood : ∀ p ∈ X.primesLE, p ∉ bad →
      primeRootWeight f p = integerFactorDegreeOneWeight f hf p)
    (hbad : bad.card ≤ 2 * f.natDegree * Δ) :
    |(primeRootSum f (X + 1) : ℝ) -
      ∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
        primeIdealCountLE (IntegerFactorRootField f hf i) X| ≤
      2 * f.natDegree * Real.sqrt X + 4 * (f.natDegree : ℝ) ^ 2 * Δ := by
  have hsum : (∑ p ∈ X.primesLE, (integerFactorDegreeOneWeight f hf p : ℝ)) =
      ∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
        degreeOnePrimeIdealCountLE (IntegerFactorRootField f hf i) X := by
    exact_mod_cast integerFactorDegreeOneWeight_sum f hf X
  obtain ⟨hh₀, hh₁⟩ := integerFactor_higher_degree_bound f hf X
  rw [← hsum] at hh₀ hh₁
  have hcompare := prime_root_field_comparison X.primesLE bad
    (fun p ↦ (primeRootWeight f p : ℝ))
    (fun p ↦ (integerFactorDegreeOneWeight f hf p : ℝ))
    (∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
      primeIdealCountLE (IntegerFactorRootField f hf i) X)
    (f.natDegree : ℝ) (Δ : ℝ) (X : ℝ) (by positivity)
    (fun p hp hb ↦ by exact_mod_cast hgood p hp hb)
    (fun p _ ↦ ?_) (by exact_mod_cast hbad) hh₀ hh₁
  · simpa only [primeRootSum, Nat.primesLE_eq_filter_range, Nat.cast_sum] using hcompare
  · have ha : (primeRootWeight f p : ℝ) ≤ 2 * f.natDegree := by
      exact_mod_cast primeRootWeight_le f hf p
    have hb : (integerFactorDegreeOneWeight f hf p : ℝ) ≤ f.natDegree := by
      exact_mod_cast integerFactorDegreeOneWeight_le f hf p
    have hpa : (0 : ℝ) ≤ primeRootWeight f p := Nat.cast_nonneg _
    have hpb : (0 : ℝ) ≤ integerFactorDegreeOneWeight f hf p := Nat.cast_nonneg _
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Proposition 4.1 for the actual primitive polynomial. The analytic assumption
is the uniform external prime-ideal estimate; the remaining algebraic inputs are
the weighted field-discriminant bound and the good-prime exceptional-set data. -/
theorem integer_prime_root_average (f : ℤ[X]) (hf : f.IsPrimitive)
    (C : ℝ) (hC : 0 ≤ C) (hExternal : UniformPrimeIdealEstimate C)
    (X : ℕ) (hX : 2 < X) (bad : Finset ℕ)
    (hdiscriminant :
      (∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
        fieldLogDiscriminant (IntegerFactorRootField f hf i)) ≤
          (f.natDegree : ℝ) ^ 2 * inputDelta f)
    (hgood : ∀ p ∈ X.primesLE, p ∉ bad →
      primeRootWeight f p = integerFactorDegreeOneWeight f hf p)
    (hbad : bad.card ≤ 2 * f.natDegree * inputDelta f) :
    |(primeRootSum f (X + 1) : ℝ) -
      factorStatistic (f.map (Int.castRingHom ℚ)) * (X.primeCounting : ℝ)| ≤
      C * (X : ℝ) ^ (31 / 32 : ℝ) *
        (64 * (f.natDegree : ℝ) ^ 2 * inputDelta f +
          4 * f.natDegree * Real.log X) +
        2 * f.natDegree * Real.sqrt X + 4 * (f.natDegree : ℝ) ^ 2 * inputDelta f := by
  have hweight : (∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ)) =
      factorStatistic (f.map (Int.castRingHom ℚ)) := by
    exact_mod_cast integerFactorIndex_weight_sum f hf
  have havg := prime_root_average_bound Finset.univ
    (fun i : IntegerFactorIndex f ↦ (integerFactorWeight f i.val : ℝ))
    (fun i ↦ (primeIdealCountLE (IntegerFactorRootField f hf i) X : ℝ))
    (fun i ↦ fieldLogDiscriminant (IntegerFactorRootField f hf i))
    (fun i ↦ (Module.finrank ℚ (IntegerFactorRootField f hf i) : ℝ))
    (primeRootSum f (X + 1) : ℝ) (X.primeCounting : ℝ)
    (∫ t in (2 : ℝ)..(X : ℝ), 1 / Real.log t) C (f.natDegree : ℝ)
    (inputDelta f : ℝ) (X : ℝ)
    (fun _ _ ↦ by positivity) hC (by positivity) (by positivity)
    (by exact_mod_cast hX)
    (by exact_mod_cast integerFactorIndex_weight_sum_le f hf)
    (by exact_mod_cast integerFactorIndex_weighted_finrank_sum_le f hf)
    hdiscriminant (fun i _ ↦ hExternal (IntegerFactorRootField f hf i) X hX)
    (rational_primeCount_estimate C hExternal X hX)
    (integer_prime_root_field_comparison f hf X (inputDelta f) bad hgood hbad)
  simpa only [hweight] using havg

/-- The same bound at a composite endpoint uses exactly the strict counters
appearing in the streaming algorithm. -/
theorem integer_prime_root_average_of_not_prime (f : ℤ[X]) (hf : f.IsPrimitive)
    (C : ℝ) (hC : 0 ≤ C) (hExternal : UniformPrimeIdealEstimate C)
    (X : ℕ) (hX : 2 < X) (hcomposite : ¬X.Prime) (bad : Finset ℕ)
    (hdiscriminant :
      (∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
        fieldLogDiscriminant (IntegerFactorRootField f hf i)) ≤
          (f.natDegree : ℝ) ^ 2 * inputDelta f)
    (hgood : ∀ p ∈ X.primesLE, p ∉ bad →
      primeRootWeight f p = integerFactorDegreeOneWeight f hf p)
    (hbad : bad.card ≤ 2 * f.natDegree * inputDelta f) :
    |(primeRootSum f X : ℝ) -
      factorStatistic (f.map (Int.castRingHom ℚ)) * (primeCountBelow X : ℝ)| ≤
      C * (X : ℝ) ^ (31 / 32 : ℝ) *
        (64 * (f.natDegree : ℝ) ^ 2 * inputDelta f +
          4 * f.natDegree * Real.log X) +
        2 * f.natDegree * Real.sqrt X + 4 * (f.natDegree : ℝ) ^ 2 * inputDelta f := by
  rw [primeCountBelow_eq_primeCounting_of_not_prime X hcomposite,
    ← primeRootSum_succ_of_not_prime f X hcomposite]
  exact integer_prime_root_average f hf C hC hExternal X hX bad hdiscriminant hgood hbad

/-- Proposition 4.1 instantiated for the actual irreducible factors of the
input. The only remaining analytic hypothesis is the uniform prime-ideal
estimate. -/
theorem integer_prime_root_average_concrete (f : ℤ[X]) (hf : f.IsPrimitive)
    (hdegree : 1 ≤ f.natDegree) (C : ℝ) (hC : 0 ≤ C)
    (hExternal : UniformPrimeIdealEstimate C)
    (X : ℕ) (hX : 2 < X) :
    |(primeRootSum f (X + 1) : ℝ) -
      factorStatistic (f.map (Int.castRingHom ℚ)) * (X.primeCounting : ℝ)| ≤
      C * (X : ℝ) ^ (31 / 32 : ℝ) *
        (64 * (f.natDegree : ℝ) ^ 2 * inputDelta f +
          4 * f.natDegree * Real.log X) +
        2 * f.natDegree * Real.sqrt X + 4 * (f.natDegree : ℝ) ^ 2 * inputDelta f := by
  apply integer_prime_root_average f hf C hC hExternal X hX
    (integerSquarefreeExceptionalPrimes f)
    (integerFactorIndex_weighted_fieldLogDiscriminant_le f hf hdegree)
  · intro p hpX hpnot
    obtain ⟨_, hp⟩ := Nat.mem_primesLE.mp hpX
    letI : Fact p.Prime := ⟨hp⟩
    exact integerFactorization_good_prime_root_weight_eq_degreeOne
      f hf hdegree p hp hpnot
  · exact integerSquarefreeExceptionalPrimes_card_le f hf hdegree

/-- The composite-endpoint form of the concrete average estimate, matching the
strict prime counters used by the streaming algorithm. -/
theorem integer_prime_root_average_of_not_prime_concrete (f : ℤ[X])
    (hf : f.IsPrimitive) (hdegree : 1 ≤ f.natDegree)
    (C : ℝ) (hC : 0 ≤ C) (hExternal : UniformPrimeIdealEstimate C)
    (X : ℕ) (hX : 2 < X) (hcomposite : ¬X.Prime) :
    |(primeRootSum f X : ℝ) -
      factorStatistic (f.map (Int.castRingHom ℚ)) * (primeCountBelow X : ℝ)| ≤
      C * (X : ℝ) ^ (31 / 32 : ℝ) *
        (64 * (f.natDegree : ℝ) ^ 2 * inputDelta f +
          4 * f.natDegree * Real.log X) +
        2 * f.natDegree * Real.sqrt X + 4 * (f.natDegree : ℝ) ^ 2 * inputDelta f := by
  exact integer_prime_root_average_of_not_prime f hf C hC hExternal X hX
    hcomposite (integerSquarefreeExceptionalPrimes f)
    (integerFactorIndex_weighted_fieldLogDiscriminant_le f hf hdegree)
    (by
      intro p hpX hpnot
      obtain ⟨_, hp⟩ := Nat.mem_primesLE.mp hpX
      letI : Fact p.Prime := ⟨hp⟩
      exact integerFactorization_good_prime_root_weight_eq_degreeOne
        f hf hdegree p hp hpnot)
    (integerSquarefreeExceptionalPrimes_card_le f hf hdegree)

/-- Combining the concrete root-average theorem with the rational-prime estimate
derives the paper's exact decision inequality from the single uniform external
prime-ideal estimate. -/
theorem integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate
    (C₀ : ℕ) (f : ℤ[X]) (hC : 1 ≤ C₀) (hf : f.IsPrimitive)
    (hdegree : 0 < f.natDegree)
    (hExternal : UniformPrimeIdealEstimate C₀) :
    Irreducible f ↔
      2 * primeRootSum f (primeCountingCutoff C₀ f) <
        3 * primeCountBelow (primeCountingCutoff C₀ f) := by
  have hX : 2 < primeCountingCutoff C₀ f := by
    have hm := inputCutoffExponent_ge C₀ f hC hdegree
    have hp : 2 ^ 2 ≤ 2 ^ inputCutoffExponent C₀ f :=
      Nat.pow_le_pow_right (by decide) (by omega)
    unfold primeCountingCutoff
    omega
  have hnot : ¬(primeCountingCutoff C₀ f).Prime := by
    unfold primeCountingCutoff
    apply Nat.Prime.not_prime_pow
    have hm := inputCutoffExponent_ge C₀ f hC hdegree
    omega
  apply integer_irreducible_iff_primeCounting_threshold C₀ f hC hf hdegree
  · exact primeCountingCutoff_prime_estimate C₀ hC hExternal f hdegree
  · exact integer_prime_root_average_of_not_prime_concrete f hf
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdegree)) C₀ (by positivity)
      hExternal (primeCountingCutoff C₀ f) hX hnot

end SparseIrred.UpperBounds
