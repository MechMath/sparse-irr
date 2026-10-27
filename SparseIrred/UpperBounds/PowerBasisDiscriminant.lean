import Mathlib.NumberTheory.NumberField.Norm
import SparseIrred.UpperBounds.PolynomialRootField
import SparseIrred.UpperBounds.MonicScaling

/-!
# Power-basis and polynomial discriminants

This file identifies the discriminant of the actual integral power basis in
PolynomialRootField with the discriminant of its integer minimal polynomial.
-/

namespace SparseIrred.UpperBounds

open Polynomial NumberField

theorem norm_aeval_roots {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    (B : PowerBasis K L) (q : K[X]) :
    algebraMap K E (Algebra.norm K (aeval B.gen q)) =
      (((minpoly K B.gen).aroots E).map (q.map (algebraMap K E)).eval).prod := by
  classical
  rw [Algebra.norm_eq_prod_embeddings K E]
  rw [Fintype.prod_equiv B.liftEquiv'
    (fun σ ↦ σ (aeval B.gen q)) (fun x ↦ (q.map (algebraMap K E)).eval x) ?_]
  · rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr]
    · exact nodup_roots (.map (Algebra.IsSeparable.isSeparable K B.gen))
    · intro x; rfl
  · intro σ
    simp only [PowerBasis.liftEquiv'_apply_coe, eval_map_algebraMap, aeval_algHom_apply]

theorem resultant_minpoly_eq_norm {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (B : PowerBasis K L) (q : K[X]) (n : ℕ) (hq : q.natDegree ≤ n) :
    (minpoly K B.gen).resultant q (minpoly K B.gen).natDegree n =
      Algebra.norm K (aeval B.gen q) := by
  let E := AlgebraicClosure K
  apply (algebraMap K E).injective
  rw [norm_aeval_roots E B q, ← resultant_map_map]
  rw [← natDegree_map_eq_of_injective (algebraMap K E).injective (minpoly K B.gen)]
  rw [resultant_eq_prod_eval _ _ n (natDegree_map_le.trans hq) (IsAlgClosed.splits _)]
  rw [((minpoly.monic B.isIntegral_gen).map _).leadingCoeff, one_pow, one_mul]

/-- The discriminant of an integral family agrees with the rational
discriminant of its image in a number field. -/
theorem algebra_discr_int_coe (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → 𝓞 K) :
    (Algebra.discr ℤ v : ℚ) = Algebra.discr ℚ (fun i ↦ (v i : K)) := by
  rw [Algebra.discr_def, Algebra.discr_def]
  change algebraMap ℤ ℚ (Algebra.traceMatrix ℤ v).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, ← map_mul]
  exact (Algebra.trace_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 K) (Sₘ := K)
    (nonZeroDivisors ℤ) (v i * v j)).symm

/-- The discriminant of a power basis is the discriminant of the minimal
polynomial of its generator. -/
theorem powerBasis_discr_eq_minpoly_discr {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (B : PowerBasis K L) : Algebra.discr K B.basis = (minpoly K B.gen).discr := by
  have hpos : 0 < (minpoly K B.gen).degree := minpoly.degree_pos B.isIntegral_gen
  have hres := resultant_deriv hpos
  rw [resultant_minpoly_eq_norm B _ _ (natDegree_derivative_le _),
    (minpoly.monic B.isIntegral_gen).leadingCoeff, mul_one] at hres
  rw [Algebra.discr_powerBasis_eq_norm, B.finrank, ← B.natDegree_minpoly, hres]
  rw [← mul_assoc, ← pow_two, ← pow_mul]
  simp

/-- For a monic integer polynomial, mapping coefficients to the rationals
commutes with the polynomial discriminant. -/
theorem monic_polynomial_discr_map_rat (g : ℤ[X]) (hg : g.Monic)
    (hdeg : 0 < g.degree) :
    (g.map (Int.castRingHom ℚ)).discr = (g.discr : ℚ) := by
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  have hnat : 0 < g.natDegree := natDegree_pos_iff_degree_pos.mpr hdeg
  have hnat' : 0 < (g.map φ).natDegree := by
    rw [natDegree_map_eq_of_injective Int.cast_injective]
    exact hnat
  have hdeg' : 0 < (g.map φ).degree := natDegree_pos_iff_degree_pos.mp hnat'
  have hr := resultant_deriv (f := g) hdeg
  have hr' := resultant_deriv (f := g.map φ) hdeg'
  have hmap :
      (g.map φ).resultant (g.map φ).derivative (g.map φ).natDegree
          ((g.map φ).natDegree - 1) =
        φ (g.resultant g.derivative g.natDegree (g.natDegree - 1)) := by
    rw [Polynomial.derivative_map, ← resultant_map_map]
    rw [natDegree_map_eq_of_injective Int.cast_injective]
  rw [hmap] at hr'
  rw [natDegree_map_eq_of_injective Int.cast_injective] at hr'
  rw [hg.leadingCoeff] at hr
  rw [hg.map φ |>.leadingCoeff] at hr'
  have hm := congrArg φ hr
  simp only [map_mul, map_pow, map_neg, map_one] at hm
  have hcast : φ g.discr = (g.discr : ℚ) := rfl
  rw [hcast] at hm
  simp only [mul_one] at hm
  have hs : (-1 : ℚ) ^ (g.natDegree * (g.natDegree - 1) / 2) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hs)
  calc
    (-1 : ℚ) ^ (g.natDegree * (g.natDegree - 1) / 2) * (g.map φ).discr =
        φ (g.resultant g.derivative g.natDegree (g.natDegree - 1)) := by
      simpa only [mul_one, one_mul] using hr'.symm
    _ = (-1 : ℚ) ^ (g.natDegree * (g.natDegree - 1) / 2) * (g.discr : ℚ) := by
      exact hm

/-- The integer discriminant of the power family of the distinguished integral
root is exactly the discriminant of the integral monic scaling. -/
theorem polynomialRoot_powerFamily_discr (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    Algebra.discr ℤ
        (fun i : Fin (Module.finrank ℚ (PolynomialRootField f hd hirr)) ↦
          polynomialRootInteger f hd hirr ^ (i : ℕ)) =
      f.integralNormalization.discr := by
  let K := PolynomialRootField f hd hirr
  let θ := polynomialRootInteger f hd hirr
  let B := polynomialRootPowerBasis f hd hirr
  let g := f.integralNormalization
  have hmin : minpoly ℚ B.gen = g.map (Int.castRingHom ℚ) := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · exact monicScaling_irreducible_rat f hd hirr
    · exact AdjoinRoot.eval₂_root _
    · exact (monic_integralNormalization (ne_zero_of_natDegree_gt hd)).map _
  have hdisc := algebra_discr_int_coe K
    (fun i : Fin (Module.finrank ℚ K) ↦ θ ^ (i : ℕ))
  rw [B.finrank] at hdisc
  have hgen : B.gen = (θ : K) := by
    exact polynomialRootPowerBasis_gen f hd hirr
  have hdisc' : (Algebra.discr ℤ
      (fun i : Fin B.dim ↦ θ ^ (i : ℕ)) : ℚ) = Algebra.discr ℚ B.basis := by
    convert hdisc using 1
    · congr 1
      funext i
      rw [PowerBasis.basis_eq_pow, hgen]
      rfl
  have hnatg : 0 < g.natDegree := by
    rw [natDegree_integralNormalization]
    exact hd
  have hdegg : 0 < g.degree := natDegree_pos_iff_degree_pos.mp hnatg
  rw [powerBasis_discr_eq_minpoly_discr B, hmin,
    monic_polynomial_discr_map_rat g
      (monic_integralNormalization (ne_zero_of_natDegree_gt hd)) hdegg]
    at hdisc'
  rw [B.finrank]
  exact_mod_cast hdisc'

/-- The absolute number-field discriminant divides the discriminant of the
integral monic scaling used to define the root field. -/
theorem polynomialRoot_numberField_discr_dvd (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    NumberField.discr (PolynomialRootField f hd hirr) ∣
      f.integralNormalization.discr := by
  have h := numberField_discr_dvd_power_family
    (PolynomialRootField f hd hirr) (polynomialRootInteger f hd hirr)
  rw [polynomialRoot_powerFamily_discr f hd hirr] at h
  exact h

/-- The rational discriminant hypothesis in the Dedekind correspondence is
automatic for the power basis of the polynomial root field. -/
theorem polynomialRoot_powerBasis_discr_rat (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    Algebra.discr ℚ (polynomialRootPowerBasis f hd hirr).basis =
      (f.integralNormalization.discr : ℚ) := by
  let K := PolynomialRootField f hd hirr
  let θ := polynomialRootInteger f hd hirr
  let B := polynomialRootPowerBasis f hd hirr
  let g := f.integralNormalization
  have hdisc := algebra_discr_int_coe K
    (fun i : Fin (Module.finrank ℚ K) ↦ θ ^ (i : ℕ))
  rw [B.finrank] at hdisc
  have hgen : B.gen = (θ : K) := by
    exact polynomialRootPowerBasis_gen f hd hirr
  have hdisc' : (Algebra.discr ℤ
      (fun i : Fin B.dim ↦ θ ^ (i : ℕ)) : ℚ) = Algebra.discr ℚ B.basis := by
    convert hdisc using 1
    congr 1
    funext i
    rw [PowerBasis.basis_eq_pow, hgen]
    rfl
  have hint : Algebra.discr ℤ
      (fun i : Fin B.dim ↦ θ ^ (i : ℕ)) = g.discr := by
    rw [← B.finrank]
    simpa [K, θ, B, g] using polynomialRoot_powerFamily_discr f hd hirr
  calc
    Algebra.discr ℚ B.basis =
        (Algebra.discr ℤ (fun i : Fin B.dim ↦ θ ^ (i : ℕ)) : ℚ) := hdisc'.symm
    _ = (g.discr : ℚ) := congrArg (Int.castRingHom ℚ) hint
    _ = (f.integralNormalization.discr : ℚ) := by rfl

/-- Concrete good-prime root-count correspondence for the distinguished root
of the polynomial root field. -/
theorem polynomialRoot_nonmonic_rootCount_eq_degreeOnePrimesOver
    (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (p : ℕ) [Fact p.Prime]
    (ha : ¬(p : ℤ) ∣ f.leadingCoeff)
    (hfdisc : ¬(p : ℤ) ∣ f.discr) :
    rootCount (f.map (Int.castRingHom (ZMod p))) =
      Nat.card {P : (Ideal.span {(p : ℤ)}).primesOver
          (𝓞 (PolynomialRootField f hd hirr)) // P.val.inertiaDeg ℤ = 1} := by
  apply nonmonic_rootCount_eq_degreeOnePrimesOver
    (PolynomialRootField f hd hirr) f hd
    (polynomialRootInteger f hd hirr)
    (polynomialRootInteger_minpoly f hd hirr)
    (polynomialRootPowerBasis f hd hirr)
    (polynomialRootPowerBasis_gen f hd hirr)
    (polynomialRoot_powerBasis_discr_rat f hd hirr) p ha hfdisc

end SparseIrred.UpperBounds
