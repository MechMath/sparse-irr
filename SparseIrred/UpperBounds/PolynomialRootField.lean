import SparseIrred.UpperBounds.DedekindRootComparison

/-!
# The number field of an integer polynomial

For a positive-degree integer polynomial irreducible over the rationals, we
construct the field of a root of its integral monic scaling. Its distinguished
root is integral and has the scaled polynomial as its integer minimal
polynomial. The field degree is the degree of the original polynomial.
-/

namespace SparseIrred.UpperBounds

open Polynomial NumberField

/-- The rational polynomial defining the scaled root field is irreducible. -/
theorem monicScaling_irreducible_rat (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    Irreducible (f.integralNormalization.map (Int.castRingHom ℚ)) :=
  (monic_integralNormalization (ne_zero_of_natDegree_gt hd))
    |>.irreducible_iff_irreducible_map_fraction_map.mp (monicScaling_irreducible f hd hirr)

/-- The concrete number field used for an irreducible nonmonic factor. -/
abbrev PolynomialRootField (f : ℤ[X]) (_hd : 1 ≤ f.natDegree)
    (_hirr : Irreducible (f.map (Int.castRingHom ℚ))) : Type :=
  AdjoinRoot (f.integralNormalization.map (Int.castRingHom ℚ))

noncomputable instance polynomialRootFieldField (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    Field (PolynomialRootField f hd hirr) := by
  let : Fact (Irreducible (f.integralNormalization.map (Int.castRingHom ℚ))) :=
    ⟨monicScaling_irreducible_rat f hd hirr⟩
  unfold PolynomialRootField
  infer_instance

noncomputable instance polynomialRootFieldNumberField (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    NumberField (PolynomialRootField f hd hirr) := by
  let : Fact (Irreducible (f.integralNormalization.map (Int.castRingHom ℚ))) :=
    ⟨monicScaling_irreducible_rat f hd hirr⟩
  unfold PolynomialRootField
  infer_instance

instance polynomialRootFieldIsScalarTower (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    IsScalarTower ℤ ℚ (PolynomialRootField f hd hirr) := by
  constructor
  intro z q x
  rw [← Int.cast_smul_eq_zsmul ℚ z q,
    ← Int.cast_smul_eq_zsmul ℚ z (q • x), smul_assoc]
  rfl

/-- The canonical rational power basis in the scaled root field. -/
noncomputable def polynomialRootPowerBasis (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    PowerBasis ℚ (PolynomialRootField f hd hirr) :=
  AdjoinRoot.powerBasis (monicScaling_irreducible_rat f hd hirr).ne_zero

/-- The scaled polynomial vanishes at the distinguished root over the integers. -/
theorem polynomialRootPowerBasis_aeval (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    f.integralNormalization.aeval (polynomialRootPowerBasis f hd hirr).gen = 0 := by
  let tower := polynomialRootFieldIsScalarTower f hd hirr
  have hmap :
      Polynomial.aeval (polynomialRootPowerBasis f hd hirr).gen
          (f.integralNormalization.map (Int.castRingHom ℚ)) =
        Polynomial.aeval (polynomialRootPowerBasis f hd hirr).gen f.integralNormalization :=
    @Polynomial.aeval_map_algebraMap ℤ ℚ (PolynomialRootField f hd hirr)
      _ _ _ _ _ _ tower _ _
  rw [← hmap]
  exact AdjoinRoot.eval₂_root _

/-- The scaled root, unlike the root before scaling, is an algebraic integer. -/
theorem polynomialRootPowerBasis_isIntegral (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    IsIntegral ℤ (polynomialRootPowerBasis f hd hirr).gen :=
  ⟨f.integralNormalization, monic_integralNormalization (ne_zero_of_natDegree_gt hd),
    polynomialRootPowerBasis_aeval f hd hirr⟩

/-- The distinguished root as an element of the ring of integers. -/
noncomputable def polynomialRootInteger (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    𝓞 (PolynomialRootField f hd hirr) :=
  ⟨(polynomialRootPowerBasis f hd hirr).gen,
    polynomialRootPowerBasis_isIntegral f hd hirr⟩

/-- The power-basis generator is the underlying value of the integral root. -/
theorem polynomialRootPowerBasis_gen (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    (polynomialRootPowerBasis f hd hirr).gen =
      (polynomialRootInteger f hd hirr : PolynomialRootField f hd hirr) := rfl

/-- The integer minimal polynomial is exactly the integral monic scaling. -/
theorem polynomialRootInteger_minpoly (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    minpoly ℤ (polynomialRootInteger f hd hirr) = f.integralNormalization := by
  let tower := polynomialRootFieldIsScalarTower f hd hirr
  rw [← RingOfIntegers.minpoly_coe, ← polynomialRootPowerBasis_gen]
  have hq : minpoly ℚ (polynomialRootPowerBasis f hd hirr).gen =
      f.integralNormalization.map (Int.castRingHom ℚ) := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · exact monicScaling_irreducible_rat f hd hirr
    · exact AdjoinRoot.eval₂_root _
    · exact (monic_integralNormalization (ne_zero_of_natDegree_gt hd)).map _
  have hbridge : minpoly ℚ (polynomialRootPowerBasis f hd hirr).gen =
      (minpoly ℤ (polynomialRootPowerBasis f hd hirr).gen).map (Int.castRingHom ℚ) :=
    @minpoly.isIntegrallyClosed_eq_field_fractions' ℤ
      (PolynomialRootField f hd hirr) _ _ _ _ ℚ _ _ _ _ _ _ tower _
      (polynomialRootPowerBasis_isIntegral f hd hirr)
  rw [hq] at hbridge
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  exact hbridge.symm

/-- Monic scaling and formation of the root field preserve the degree. -/
theorem polynomialRootField_finrank (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) :
    Module.finrank ℚ (PolynomialRootField f hd hirr) = f.natDegree := by
  rw [(polynomialRootPowerBasis f hd hirr).finrank]
  change (f.integralNormalization.map (Int.castRingHom ℚ)).natDegree = f.natDegree
  rw [natDegree_map_eq_of_injective (Int.cast_injective : Function.Injective (Int.castRingHom ℚ)),
    natDegree_integralNormalization]

end SparseIrred.UpperBounds
