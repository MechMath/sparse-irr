import SparseDivComplexity.Appendix.Content

/-!
# Integer-polynomial boundary cases

Section 3 first separates constants and nonprimitive nonconstant polynomials.
The classification here includes zero, both units, negative prime constants,
and polynomials with zero constant coefficient.
-/

open Polynomial

namespace SparseIrred.UpperBounds

/-- Irreducible integer constants are exactly the signed rational primes. -/
theorem irreducible_integer_constant_iff (c : ℤ) :
    Irreducible (C c : ℤ[X]) ↔ c.natAbs.Prime := by
  rw [irreducible_iff_prime, Polynomial.prime_C_iff, Int.prime_iff_natAbs_prime]

/-- A positive-degree integer polynomial is irreducible exactly when it is primitive
and irreducible over the rationals. -/
theorem integer_irreducible_iff_primitive_and_rational (f : ℤ[X]) (hf : 0 < f.natDegree) :
    Irreducible f ↔ f.IsPrimitive ∧ Irreducible (f.map (Int.castRingHom ℚ)) := by
  constructor
  · intro hi
    have hp := hi.isPrimitive hf.ne'
    exact ⟨hp, (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp).mp hi⟩
  · rintro ⟨hp, hi⟩
    exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp).mpr hi

/-- Complete semantic preprocessing for the integer algorithm. -/
theorem integer_irreducible_boundary (f : ℤ[X]) :
    Irreducible f ↔
      if f.natDegree = 0 then (f.coeff 0).natAbs.Prime
      else f.IsPrimitive ∧ Irreducible (f.map (Int.castRingHom ℚ)) := by
  split_ifs with hd
  · conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    exact irreducible_integer_constant_iff _
  · exact integer_irreducible_iff_primitive_and_rational f (Nat.pos_of_ne_zero hd)

end SparseIrred.UpperBounds
