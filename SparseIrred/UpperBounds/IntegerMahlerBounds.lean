import SparseIrred.UpperBounds.SparseInputBounds
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-!
# Mahler measure bounds for integer factors

The coefficient norm `S` in Lemma 3.1 of the standalone prime-counting note is
the actual integer coefficient sum `integerL1`. A nonzero integer polynomial has
Mahler measure at least one. Multiplicativity therefore bounds the Mahler
measure of every integer divisor by that of the original polynomial, and hence
by `S`. None of these bounds is an analytic hypothesis.
-/

namespace SparseIrred.UpperBounds

open Polynomial

/-- The natural coefficient sum agrees with the real sum of coefficient norms. -/
theorem integerL1_eq_sum_norm (f : ℤ[X]) :
    (integerL1 f : ℝ) = f.sum fun _ a ↦ ‖a‖ := by
  rw [integerL1_eq_sum, Nat.cast_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro e he
  exact congrArg (fun x : NNReal ↦ (x : ℝ)) (NNReal.natCast_natAbs (f.coeff e))

/-- A nonzero integer leading coefficient forces Mahler measure at least one. -/
theorem integerMahler_one_le (f : ℤ[X]) (hf : f ≠ 0) :
    1 ≤ f.mapMahlerMeasure (Int.castRingHom ℂ) := by
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hpos : 0 < f.leadingCoeff.natAbs := Int.natAbs_pos.mpr hlc
  have hnorm : (f.leadingCoeff.natAbs : ℝ) = ‖f.leadingCoeff‖ :=
    congrArg (fun x : NNReal ↦ (x : ℝ)) (NNReal.natCast_natAbs f.leadingCoeff)
  have hlc₁ : 1 ≤ ‖f.leadingCoeff‖ := by
    rw [← hnorm]
    exact_mod_cast hpos
  exact hlc₁.trans
    (f.leadingCoeff_le_mapMahlerMeasure (Int.castRingHom ℂ) Complex.isometry_intCast)

/-- The Mahler measure is bounded by the sparse integer coefficient norm. -/
theorem integerMahler_le_integerL1 (f : ℤ[X]) :
    f.mapMahlerMeasure (Int.castRingHom ℂ) ≤ (integerL1 f : ℝ) := by
  rw [integerL1_eq_sum_norm]
  exact f.mapMahlerMeasure_le_sum_norm_coeff (Int.castRingHom ℂ) Complex.isometry_intCast

/-- Every integer divisor of a nonzero polynomial has no larger Mahler measure. -/
theorem integerMahler_le_of_dvd (f g : ℤ[X]) (hf : f ≠ 0) (hgf : g ∣ f) :
    g.mapMahlerMeasure (Int.castRingHom ℂ) ≤ f.mapMahlerMeasure (Int.castRingHom ℂ) := by
  obtain ⟨h, rfl⟩ := hgf
  have hh : h ≠ 0 := right_ne_zero_of_mul hf
  have hM := integerMahler_one_le h hh
  rw [mapMahlerMeasure_mul]
  calc
    g.mapMahlerMeasure (Int.castRingHom ℂ) =
        g.mapMahlerMeasure (Int.castRingHom ℂ) * 1 := by ring
    _ ≤ g.mapMahlerMeasure (Int.castRingHom ℂ) *
        h.mapMahlerMeasure (Int.castRingHom ℂ) :=
      mul_le_mul_of_nonneg_left hM (g.mapMahlerMeasure_nonneg (Int.castRingHom ℂ))

/-- The complete Mahler bound used for each primitive irreducible factor and
for the squarefree part: both are integer divisors of the nonzero input. -/
theorem integer_divisor_mahler_bounds (f g : ℤ[X]) (hf : f ≠ 0) (hgf : g ∣ f) :
    1 ≤ g.mapMahlerMeasure (Int.castRingHom ℂ) ∧
      g.mapMahlerMeasure (Int.castRingHom ℂ) ≤ f.mapMahlerMeasure (Int.castRingHom ℂ) ∧
      f.mapMahlerMeasure (Int.castRingHom ℂ) ≤ (integerL1 f : ℝ) := by
  have hg : g ≠ 0 := ne_zero_of_dvd_ne_zero hf hgf
  exact ⟨integerMahler_one_le g hg, integerMahler_le_of_dvd f g hf hgf,
    integerMahler_le_integerL1 f⟩

/-- The logarithmic form needed when bounding discriminants of root fields. -/
theorem integer_divisor_logMahler_bounds (f g : ℤ[X]) (hf : f ≠ 0) (hgf : g ∣ f) :
    0 ≤ Real.log (g.mapMahlerMeasure (Int.castRingHom ℂ)) ∧
      Real.log (g.mapMahlerMeasure (Int.castRingHom ℂ)) ≤ Real.log (integerL1 f : ℝ) := by
  obtain ⟨h₁, h₂, h₃⟩ := integer_divisor_mahler_bounds f g hf hgf
  exact ⟨Real.log_nonneg h₁, Real.log_le_log (by linarith) (h₂.trans h₃)⟩

/-- Mignotte's coefficient bound for an integer divisor, in terms of the
coefficient sum of the input polynomial. -/
theorem integer_divisor_coeff_bound (f g : ℤ[X]) (hf : f ≠ 0) (hgf : g ∣ f) (e : ℕ) :
    ((g.coeff e).natAbs : ℝ) ≤ (g.natDegree.choose e : ℝ) * (integerL1 f : ℝ) := by
  have hnorm : ((g.coeff e).natAbs : ℝ) = ‖g.coeff e‖ :=
    congrArg (fun x : NNReal ↦ (x : ℝ)) (NNReal.natCast_natAbs (g.coeff e))
  rw [hnorm]
  refine (norm_coeff_le_choose_mul_mapMahlerMeasure (Int.castRingHom ℂ)
    Complex.isometry_intCast e g).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (integerMahler_le_of_dvd f g hf hgf).trans (integerMahler_le_integerL1 f)

end SparseIrred.UpperBounds
