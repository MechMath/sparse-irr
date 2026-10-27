import Mathlib
import SparseIrred.UpperBounds.ModularRoots

/-!
# Integral monic scaling of a nonmonic integer polynomial

The polynomial `f.integralNormalization` is the integer polynomial
`a^(d-1) f(y/a)`, where `a` is the leading coefficient and `d` is the positive
degree of `f`. This file verifies the change of variable and its discriminant
scaling, without treating either assertion as a number-theoretic input.
-/

namespace SparseIrred.UpperBounds

open Polynomial

/-- Coefficients below the leading term of the integral monic scaling. -/
theorem monicScaling_coeff (f : ℤ[X]) (i : ℕ) (hi : i < f.natDegree) :
    f.integralNormalization.coeff i =
      f.coeff i * f.leadingCoeff ^ (f.natDegree - 1 - i) :=
  integralNormalization_coeff_ne_natDegree (by omega)

/-- The construction stays over the integers, is monic, and preserves degree. -/
theorem monicScaling_monic_degree (f : ℤ[X]) (hf : f ≠ 0) :
    f.integralNormalization.Monic ∧ f.integralNormalization.natDegree = f.natDegree :=
  ⟨monic_integralNormalization hf, natDegree_integralNormalization⟩

/-- The substitution formula, valid over any commutative target ring. -/
theorem monicScaling_eval {R : Type*} [CommRing R] (f : ℤ[X])
    (hd : 1 ≤ f.natDegree) (φ : ℤ →+* R) (x : R) :
    f.integralNormalization.eval₂ φ (φ f.leadingCoeff * x) =
      φ f.leadingCoeff ^ (f.natDegree - 1) * f.eval₂ φ x :=
  integralNormalization_eval₂_leadingCoeff_mul hd φ x

/-- Scaling gives both directions of the root correspondence, provided the
leading coefficient survives in the target field. -/
theorem monicScaling_root_iff {K : Type*} [Field K] (f : ℤ[X])
    (hd : 1 ≤ f.natDegree) (φ : ℤ →+* K) (ha : φ f.leadingCoeff ≠ 0) (x : K) :
    f.integralNormalization.eval₂ φ (φ f.leadingCoeff * x) = 0 ↔ f.eval₂ φ x = 0 := by
  rw [monicScaling_eval f hd φ x]
  exact ⟨fun h ↦ (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ ha),
    fun h ↦ by rw [h, mul_zero]⟩

/-- The change of variable is an actual equivalence of root sets. -/
noncomputable def monicScaling_rootEquiv {K : Type*} [Field K] (f : ℤ[X])
    (hd : 1 ≤ f.natDegree) (φ : ℤ →+* K) (ha : φ f.leadingCoeff ≠ 0) :
    {x : K // f.eval₂ φ x = 0} ≃ {y : K // f.integralNormalization.eval₂ φ y = 0} where
  toFun x := ⟨φ f.leadingCoeff * x, (monicScaling_root_iff f hd φ ha x).2 x.property⟩
  invFun y := ⟨(φ f.leadingCoeff)⁻¹ * y, by
    apply (monicScaling_root_iff f hd φ ha _).1
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact inv_mul_cancel_left₀ ha x
  right_inv y := by
    apply Subtype.ext
    exact mul_inv_cancel_left₀ ha y

/-- At a prime not dividing the leading coefficient, monic scaling preserves
the modular root count. The statement also applies to arbitrary finite fields. -/
theorem monicScaling_rootCount {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : ℤ[X]) (hd : 1 ≤ f.natDegree) (φ : ℤ →+* K) (ha : φ f.leadingCoeff ≠ 0) :
    rootCount (f.map φ) = rootCount (f.integralNormalization.map φ) := by
  classical
  have h := Fintype.card_congr (monicScaling_rootEquiv f hd φ ha)
  simpa only [rootCount, Fintype.card_subtype, eval_map] using h

/-- The concrete good-prime root-count bridge used in Lemma 3.2. -/
theorem monicScaling_mod_rootCount (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (p : ℕ) [Fact p.Prime] (ha : ¬(p : ℤ) ∣ f.leadingCoeff) :
    rootCount (f.map (Int.castRingHom (ZMod p))) =
      rootCount (f.integralNormalization.map (Int.castRingHom (ZMod p))) := by
  apply monicScaling_rootCount f hd
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd f.leadingCoeff p).not.mpr ha

/-- A polynomial identity for the substitution; unlike division notation it
also makes sense over the original integer coefficient ring. -/
theorem monicScaling_comp_mul_X (f : ℤ[X]) (hd : 1 ≤ f.natDegree) :
    f.integralNormalization.comp (C f.leadingCoeff * X) =
      C (f.leadingCoeff ^ (f.natDegree - 1)) * f := by
  ext i
  rw [comp_C_mul_X_coeff, coeff_C_mul]
  exact (integralNormalization_coeff_mul_leadingCoeff_pow i hd).trans (mul_comm _ _)

/-- Irreducibility over the rationals survives the integral monic scaling. -/
theorem monicScaling_irreducible (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) : Irreducible f.integralNormalization := by
  have hf : f ≠ 0 := ne_zero_of_natDegree_gt hd
  have ha : (f.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hf
  let _ : Invertible (f.leadingCoeff : ℚ) := invertibleOfNonzero ha
  let e := algEquivCMulXAddC (f.leadingCoeff : ℚ) 0
  have he : e (f.integralNormalization.map (Int.castRingHom ℚ)) =
      C ((f.leadingCoeff : ℚ) ^ (f.natDegree - 1)) * f.map (Int.castRingHom ℚ) := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) (monicScaling_comp_mul_X f hd)
    simpa [e, algEquivCMulXAddC_apply, ← comp_eq_aeval, Polynomial.map_comp] using h
  have hi : Irreducible (e (f.integralNormalization.map (Int.castRingHom ℚ))) := by
    rw [he]
    apply (irreducible_isUnit_mul ?_).2 hirr
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha)).map C
  have himap : Irreducible (f.integralNormalization.map (Int.castRingHom ℚ)) :=
    (MulEquiv.irreducible_iff (f := e.toRingEquiv.toMulEquiv)).mp hi
  exact (monic_integralNormalization hf).irreducible_iff_irreducible_map_fraction_map.mpr himap

/-- The scaled root is integral, although the root of the original nonmonic
polynomial need not itself be an algebraic integer. -/
theorem monicScaling_root_isIntegral {K : Type*} [Field K] [Algebra ℤ K]
    (f : ℤ[X]) (hf : f ≠ 0) (hd : 1 ≤ f.natDegree) (x : K)
    (hx : f.aeval x = 0) : IsIntegral ℤ (algebraMap ℤ K f.leadingCoeff * x) := by
  change f.eval₂ (algebraMap ℤ K) x = 0 at hx
  refine ⟨f.integralNormalization, monic_integralNormalization hf, ?_⟩
  simpa only [aeval_def] using
    (monicScaling_eval f hd (algebraMap ℤ K) x).trans (by rw [hx]; ring)

/-- The derivative transforms with one factor of the original leading coefficient.
This identity is proved coefficientwise and supplies the resultant argument. -/
theorem monicScaling_derivative (f : ℤ[X]) (hd : 1 ≤ f.natDegree) :
    f.derivative.scaleRoots f.leadingCoeff =
      C f.leadingCoeff * f.integralNormalization.derivative := by
  ext i
  rw [coeff_scaleRoots, natDegree_derivative, coeff_C_mul, coeff_derivative,
    coeff_derivative]
  rcases lt_trichotomy (i + 1) f.natDegree with hi | hi | hi
  · rw [integralNormalization_coeff_ne_natDegree (by omega)]
    have he : f.natDegree - 1 - i = (f.natDegree - 1 - (i + 1)) + 1 := by omega
    rw [he, pow_succ]
    ring
  · rw [hi, integralNormalization_coeff_natDegree (ne_zero_of_natDegree_gt hd),
      coeff_natDegree, show f.natDegree - 1 - i = 0 by omega, pow_zero]
    ring
  · rw [coeff_eq_zero_of_natDegree_lt hi,
      integralNormalization_coeff_ne_natDegree (by omega)]
    rw [coeff_eq_zero_of_natDegree_lt hi]
    ring

/-- The discriminant scaling formula in Lemma 3.1, including degree one. -/
theorem monicScaling_discr (f : ℤ[X]) (hd : 1 ≤ f.natDegree) :
    f.integralNormalization.discr =
      f.leadingCoeff ^ ((f.natDegree - 1) * (f.natDegree - 2)) * f.discr := by
  have hf : f ≠ 0 := ne_zero_of_natDegree_gt hd
  have ha : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  let d := f.natDegree
  let a := f.leadingCoeff
  let g := f.integralNormalization
  have hg : g.Monic := monic_integralNormalization hf
  have hgd : g.natDegree = d := natDegree_integralNormalization
  by_cases hd₁ : d = 1
  · have hfd : f.degree = 1 := by rw [degree_eq_natDegree hf]; exact_mod_cast hd₁
    have hgd₁ : g.degree = 1 := by rw [degree_eq_natDegree hg.ne_zero, hgd, hd₁]; rfl
    change g.discr = a ^ ((d - 1) * (d - 2)) * f.discr
    rw [discr_of_degree_eq_one hfd, discr_of_degree_eq_one hgd₁, hd₁]
    norm_num
  have hd₂ : 2 ≤ d := by dsimp [d] at *; omega
  have hres := resultant_integralNormalization f.derivative f (by omega : f.natDegree ≠ 0)
  simp only [natDegree_scaleRoots, natDegree_integralNormalization, natDegree_derivative] at hres
  rw [monicScaling_derivative f hd, resultant_C_mul_left] at hres
  change a ^ d * g.derivative.resultant g (d - 1) d =
    a ^ ((d - 1) * (d - 1)) * f.derivative.resultant f (d - 1) d at hres
  rw [resultant_comm g.derivative g (d - 1) d,
    resultant_comm f.derivative f (d - 1) d] at hres
  have hfg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hd
  have hgg : 0 < g.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  have hrf := resultant_deriv hfg
  have hrg := resultant_deriv hgg
  change f.resultant f.derivative d (d - 1) = _ at hrf
  rw [hgd, hg.leadingCoeff, mul_one] at hrg
  rw [hrf, hrg] at hres
  let s : ℤ := (-1) ^ ((d - 1) * d) * (-1) ^ (d * (d - 1) / 2)
  have hs : s ≠ 0 := by dsimp [s]; positivity
  have heq : a ^ d * g.discr = a ^ ((d - 1) * (d - 1)) * a * f.discr := by
    apply mul_left_cancel₀ hs
    dsimp [s]
    calc
      _ = a ^ d * ((-1) ^ ((d - 1) * d) *
          ((-1) ^ (d * (d - 1) / 2) * g.discr)) := by ring
      _ = _ := hres
      _ = _ := by ring
  have hexp : d + (d - 1) * (d - 2) = (d - 1) * (d - 1) + 1 := by
    have h₁ := Nat.sub_add_cancel (show 1 ≤ d by omega)
    have h₂ := Nat.sub_add_cancel hd₂
    nlinarith
  change g.discr = a ^ ((d - 1) * (d - 2)) * f.discr
  apply mul_left_cancel₀ (pow_ne_zero d ha)
  rw [← mul_assoc, ← pow_add, hexp, pow_succ]
  exact heq

/-- A good prime for the original nonmonic polynomial also avoids the
discriminant of its integral monic scaling. -/
theorem monicScaling_not_dvd_discr (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (p : ℕ) [Fact p.Prime] (ha : ¬(p : ℤ) ∣ f.leadingCoeff)
    (hdisc : ¬(p : ℤ) ∣ f.discr) : ¬(p : ℤ) ∣ f.integralNormalization.discr := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd f.integralNormalization.discr p).not.mp
  rw [monicScaling_discr f hd, Int.cast_mul, Int.cast_pow]
  exact mul_ne_zero
    (pow_ne_zero _ ((ZMod.intCast_zmod_eq_zero_iff_dvd f.leadingCoeff p).not.mpr ha))
    ((ZMod.intCast_zmod_eq_zero_iff_dvd f.discr p).not.mpr hdisc)

/-- Reduction at a good prime preserves the common degree on both sides of
the change of variable. -/
theorem monicScaling_mod_degrees (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (p : ℕ) [Fact p.Prime] (ha : ¬(p : ℤ) ∣ f.leadingCoeff) :
    (f.map (Int.castRingHom (ZMod p))).natDegree = f.natDegree ∧
      (f.integralNormalization.map (Int.castRingHom (ZMod p))).natDegree = f.natDegree := by
  have hne : (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd f.leadingCoeff p).not.mpr ha
  refine ⟨natDegree_map_of_leadingCoeff_ne_zero _ hne, ?_⟩
  have hm : f.integralNormalization.Monic :=
    monic_integralNormalization (ne_zero_of_natDegree_gt hd)
  rw [natDegree_map_of_leadingCoeff_ne_zero _ (by simp [hm.leadingCoeff]),
    natDegree_integralNormalization]

/-- The number-field discriminant divides the discriminant of any integral
family of the correct size. Independence of the family is unnecessary: a
dependent family simply has discriminant zero. The proof constructs the integer
coordinate matrix in an integral basis and extracts its squared determinant. -/
theorem numberField_discr_dvd_integral_family (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → NumberField.RingOfIntegers K)
    (hcard : Fintype.card ι = Module.finrank ℚ K) :
    NumberField.discr K ∣ Algebra.discr ℤ v := by
  classical
  let b₀ := NumberField.RingOfIntegers.basis K
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) =
      Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b₀, NumberField.RingOfIntegers.rank, hcard]
  let b := b₀.reindex (Fintype.equivOfCardEq hc)
  let M : Matrix ι ι ℤ := fun i j ↦ b.repr (v i) j
  have hMv : (M.map (algebraMap ℤ (NumberField.RingOfIntegers K))).mulVec b = v := by
    funext i
    simpa [M, Matrix.mulVec, dotProduct, Matrix.map, Algebra.smul_def] using b.sum_repr (v i)
  have hb : Algebra.discr ℤ (fun i ↦ b i) = NumberField.discr K :=
    NumberField.discr_eq_discr K b
  rw [← hMv, Algebra.discr_of_matrix_mulVec, hb]
  exact dvd_mul_left _ _

/-- In particular, the field discriminant divides the discriminant of the
power family of any algebraic integer. This is the order-discriminant
divisibility step; identifying that power-family discriminant with the
polynomial discriminant is a separate resultant identity. -/
theorem numberField_discr_dvd_power_family (K : Type*) [Field K] [NumberField K]
    (β : NumberField.RingOfIntegers K) :
    NumberField.discr K ∣
      Algebra.discr ℤ (fun i : Fin (Module.finrank ℚ K) ↦ β ^ (i : ℕ)) := by
  exact numberField_discr_dvd_integral_family K _ (Fintype.card_fin _)

end SparseIrred.UpperBounds
