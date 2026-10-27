import SparseIrred.LargeGap.Statement
import SparseIrred.Construction.Norm

/-!
# ③ The hypotheses of the large-gap theorem for `c = 1 - X^N`, `d = A`, `L = M + N`

Notes p. 8: "Take `c = 1 - X^N`, `d = A`, and `L = M + N`, so `c̃ = B` and
`X^L c(X⁻¹) + d = H_M`.  In the unsatisfiable case, (2) supplies coprimality, and `c(0) d(0) ≠ 0`
was proved above.  Since every coefficient of `A` is divisible by `3` while `c` has a coefficient
`-1`, `c ≠ ±d`.  Every zero of the squarefree `B` is a simple pole of `d/c(X⁻¹) = X^N A / B` and
its negative, because `A` is coprime to `B` and `X` is nonzero there.  A rational-function `k`-th
power has all pole orders divisible by `k`; multiplying a fourth power by `4` does not change this.
Hence the pair is non-Capellian."  and "Equation (3) therefore gives
`L = M + N > max(L₀, L₁, N + deg A)` and `M > deg A`."

The bounds are proved as exact real inequalities (no decimal approximations are assumed); the only
numerical input is a rational bracket `117/100 < θ` for the Lehmer root, obtained from the
intermediate value theorem.
-/

open Polynomial

namespace SparseIrred

open Complexity.SAT

/-! ### Lehmer's constant -/

private theorem aeval_lehmerPoly (x : ℝ) :
    aeval x lehmerPoly = x ^ 10 + x ^ 9 - x ^ 7 - x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 + x + 1 := by
  simp [lehmerPoly]

/-- Lehmer's polynomial has a real root in `(117/100, 118/100)` (intermediate value theorem). -/
theorem exists_lehmerPoly_root :
    ∃ θ : ℝ, 117 / 100 < θ ∧ θ < 118 / 100 ∧ aeval θ lehmerPoly = 0 := by
  set f : ℝ → ℝ := fun x => x ^ 10 + x ^ 9 - x ^ 7 - x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 + x + 1 with hf
  have hcont : ContinuousOn f (Set.Icc (117 / 100) (118 / 100)) := by
    rw [hf]; fun_prop
  have hivt := intermediate_value_Ioo (show (117 / 100 : ℝ) ≤ 118 / 100 by norm_num) hcont
  have h0 : (0 : ℝ) ∈ Set.Ioo (f (117 / 100)) (f (118 / 100)) := by
    rw [hf]; constructor <;> norm_num
  obtain ⟨θ, ⟨h1, h2⟩, hθ⟩ := hivt h0
  exact ⟨θ, h1, h2, by rw [aeval_lehmerPoly]; exact hθ⟩

/-- Lehmer's polynomial is reciprocal: `L(x) = x^5 Q(x + x⁻¹)` with
`Q(2 + s) = -1 + 36 s + 69 s^2 + 43 s^3 + 11 s^4 + s^5`. -/
private theorem aeval_lehmerPoly_eq_Q (x : ℝ) (hx : x ≠ 0) :
    aeval x lehmerPoly = x ^ 5 * (-1 + 36 * (x + x⁻¹ - 2) + 69 * (x + x⁻¹ - 2) ^ 2 +
      43 * (x + x⁻¹ - 2) ^ 3 + 11 * (x + x⁻¹ - 2) ^ 4 + (x + x⁻¹ - 2) ^ 5) := by
  rw [aeval_lehmerPoly]
  field_simp
  ring

/-- `s ↦ Q(2 + s)` is strictly increasing on `[0, ∞)`. -/
private theorem lehmerQ_strictMono {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    -1 + 36 * s + 69 * s ^ 2 + 43 * s ^ 3 + 11 * s ^ 4 + s ^ 5 <
      -1 + 36 * t + 69 * t ^ 2 + 43 * t ^ 3 + 11 * t ^ 4 + t ^ 5 := by
  have h2 : s ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs hst.le 2
  have h3 : s ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ hs hst.le 3
  have h4 : s ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hs hst.le 4
  have h5 : s ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ hs hst.le 5
  linarith

/-- Lehmer's polynomial has no two roots `1 < θ₁ < θ₂`: `θ ↦ θ + θ⁻¹ - 2` is nonnegative and
strictly increasing on `(1, ∞)`, and `s ↦ Q(2 + s)` is strictly increasing on `[0, ∞)`. -/
private theorem lehmerPoly_root_lt_false {θ₁ θ₂ : ℝ} (h₁ : 1 < θ₁) (h12 : θ₁ < θ₂)
    (hr₁ : aeval θ₁ lehmerPoly = 0) (hr₂ : aeval θ₂ lehmerPoly = 0) : False := by
  have h₂ : 1 < θ₂ := h₁.trans h12
  have hp₁ : 0 < θ₁ := by linarith
  have hp₂ : 0 < θ₂ := by linarith
  rw [aeval_lehmerPoly_eq_Q θ₁ hp₁.ne'] at hr₁
  rw [aeval_lehmerPoly_eq_Q θ₂ hp₂.ne'] at hr₂
  have hs0 : 0 ≤ θ₁ + θ₁⁻¹ - 2 := by
    have : θ₁ + θ₁⁻¹ - 2 = (θ₁ - 1) ^ 2 / θ₁ := by field_simp; ring
    rw [this]; positivity
  have hs : θ₁ + θ₁⁻¹ - 2 < θ₂ + θ₂⁻¹ - 2 := by
    have : θ₂ + θ₂⁻¹ - 2 - (θ₁ + θ₁⁻¹ - 2) = (θ₂ - θ₁) * (θ₁ * θ₂ - 1) / (θ₁ * θ₂) := by
      field_simp; ring
    have hpos : 0 < (θ₂ - θ₁) * (θ₁ * θ₂ - 1) / (θ₁ * θ₂) := by
      apply div_pos _ (mul_pos hp₁ hp₂)
      apply mul_pos (by linarith)
      nlinarith
    linarith
  have hQ := lehmerQ_strictMono hs0 hs
  have e₁ := (mul_eq_zero.1 hr₁).resolve_left (pow_ne_zero 5 hp₁.ne')
  have e₂ := (mul_eq_zero.1 hr₂).resolve_left (pow_ne_zero 5 hp₂.ne')
  linarith

/-- Lehmer's polynomial has exactly one real root `> 1`. -/
theorem lehmerPoly_root_unique {θ₁ θ₂ : ℝ} (h₁ : 1 < θ₁) (h₂ : 1 < θ₂)
    (hr₁ : aeval θ₁ lehmerPoly = 0) (hr₂ : aeval θ₂ lehmerPoly = 0) : θ₁ = θ₂ := by
  rcases lt_trichotomy θ₁ θ₂ with h | h | h
  · exact (lehmerPoly_root_lt_false h₁ h hr₁ hr₂).elim
  · exact h
  · exact (lehmerPoly_root_lt_false h₂ h hr₂ hr₁).elim

/-! ### The individual hypotheses -/

/-- `c̃ = B`. -/
theorem reverse_cPoly (Φ : CNF) : (cPoly Φ).reverse = Bpoly Φ := by
  have h : cPoly Φ = -X ^ bigN Φ + C 1 := by simp [cPoly]; ring
  rw [h, reverse_add_C, reverse_neg]
  have h1 : (X ^ bigN Φ : ℤ[X]).reverse = 1 := by
    have := reverse_X_pow_mul (1 : ℤ[X]) (bigN Φ)
    rw [mul_one] at this
    rw [this, ← C_1, reverse_C]
  rw [h1, natDegree_neg, natDegree_X_pow, Bpoly]; simp; ring

/-- `deg c = N`. -/
theorem natDegree_cPoly (Φ : CNF) : (cPoly Φ).natDegree = bigN Φ := by
  rw [cPoly, ← neg_sub, natDegree_neg, ← C_1, natDegree_X_pow_sub_C]

private theorem cPoly_coeff_zero_eq_one (Φ : CNF) : (cPoly Φ).coeff 0 = 1 := by
  simp [cPoly, coeff_one, coeff_X_pow, (bigN_pos Φ).ne]

/-- `c(0) ≠ 0`. -/
theorem cPoly_coeff_zero (Φ : CNF) : (cPoly Φ).coeff 0 ≠ 0 := by
  rw [cPoly_coeff_zero_eq_one]; exact one_ne_zero

private theorem Bpoly_coeff_zero (Φ : CNF) : (Bpoly Φ).coeff 0 = -1 := by
  simp [Bpoly, coeff_one, coeff_X_pow, (bigN_pos Φ).ne]

private theorem isCoprime_of_unsat (Φ : CNF) (hunsat : ¬Φ.Satisfiable) :
    IsCoprime ((Apoly Φ).map (Int.castRingHom ℚ)) ((Bpoly Φ).map (Int.castRingHom ℚ)) := by
  by_contra h
  exact hunsat ((satisfiable_iff_not_isCoprime Φ).2 h)

/-- In the unsatisfiable case, `gcd_{ℤ[X]}(c̃, d) = 1`. -/
theorem isRelPrime_reverse_cPoly_Apoly (Φ : CNF) (hunsat : ¬Φ.Satisfiable) :
    IsRelPrime (cPoly Φ).reverse (Apoly Φ) := by
  rw [reverse_cPoly]
  have hcop := isCoprime_of_unsat Φ hunsat
  intro g hgB hgA
  have hunit : IsUnit (g.map (Int.castRingHom ℚ)) :=
    hcop.isRelPrime (Polynomial.map_dvd _ hgA) (Polynomial.map_dvd _ hgB)
  have hdeg : g.natDegree = 0 := by
    have := natDegree_eq_zero_of_isUnit hunit
    rwa [natDegree_map_eq_of_injective (RingHom.injective_int _)] at this
  rw [eq_C_of_natDegree_eq_zero hdeg] at hgB ⊢
  apply Polynomial.isUnit_C.2
  have := (C_dvd_iff_dvd_coeff _ _).1 hgB 0
  rw [Bpoly_coeff_zero] at this
  exact isUnit_of_dvd_unit this (by simp)

/-- `c ≠ d`: every coefficient of `A` is divisible by `3`, while `c(0) = 1`. -/
theorem cPoly_ne_Apoly (Φ : CNF) : cPoly Φ ≠ Apoly Φ := by
  intro h
  have h3 := three_dvd_Apoly_coeff Φ 0
  rw [← h, cPoly_coeff_zero_eq_one] at h3
  norm_num at h3

/-- `c ≠ -d`. -/
theorem cPoly_ne_neg_Apoly (Φ : CNF) : cPoly Φ ≠ -Apoly Φ := by
  intro h
  have h3 := three_dvd_Apoly_coeff Φ 0
  have hA : Apoly Φ = -cPoly Φ := by rw [h, neg_neg]
  rw [hA, coeff_neg, cPoly_coeff_zero_eq_one] at h3
  norm_num at h3

private theorem rootMultiplicity_pow {K : Type*} [Field K] (p : K[X]) (a : K) (n : ℕ) :
    rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  classical
  rw [← count_roots, roots_pow, Multiset.count_nsmul, count_roots]

private theorem rootMultiplicity_one_X_pow_sub_one (N : ℕ) (hN : 0 < N) :
    rootMultiplicity (1 : ℚ) (X ^ N - 1) = 1 := by
  have hsep : (X ^ N - 1 : ℚ[X]).Separable :=
    X_pow_sub_one_separable_iff.2 (by exact_mod_cast hN.ne')
  have hne : (X ^ N - 1 : ℚ[X]) ≠ 0 := X_pow_sub_C_ne_zero hN 1
  have hle := rootMultiplicity_le_one_of_separable hsep 1
  have hpos : 0 < rootMultiplicity (1 : ℚ) (X ^ N - 1) :=
    (rootMultiplicity_pos hne).2 (by simp)
  omega

/-- `c X^N A / (X^N - 1)` is not a `p`-th power in `ℚ(X)` for `p ≥ 2` when `A(1) ≠ 0`: the root
multiplicity at `1` of the denominator is `1`. -/
private theorem not_pow_of_rootMultiplicity (A : ℚ[X]) (N p : ℕ) (hN : 0 < N) (hp : 2 ≤ p)
    (hA : A.eval 1 ≠ 0) (c : ℚ) (hc : c ≠ 0) (g : RatFunc ℚ) :
    algebraMap ℚ[X] (RatFunc ℚ) (C c * X ^ N * A) / algebraMap ℚ[X] (RatFunc ℚ) (X ^ N - 1)
      ≠ g ^ p := by
  intro h
  have hB : (X ^ N - 1 : ℚ[X]) ≠ 0 := X_pow_sub_C_ne_zero hN 1
  have hA0 : A ≠ 0 := fun h0 => hA (by simp [h0])
  have hL : (C c * X ^ N * A : ℚ[X]) ≠ 0 := by
    simp [hc, hA0, X_ne_zero]
  rw [← RatFunc.num_div_denom g, div_pow, ← map_pow, ← map_pow,
    div_eq_div_iff (RatFunc.algebraMap_ne_zero hB)
      (RatFunc.algebraMap_ne_zero (pow_ne_zero _ (RatFunc.denom_ne_zero g))),
    ← map_mul, ← map_mul] at h
  have h' := RatFunc.algebraMap_injective ℚ h
  have hnum : g.num ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega), zero_mul] at h'
    exact mul_ne_zero hL (pow_ne_zero _ (RatFunc.denom_ne_zero g)) h'
  have := congrArg (rootMultiplicity (1 : ℚ)) h'
  rw [rootMultiplicity_mul (mul_ne_zero hL (pow_ne_zero _ (RatFunc.denom_ne_zero g))),
    rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hnum) hB),
    rootMultiplicity_pow, rootMultiplicity_pow, rootMultiplicity_one_X_pow_sub_one N hN,
    rootMultiplicity_eq_zero (p := C c * X ^ N * A) (by simp [hc, hA])] at this
  have hdvd : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_right p _)).1 (by rw [← this]; simp)
  have := Nat.le_of_dvd one_pos hdvd
  omega

/-- `d / c(X⁻¹) = X^N A / B` in `ℚ(X)`. -/
private theorem toRatFunc_div_invSubst (Φ : CNF) :
    toRatFunc (Apoly Φ) / invSubst (cPoly Φ) =
      algebraMap ℚ[X] (RatFunc ℚ) (X ^ bigN Φ * (Apoly Φ).map (Int.castRingHom ℚ)) /
        algebraMap ℚ[X] (RatFunc ℚ) (X ^ bigN Φ - 1) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hB : (RatFunc.X : RatFunc ℚ) ^ bigN Φ - 1 ≠ 0 := by
    have := RatFunc.algebraMap_ne_zero (K := ℚ) (X_pow_sub_C_ne_zero (bigN_pos Φ) (1 : ℚ))
    simpa using this
  simp only [toRatFunc, invSubst, cPoly, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X, eval₂_sub, eval₂_one, eval₂_pow, eval₂_X, map_mul,
    map_pow, map_sub, map_one, RatFunc.algebraMap_X]
  have h1 : 1 - (RatFunc.X : RatFunc ℚ)⁻¹ ^ bigN Φ =
      (RatFunc.X ^ bigN Φ - 1) / RatFunc.X ^ bigN Φ := by
    rw [eq_div_iff (pow_ne_zero _ hX), sub_mul, one_mul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hX)]
  rw [h1, div_div_eq_mul_div, mul_comm]

/-- In the unsatisfiable case the pair `(c, d)` is not Capellian. -/
theorem not_capellian (Φ : CNF) (hunsat : ¬Φ.Satisfiable) :
    ¬Capellian (cPoly Φ) (Apoly Φ) := by
  have hA1 : ((Apoly Φ).map (Int.castRingHom ℚ)).eval 1 ≠ 0 := by
    obtain ⟨u, v, huv⟩ := isCoprime_of_unsat Φ hunsat
    intro h0
    have := congrArg (eval 1) huv
    simp [eval_add, eval_mul, h0, Bpoly] at this
  rintro (⟨p, hp, r, hr⟩ | ⟨r, hr⟩)
  · rw [toRatFunc_div_invSubst] at hr
    apply not_pow_of_rootMultiplicity _ (bigN Φ) p (bigN_pos Φ) hp.two_le hA1 (-1)
      (by norm_num) r
    rw [← hr, C_neg, C_1, neg_one_mul, neg_mul, map_neg, neg_div]
  · rw [toRatFunc_div_invSubst] at hr
    apply not_pow_of_rootMultiplicity _ (bigN Φ) 4 (bigN_pos Φ) (by norm_num) hA1 (1 / 4)
      (by norm_num) r
    rw [mul_assoc, map_mul, mul_div_assoc, hr, RatFunc.algebraMap_C]
    rw [← mul_assoc, ← map_ofNat RatFunc.C 4, ← map_mul]
    norm_num

/-! ### The choice of `M` -/

/-- `2/13 < log (117/100)`, via `exp (2/13) < 117/100`. -/
private theorem two_div_thirteen_lt_log : (2 / 13 : ℝ) < Real.log (117 / 100) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_bound' (x := 2 / 13) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  refine lt_of_le_of_lt h ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- `2 / log θ < 13` for `θ > 117/100`. -/
private theorem two_div_log_lt {θ : ℝ} (hθ : 117 / 100 < θ) : 2 / Real.log θ < 13 := by
  have h1 : Real.log (117 / 100) < Real.log θ := Real.log_lt_log (by norm_num) hθ
  have h2 := two_div_thirteen_lt_log
  have hpos : 0 < Real.log θ := by linarith
  rw [div_lt_iff₀ hpos]
  linarith

/-- The FFK part of the bound: `2 max {5^{4w-15}, m (5^{2w-8} + 1/4)} < 2^{20(w+1)} (m+1)^6`. -/
private theorem ffk_part_lt (w m : ℕ) :
    2 * max ((5 : ℝ) ^ (4 * (w : ℤ) - 15)) ((m : ℝ) * ((5 : ℝ) ^ (2 * (w : ℤ) - 8) + 1 / 4)) <
      (2 : ℝ) ^ (20 * (w + 1)) * ((m : ℝ) + 1) ^ 6 := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm6 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 6 := one_le_pow₀ (by linarith)
  have hmm6 : (m : ℝ) < ((m : ℝ) + 1) ^ 6 := by
    calc (m : ℝ) < (m : ℝ) + 1 := by linarith
      _ = ((m : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((m : ℝ) + 1) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hA : (5 : ℝ) ^ (4 * (w : ℤ) - 15) < (5 : ℝ) ^ (4 * w) := by
    rw [← zpow_natCast]
    apply zpow_lt_zpow_right₀ (by norm_num)
    push_cast; linarith
  have hB : (5 : ℝ) ^ (2 * (w : ℤ) - 8) + 1 / 4 < (5 : ℝ) ^ (2 * w) := by
    rw [zpow_sub₀ (by norm_num), show (2 * (w : ℤ)) = ((2 * w : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
    have : (1 : ℝ) ≤ 5 ^ (2 * w) := one_le_pow₀ (by norm_num)
    have h8 : ((5 : ℝ) ^ (8 : ℤ)) = 390625 := by norm_num
    rw [h8]
    rw [div_add' _ _ _ (by norm_num), div_lt_iff₀ (by norm_num)]
    nlinarith
  have h625 : (5 : ℝ) ^ (4 * w) ≤ 2 ^ (10 * w) := by
    rw [pow_mul, pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) w
  have h25 : (5 : ℝ) ^ (2 * w) ≤ 2 ^ (5 * w) := by
    rw [pow_mul, pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) w
  have hp1 : 2 * (2 : ℝ) ^ (10 * w) ≤ 2 ^ (20 * (w + 1)) := by
    rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hp2 : 2 * (2 : ℝ) ^ (5 * w) ≤ 2 ^ (20 * (w + 1)) := by
    rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hP : (0 : ℝ) < 2 ^ (20 * (w + 1)) := by positivity
  have h5B : (0 : ℝ) ≤ 5 ^ (2 * w) := by positivity
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), max_lt_iff]
  constructor
  · nlinarith
  · have e1 : 2 * ((m : ℝ) * ((5 : ℝ) ^ (2 * (w : ℤ) - 8) + 1 / 4)) ≤
        (m : ℝ) * (2 * (2 : ℝ) ^ (5 * w)) := by nlinarith
    have e2 : (m : ℝ) * (2 * (2 : ℝ) ^ (5 * w)) ≤ (m : ℝ) * 2 ^ (20 * (w + 1)) :=
      mul_le_mul_of_nonneg_left hp2 hm0
    nlinarith

/-- The Corollary 1.3 part of the bound. -/
private theorem sss_part_lt {θ : ℝ} (hθ : 117 / 100 < θ) (m dA w : ℕ) (hdA : dA ≤ m) {W : ℝ}
    (hW0 : 0 ≤ W) (hWw : W ≤ w) :
    (dA : ℝ) + (if m ≤ 27 then 2 * (m : ℝ) / Real.log θ * Real.log W
      else (m : ℝ) * Real.log (6 * (m : ℝ)) ^ 3 * Real.log W) <
      (2 : ℝ) ^ (20 * (w + 1)) * ((m : ℝ) + 1) ^ 6 := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlogθ : 0 < Real.log θ := Real.log_pos (by linarith)
  have h13 := two_div_log_lt hθ
  -- `E ≤ 216 m^4 W`
  have hE : (if m ≤ 27 then 2 * (m : ℝ) / Real.log θ * Real.log W
      else (m : ℝ) * Real.log (6 * (m : ℝ)) ^ 3 * Real.log W) ≤ 216 * (m : ℝ) ^ 4 * W := by
    have hlogW : Real.log W ≤ W := Real.log_le_self hW0
    have hRHS : 0 ≤ 216 * (m : ℝ) ^ 4 * W := by positivity
    rcases le_or_gt (Real.log W) 0 with hl | hl
    · split_ifs with hm
      · have : 0 ≤ 2 * (m : ℝ) / Real.log θ := by positivity
        nlinarith
      · have h6 : 0 ≤ Real.log (6 * (m : ℝ)) := by
          apply Real.log_nonneg
          have : (28 : ℝ) ≤ m := by exact_mod_cast (show 28 ≤ m by omega)
          linarith
        have : 0 ≤ (m : ℝ) * Real.log (6 * (m : ℝ)) ^ 3 := by positivity
        nlinarith
    · split_ifs with hm
      · have e1 : 2 * (m : ℝ) / Real.log θ = (m : ℝ) * (2 / Real.log θ) := by ring
        have e2 : (m : ℝ) * (2 / Real.log θ) ≤ (m : ℝ) * 13 :=
          mul_le_mul_of_nonneg_left h13.le hm0
        have e3 : 2 * (m : ℝ) / Real.log θ * Real.log W ≤ (m : ℝ) * 13 * W := by
          rw [e1]
          calc (m : ℝ) * (2 / Real.log θ) * Real.log W ≤ (m : ℝ) * 13 * Real.log W :=
                mul_le_mul_of_nonneg_right e2 hl.le
            _ ≤ (m : ℝ) * 13 * W := mul_le_mul_of_nonneg_left hlogW (by positivity)
        have e4 : (m : ℝ) * 13 ≤ 216 * (m : ℝ) ^ 4 := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · subst h0; simp
          · have : (1 : ℝ) ≤ m := by exact_mod_cast h0
            have : (m : ℝ) ≤ (m : ℝ) ^ 4 := by
              calc (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
                _ ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ this (by norm_num)
            linarith
        calc 2 * (m : ℝ) / Real.log θ * Real.log W ≤ (m : ℝ) * 13 * W := e3
          _ ≤ 216 * (m : ℝ) ^ 4 * W := mul_le_mul_of_nonneg_right e4 hW0
      · have hm1 : (1 : ℝ) ≤ 6 * (m : ℝ) := by
          have : (28 : ℝ) ≤ m := by exact_mod_cast (show 28 ≤ m by omega)
          linarith
        have h6 : 0 ≤ Real.log (6 * (m : ℝ)) := Real.log_nonneg hm1
        have h6' : Real.log (6 * (m : ℝ)) ≤ 6 * (m : ℝ) := Real.log_le_self (by linarith)
        have h63 : Real.log (6 * (m : ℝ)) ^ 3 ≤ (6 * (m : ℝ)) ^ 3 := pow_le_pow_left₀ h6 h6' 3
        calc (m : ℝ) * Real.log (6 * (m : ℝ)) ^ 3 * Real.log W
            ≤ (m : ℝ) * (6 * (m : ℝ)) ^ 3 * Real.log W := by
              apply mul_le_mul_of_nonneg_right _ hl.le
              exact mul_le_mul_of_nonneg_left h63 hm0
          _ ≤ (m : ℝ) * (6 * (m : ℝ)) ^ 3 * W := mul_le_mul_of_nonneg_left hlogW (by positivity)
          _ = 216 * (m : ℝ) ^ 4 * W := by ring
  have hdA' : (dA : ℝ) ≤ m := by exact_mod_cast hdA
  -- `2^{20(w+1)} ≥ 2^20 (w+1)`
  have hw2 : (2 : ℝ) ^ 20 * ((w : ℝ) + 1) ≤ 2 ^ (20 * (w + 1)) := by
    have hnat : w + 1 ≤ 2 ^ (20 * w) := by
      calc w + 1 ≤ 2 ^ w := Nat.lt_two_pow_self
        _ ≤ 2 ^ (20 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : ((w : ℝ) + 1) ≤ 2 ^ (20 * w) := by exact_mod_cast hnat
    rw [show 20 * (w + 1) = 20 + 20 * w by ring, pow_add]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hm4 : (m : ℝ) ^ 4 ≤ ((m : ℝ) + 1) ^ 6 := by
    calc (m : ℝ) ^ 4 ≤ ((m : ℝ) + 1) ^ 4 := pow_le_pow_left₀ hm0 (by linarith) 4
      _ ≤ ((m : ℝ) + 1) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hmm6 : (m : ℝ) < ((m : ℝ) + 1) ^ 6 := by
    calc (m : ℝ) < (m : ℝ) + 1 := by linarith
      _ = ((m : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((m : ℝ) + 1) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hm6pos : (0 : ℝ) < ((m : ℝ) + 1) ^ 6 := by positivity
  have hWm : 216 * (m : ℝ) ^ 4 * W ≤ 216 * ((m : ℝ) + 1) ^ 6 * w := by
    have : (m : ℝ) ^ 4 * W ≤ ((m : ℝ) + 1) ^ 6 * w :=
      mul_le_mul hm4 hWw hW0 hm6pos.le
    linarith
  calc (dA : ℝ) + _ ≤ (m : ℝ) + 216 * ((m : ℝ) + 1) ^ 6 * w := by linarith
    _ < ((m : ℝ) + 1) ^ 6 * (2 ^ 20 * ((w : ℝ) + 1)) := by nlinarith
    _ ≤ ((m : ℝ) + 1) ^ 6 * 2 ^ (20 * (w + 1)) := mul_le_mul_of_nonneg_left hw2 hm6pos.le
    _ = (2 : ℝ) ^ (20 * (w + 1)) * ((m : ℝ) + 1) ^ 6 := by ring

/-- `M = 2^{20(w+1)} (m+1)^6` makes `L = M + N` exceed both explicit bounds. -/
theorem bound_lt_Mval_add (Φ : CNF) {θ : ℝ} (hθ : 117 / 100 < θ) :
    max (ffkBound (cPoly Φ) (Apoly Φ)) (sssN1 θ (cPoly Φ) (Apoly Φ)) <
      ((Mval Φ + bigN Φ : ℕ) : ℝ) := by
  have hwz : ((weight (cPoly Φ) : ℤ) + (weight (Apoly Φ) : ℤ) + (termCount (cPoly Φ) : ℤ) +
      (termCount (Apoly Φ) : ℤ)) = (wParam Φ : ℤ) := by
    simp [wParam]
  have hWw : ((weight (cPoly Φ) : ℝ) + (weight (Apoly Φ) : ℝ)) ≤ (wParam Φ : ℝ) := by
    simp only [wParam]; push_cast
    have := Nat.cast_nonneg (α := ℝ) (termCount (cPoly Φ))
    have := Nat.cast_nonneg (α := ℝ) (termCount (Apoly Φ))
    linarith
  have hW0 : (0 : ℝ) ≤ (weight (cPoly Φ) : ℝ) + (weight (Apoly Φ) : ℝ) := by positivity
  have hdA : (Apoly Φ).natDegree ≤ mParam Φ := le_max_right _ _
  have hM : ((Mval Φ + bigN Φ : ℕ) : ℝ) =
      (2 : ℝ) ^ (20 * (wParam Φ + 1)) * ((mParam Φ : ℝ) + 1) ^ 6 + bigN Φ := by
    rw [Mval, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
  have hmP : max (cPoly Φ).natDegree (Apoly Φ).natDegree = mParam Φ := rfl
  rw [hM, max_lt_iff]
  constructor
  · simp only [ffkBound]
    rw [hwz, hmP, natDegree_cPoly]
    have := ffk_part_lt (wParam Φ) (mParam Φ)
    linarith
  · simp only [sssN1]
    rw [hmP, natDegree_cPoly]
    have := sss_part_lt hθ (mParam Φ) (Apoly Φ).natDegree (wParam Φ) hdA hW0 hWw
    linarith

/-- `M > deg A`. -/
theorem natDegree_Apoly_lt_Mval (Φ : CNF) : (Apoly Φ).natDegree < Mval Φ := by
  have h1 : (Apoly Φ).natDegree ≤ mParam Φ := le_max_right _ _
  have h2 : mParam Φ < (mParam Φ + 1) ^ 6 :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_self_pow (by norm_num) _)
  have h3 : (mParam Φ + 1) ^ 6 ≤ Mval Φ := by
    rw [Mval]; exact Nat.le_mul_of_pos_left _ (by positivity)
  omega

/-- `X^L c(X⁻¹) + d = H_M` for `L = M + N`. -/
theorem fL_eq_Hfinal (Φ : CNF) :
    X ^ (Mval Φ + bigN Φ - (cPoly Φ).natDegree) * (cPoly Φ).reverse + Apoly Φ = Hfinal Φ := by
  rw [natDegree_cPoly, reverse_cPoly, Nat.add_sub_cancel, Hfinal, Hpoly, add_comm]

/-- The large-gap theorem applies: the non-cyclotomic part of `H_M` is irreducible over `ℚ`. -/
theorem noncyclotomicPartIrreducible_Hfinal (hSSS : SSSLargeGap) (Φ : CNF) (hΦ : Φ ≠ [])
    (hunsat : ¬Φ.Satisfiable) : NoncyclotomicPartIrreducible (Hfinal Φ) := by
  obtain ⟨θ, hθ1, -, hθ⟩ := exists_lehmerPoly_root
  have h := hSSS (cPoly Φ) (Apoly Φ) (Mval Φ + bigN Φ) θ (by linarith) hθ (cPoly_coeff_zero Φ)
    (Apoly_coeff_zero_ne_zero Φ hΦ) (isRelPrime_reverse_cPoly_Apoly Φ hunsat) (cPoly_ne_Apoly Φ)
    (cPoly_ne_neg_Apoly Φ) (not_capellian Φ hunsat) (bound_lt_Mval_add Φ hθ1)
  rwa [fL_eq_Hfinal] at h

end SparseIrred
