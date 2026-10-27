import Mathlib

/-!
# The FFK `κ`-lift `ℤ[x] → ℤ[x][y]` and the no-carry product identity

This file formalizes the lifting step of Filaseta–Ford–Konyagin (Illinois J. Math. 44 (2000),
proof of Theorem 2).  For a modulus `κ` and a shift `h` (in the application `h = ⌊κ/4⌋`), a
polynomial `f = ∑ f_e x^e` is lifted to

  `kLift κ h f = ∑_e f_e x^{(e + h) mod κ} y^{(e + h) div κ} ∈ ℤ[x][y]`,

so that `(kLift κ h f)(x, x^κ) = x^h f(x)` (`eval_kLift`).  When all shifted residues are `< κ/2`
(`LiftGood`), all `x`-exponents of a product of two lifts are `< κ`, and on such polynomials the
specialization `y ↦ x^κ` is injective (`eq_of_eval_X_pow_eq`: there are no carries).  Hence an
identity `f₁ f₂ = g₁ g₂` in `ℤ[x]` between polynomials satisfying the lifting condition lifts to
the identity `kLift f₁ · kLift f₂ = kLift g₁ · kLift g₂` in `ℤ[x][y]` (`kLift_mul_eq_of_mul_eq`,
FFK (9)).

## Main results

* `eval_kLift`, `kLift_mul_eq_of_mul_eq`: as above.
* `add_div_eq_of_two_mul_mod_lt`: FFK's "same block" argument; two exponents at distance `≤ κ/2`
  get the same `y`-degree when the lower one satisfies the lifting condition.
* `kLift_X_pow_mul`, `kLift_two_block`: the lift of a block `X^s g` whose exponents all have the
  same `y`-degree, and of a polynomial made of two such blocks.
* `dvd_of_kLift_dvd`: specialization of a divisibility in `ℤ[x][y]` back to `ℤ[x]`.

## Implementation notes

The ring `ℤ[x][y]` is `ℤ[X][X]`: the *outer* variable `X` plays the role of `y`, and `C X` is `x`.
-/

open Polynomial

namespace SparseIrred.FFK

/-- The FFK lift `∑_e f_e x^{(e+h) mod κ} y^{(e+h) div κ}` (outer variable `y`). -/
noncomputable def kLift (κ h : ℕ) (f : ℤ[X]) : ℤ[X][X] :=
  f.sum fun e a => monomial ((e + h) / κ) (monomial ((e + h) % κ) a : ℤ[X])

/-- The lifting condition: every shifted residue `(e + h) mod κ` (`e` in the support) is `< κ/2`. -/
def LiftGood (κ h : ℕ) (f : ℤ[X]) : Prop := ∀ e ∈ f.support, 2 * ((e + h) % κ) < κ

/-- All `y`-coefficients of `P ∈ ℤ[x][y]` have `x`-degree `≤ α`. -/
def XDegLE (α : ℕ) (P : ℤ[X][X]) : Prop := ∀ j, (P.coeff j).natDegree ≤ α

/-! ### Additivity and specialization -/

theorem kLift_monomial (κ h e : ℕ) (a : ℤ) :
    kLift κ h (monomial e a) = monomial ((e + h) / κ) (monomial ((e + h) % κ) a : ℤ[X]) := by
  unfold kLift
  rw [sum_monomial_index]
  simp

theorem kLift_zero (κ h : ℕ) : kLift κ h 0 = 0 := by
  simp [kLift]

theorem kLift_add (κ h : ℕ) (f g : ℤ[X]) : kLift κ h (f + g) = kLift κ h f + kLift κ h g := by
  unfold kLift
  rw [sum_add_index]
  · intro i; simp
  · intro i a b; simp [map_add]

/-- `kLift κ h` as an additive homomorphism. -/
noncomputable def kLiftHom (κ h : ℕ) : ℤ[X] →+ ℤ[X][X] where
  toFun := kLift κ h
  map_zero' := kLift_zero κ h
  map_add' := kLift_add κ h

theorem kLiftHom_apply (κ h : ℕ) (f : ℤ[X]) : kLiftHom κ h f = kLift κ h f := rfl

theorem kLift_neg (κ h : ℕ) (f : ℤ[X]) : kLift κ h (-f) = -kLift κ h f :=
  map_neg (kLiftHom κ h) f

theorem kLift_sub (κ h : ℕ) (f g : ℤ[X]) : kLift κ h (f - g) = kLift κ h f - kLift κ h g :=
  map_sub (kLiftHom κ h) f g

theorem kLift_sum {ι : Type*} (κ h : ℕ) (s : Finset ι) (f : ι → ℤ[X]) :
    kLift κ h (∑ i ∈ s, f i) = ∑ i ∈ s, kLift κ h (f i) :=
  map_sum (kLiftHom κ h) f s

/-- Specialization `y ↦ x^κ` of the lift: `(kLift κ h f)(x, x^κ) = x^h f(x)`. -/
theorem eval_kLift (κ h : ℕ) (f : ℤ[X]) : (kLift κ h f).eval (X ^ κ) = X ^ h * f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [kLift_add, eval_add, hp, hq, mul_add]
  | monomial e a =>
    rw [kLift_monomial, eval_monomial, ← pow_mul, ← C_mul_X_pow_eq_monomial,
      ← C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add, Nat.mod_add_div]
    ring

/-! ### No carries -/

theorem XDegLE.mul {α β : ℕ} {P Q : ℤ[X][X]} (hP : XDegLE α P) (hQ : XDegLE β Q) :
    XDegLE (α + β) (P * Q) := by
  intro j
  rw [coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro x _
  exact natDegree_mul_le.trans (add_le_add (hP _) (hQ _))

/-- A lift satisfying the lifting condition has all `x`-exponents `≤ (κ - 1) / 2`. -/
theorem xDegLE_kLift {κ h : ℕ} {f : ℤ[X]} (hf : LiftGood κ h f) :
    XDegLE ((κ - 1) / 2) (kLift κ h f) := by
  intro j
  rw [kLift, Polynomial.sum_def, finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro e he
  rw [coeff_monomial]
  split_ifs
  · exact (natDegree_monomial_le _).trans (by have := hf e he; omega)
  · simp

/-- Coefficient extraction after specialization, when all `x`-exponents are `< κ`. -/
theorem coeff_eval_X_pow {κ α : ℕ} {P : ℤ[X][X]} (hP : XDegLE α P) (hα : α < κ) (j i : ℕ)
    (hi : i < κ) : (P.eval (X ^ κ)).coeff (κ * j + i) = (P.coeff j).coeff i := by
  rw [eval_eq_sum, Polynomial.sum_def, finsetSum_coeff, Finset.sum_eq_single j]
  · rw [← pow_mul, coeff_mul_X_pow']
    simp
  · intro e _ hne
    rw [← pow_mul, coeff_mul_X_pow']
    split_ifs with hle
    · apply coeff_eq_zero_of_natDegree_lt
      rcases lt_or_gt_of_ne hne with hej | hej
      · have := Nat.mul_le_mul_left κ (show e + 1 ≤ j by omega)
        rw [mul_add, mul_one] at this
        exact (hP e).trans_lt (by omega)
      · have := Nat.mul_le_mul_left κ (show j + 1 ≤ e by omega)
        rw [mul_add, mul_one] at this
        omega
    · rfl
  · intro hj
    rw [notMem_support_iff.mp hj, zero_mul, coeff_zero]

/-- Specialization `y ↦ x^κ` is injective on polynomials whose `x`-exponents are `< κ`. -/
theorem eq_of_eval_X_pow_eq {κ α : ℕ} {P Q : ℤ[X][X]} (hP : XDegLE α P) (hQ : XDegLE α Q)
    (hα : α < κ) (h : P.eval (X ^ κ) = Q.eval (X ^ κ)) : P = Q := by
  ext j i
  rcases lt_or_ge i κ with hi | hi
  · rw [← coeff_eval_X_pow hP hα j i hi, ← coeff_eval_X_pow hQ hα j i hi, h]
  · rw [coeff_eq_zero_of_natDegree_lt ((hP j).trans_lt (hα.trans_le hi)),
      coeff_eq_zero_of_natDegree_lt ((hQ j).trans_lt (hα.trans_le hi))]

/-- The no-carry product identity (FFK (9)): an identity `f₁ f₂ = g₁ g₂` in `ℤ[x]` between
polynomials satisfying the lifting condition lifts to `ℤ[x][y]`. -/
theorem kLift_mul_eq_of_mul_eq {κ h : ℕ} (hκ : 0 < κ) {f₁ f₂ g₁ g₂ : ℤ[X]}
    (h₁ : LiftGood κ h f₁) (h₂ : LiftGood κ h f₂) (h₃ : LiftGood κ h g₁) (h₄ : LiftGood κ h g₂)
    (heq : f₁ * f₂ = g₁ * g₂) :
    kLift κ h f₁ * kLift κ h f₂ = kLift κ h g₁ * kLift κ h g₂ := by
  apply eq_of_eval_X_pow_eq (κ := κ) ((xDegLE_kLift h₁).mul (xDegLE_kLift h₂))
    ((xDegLE_kLift h₃).mul (xDegLE_kLift h₄)) (by omega)
  rw [eval_mul, eval_mul, eval_kLift, eval_kLift, eval_kLift, eval_kLift]
  calc X ^ h * f₁ * (X ^ h * f₂) = X ^ h * X ^ h * (f₁ * f₂) := by ring
    _ = X ^ h * g₁ * (X ^ h * g₂) := by rw [heq]; ring

/-! ### Blocks -/

/-- FFK's "same block" argument: two exponents `s ≤ t` at distance `≤ κ/2` get the same `y`-degree
when the lower one satisfies the lifting condition (FFK use it for both endpoints). -/
theorem add_div_eq_of_two_mul_mod_lt {κ h s t : ℕ} (hst : s ≤ t) (h2 : 2 * (t - s) ≤ κ)
    (hs : 2 * ((s + h) % κ) < κ) :
    (t + h) / κ = (s + h) / κ := by
  have e1 := Nat.div_add_mod (s + h) κ
  have e2 := Nat.div_add_mod (t + h) κ
  have hle : (s + h) / κ ≤ (t + h) / κ := Nat.div_le_div_right (by omega)
  by_contra hne
  have hlt : (s + h) / κ + 1 ≤ (t + h) / κ := by omega
  have hm := Nat.mul_le_mul_left κ hlt
  rw [mul_add, mul_one] at hm
  omega

/-- The lift of a block `X^s g` all of whose exponents get the same `y`-degree `ℓ`. -/
theorem kLift_X_pow_mul {κ h s ℓ : ℕ} (g : ℤ[X]) (hg : ∀ e ≤ g.natDegree, (s + e + h) / κ = ℓ) :
    kLift κ h (X ^ s * g) = C (X ^ (s + h - κ * ℓ) * g) * X ^ ℓ := by
  have hℓ : κ * ℓ ≤ s + h := by
    have h0 := hg 0 (Nat.zero_le _)
    rw [add_zero] at h0
    rw [← h0]
    exact Nat.mul_div_le (s + h) κ
  conv_lhs => rw [g.as_sum_range_C_mul_X_pow, Finset.mul_sum]
  conv_rhs => rw [g.as_sum_range_C_mul_X_pow, Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [kLift_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' : e ≤ g.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
  have hq := hg e he'
  have hdm := Nat.div_add_mod (s + e + h) κ
  rw [hq] at hdm
  have hmod : (s + e + h) % κ = s + h - κ * ℓ + e := by omega
  have hmon : (X : ℤ[X]) ^ s * (C (g.coeff e) * X ^ e) = monomial (s + e) (g.coeff e) := by
    rw [← C_mul_X_pow_eq_monomial]; ring
  rw [hmon, kLift_monomial, hq, hmod, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    pow_add]
  congr 2
  ring

/-- The two-block shape: a low block `u` with `y`-degree `0` and a high block `X^s v` with
`y`-degree `ℓ`. -/
theorem kLift_two_block {κ h s ℓ : ℕ} (u v : ℤ[X]) (hu : ∀ e ≤ u.natDegree, (e + h) / κ = 0)
    (hv : ∀ e ≤ v.natDegree, (s + e + h) / κ = ℓ) :
    kLift κ h (X ^ s * v + u) = C (X ^ (s + h - κ * ℓ) * v) * X ^ ℓ + C (X ^ h * u) := by
  rw [kLift_add, kLift_X_pow_mul v hv]
  have hu' : ∀ e ≤ u.natDegree, (0 + e + h) / κ = 0 := fun e he => by rw [zero_add]; exact hu e he
  have := kLift_X_pow_mul (s := 0) (ℓ := 0) (κ := κ) (h := h) u hu'
  rw [pow_zero, one_mul] at this
  rw [this]
  simp

/-- Specializing a divisibility in `ℤ[x][y]` back to `ℤ[x]`: if `kLift f = x^m P` and `P` divides
`kLift g`, then `f ∣ g`, provided `x ∤ f`. -/
theorem dvd_of_kLift_dvd {κ h m : ℕ} {f g : ℤ[X]} {P : ℤ[X][X]} (hf0 : f.coeff 0 ≠ 0)
    (hP : kLift κ h f = C (X ^ m) * P) (hdvd : P ∣ kLift κ h g) : f ∣ g := by
  have h1 : X ^ h * f = X ^ m * P.eval (X ^ κ) := by
    rw [← eval_kLift, hP, eval_mul, eval_C]
  have h2 : P.eval (X ^ κ) ∣ X ^ h * g := by
    rw [← eval_kLift]
    exact (evalRingHom (X ^ κ)).map_dvd hdvd
  have h3 : X ^ h * f ∣ X ^ h * (X ^ m * g) := by
    rw [h1, mul_left_comm]
    exact mul_dvd_mul_left _ h2
  have h4 : f ∣ X ^ m * g := (mul_dvd_mul_iff_left (pow_ne_zero _ X_ne_zero)).mp h3
  have hrel : IsRelPrime f (X ^ m) := by
    apply IsRelPrime.pow_right
    apply IsRelPrime.symm
    rw [Irreducible.isRelPrime_iff_not_dvd irreducible_X, X_dvd_iff]
    exact hf0
  exact hrel.dvd_of_dvd_mul_left h4

end SparseIrred.FFK
