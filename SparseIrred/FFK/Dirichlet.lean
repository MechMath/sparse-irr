import Mathlib

/-!
# FFK Lemma 3: a modulus `κ` putting finitely many integers near multiples of `κ`

Filaseta–Ford–Konyagin (Illinois J. Math. 44 (2000)), Lemma 3: for non-negative integers
`a₁ < ⋯ < a_r` with `a_r` large enough there is an integer `k` such that every `a_j mod k` lies in
`[0, k/4) ∪ (3k/4, k)`.  We prove a version with cruder, but still single-exponential, constants:
the box principle is applied with `8` boxes per coordinate, so the multiplier `d` is at most
`8^{|S|}`, and the size hypothesis on the largest element `a` reads `(10 + κ₀) 64^{|S|} ≤ a`.
This is all that the application in `Ljunggren.lean` needs.

## Main results

* `exists_simultaneous_approx`: Dirichlet's box principle; there is `1 ≤ d ≤ 8^{|S|}` such that
  every `d t` (`t ∈ S`) is within `a/8` of a multiple of `a`.
* `exists_nearMultiple_modulus`: FFK Lemma 3; with `κ = ⌊a / d⌋`, every `t ∈ S` (`t ≤ a`) is
  within `κ/4` of a multiple of `κ`, provided `(10 + κ₀) 64^{|S|} ≤ a`; moreover `κ₀ ≤ κ ≤ a`.
* `two_mul_add_div_four_mod_lt`: if `t` is within `κ/4` of a multiple of `κ`, then the shifted
  residue `(t + ⌊κ/4⌋) mod κ` is `< κ/2`; this is the lifting condition of `Lift.lean`.
* `exists_lift_modulus`: the combination of the two previous results.
-/

namespace SparseIrred.FFK

/-- The pigeonhole step for a pair `i < j` of multipliers falling in the same box. -/
private theorem approx_of_same_box {a i j t : ℕ} (ha : 0 < a)
    (h : 8 * ((i * t) % a) / a = 8 * ((j * t) % a) / a) (hij : i ≤ j) :
    ∃ c : ℤ, 8 * |((j - i : ℕ) : ℤ) * t - c * a| < a := by
  set u := (i * t) % a with hu
  set u' := (j * t) % a with hu'
  set q := 8 * u / a with hq
  have hua : u < a := Nat.mod_lt _ ha
  have hua' : u' < a := Nat.mod_lt _ ha
  -- `q a ≤ 8 u < (q + 1) a`, and the same for `u'`
  have h1 : q * a ≤ 8 * u := Nat.div_mul_le_self _ _
  have h2 : 8 * u < q * a + a := Nat.lt_div_mul_add ha
  have h1' : q * a ≤ 8 * u' := by rw [h]; exact Nat.div_mul_le_self _ _
  have h2' : 8 * u' < q * a + a := by rw [h]; exact Nat.lt_div_mul_add ha
  refine ⟨((j * t / a : ℕ) : ℤ) - ((i * t / a : ℕ) : ℤ), ?_⟩
  have ei : a * (i * t / a) + u = i * t := Nat.div_add_mod _ _
  have ej : a * (j * t / a) + u' = j * t := Nat.div_add_mod _ _
  have key : ((j - i : ℕ) : ℤ) * t - (((j * t / a : ℕ) : ℤ) - ((i * t / a : ℕ) : ℤ)) * a =
      (u' : ℤ) - u := by
    have ei' : (a : ℤ) * ((i * t / a : ℕ) : ℤ) + u = (i : ℤ) * t := by exact_mod_cast ei
    have ej' : (a : ℤ) * ((j * t / a : ℕ) : ℤ) + u' = (j : ℤ) * t := by exact_mod_cast ej
    rw [Nat.cast_sub hij]
    linear_combination ei' - ej'
  rw [key, ← abs_of_nonneg (show (0 : ℤ) ≤ 8 by norm_num), ← abs_mul, abs_lt]
  have h1z : ((q * a : ℕ) : ℤ) ≤ 8 * (u : ℤ) := by exact_mod_cast h1
  have h2z : 8 * (u : ℤ) < ((q * a : ℕ) : ℤ) + a := by exact_mod_cast h2
  have h1z' : ((q * a : ℕ) : ℤ) ≤ 8 * (u' : ℤ) := by exact_mod_cast h1'
  have h2z' : 8 * (u' : ℤ) < ((q * a : ℕ) : ℤ) + a := by exact_mod_cast h2'
  constructor <;> linarith

/-- Dirichlet's box principle: for a finite set `S` of naturals and `a > 0` there is
`1 ≤ d ≤ 8^{|S|}` such that each `d t` (`t ∈ S`) is within `a / 8` of a multiple of `a`. -/
theorem exists_simultaneous_approx (S : Finset ℕ) {a : ℕ} (ha : 0 < a) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ 8 ^ S.card ∧ ∀ t ∈ S, ∃ c : ℤ, 8 * |(d : ℤ) * t - c * a| < a := by
  classical
  let box : Fin (8 ^ S.card + 1) → (S → Fin 8) := fun i t =>
    ⟨8 * ((i.val * t.val) % a) / a, by
      rw [Nat.div_lt_iff_lt_mul ha]
      have := Nat.mod_lt (i.val * t.val) ha
      omega⟩
  have hcard : Fintype.card (S → Fin 8) < Fintype.card (Fin (8 ^ S.card + 1)) := by
    simp
  obtain ⟨i, j, hij, hbox⟩ := Fintype.exists_ne_map_eq_of_card_lt box hcard
  have main : ∀ i j : Fin (8 ^ S.card + 1), i < j → box i = box j →
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ 8 ^ S.card ∧ ∀ t ∈ S, ∃ c : ℤ, 8 * |(d : ℤ) * t - c * a| < a := by
    intro i j hlt hb
    have hlt' : i.val < j.val := Fin.lt_def.mp hlt
    have hj := j.isLt
    refine ⟨j.val - i.val, by omega, by omega, fun t ht => ?_⟩
    have := congrArg (fun f => (f ⟨t, ht⟩ : ℕ)) hb
    simp only [box] at this
    exact approx_of_same_box ha this hlt'.le
  rcases lt_or_gt_of_ne hij with h | h
  · exact main i j h hbox
  · exact main j i h hbox.symm

/-- FFK Lemma 3 (crude constants): if `S ⊆ [0, a]` and `(10 + κ₀) 64^{|S|} ≤ a`, there is a modulus
`κ` with `κ₀ ≤ κ ≤ a` such that every `t ∈ S` is within `κ/4` (strictly) of a multiple of `κ`. -/
theorem exists_nearMultiple_modulus (S : Finset ℕ) (a κ₀ : ℕ) (hS : ∀ t ∈ S, t ≤ a)
    (ha : (10 + κ₀) * 64 ^ S.card ≤ a) :
    ∃ κ : ℕ, 0 < κ ∧ κ₀ ≤ κ ∧ κ ≤ a ∧ ∀ t ∈ S, ∃ c : ℤ, 4 * |(t : ℤ) - c * κ| < κ := by
  set n := S.card
  have h64 : (64 : ℕ) ^ n = 8 ^ n * 8 ^ n := by rw [← mul_pow]; norm_num
  have h8pos : 0 < 8 ^ n := by positivity
  have ha0 : 0 < a := by nlinarith
  obtain ⟨d, hd1, hd8, happrox⟩ := exists_simultaneous_approx S ha0
  have hdd : 8 * (d * d) ≤ a := by nlinarith [Nat.mul_le_mul hd8 hd8]
  have hda : d ≤ a := by nlinarith
  refine ⟨a / d, Nat.div_pos hda (by omega), ?_, Nat.div_le_self _ _, fun t ht => ?_⟩
  · rw [Nat.le_div_iff_mul_le (by omega)]
    nlinarith [Nat.mul_le_mul_left κ₀ hd8]
  obtain ⟨c, hc⟩ := happrox t ht
  -- `a = d κ + ρ`
  set κ := a / d with hκ
  set ρ := a % d with hρ
  have hdiv : d * κ + ρ = a := Nat.div_add_mod a d
  have hρd : ρ < d := Nat.mod_lt a (by omega)
  have hdivZ : (d : ℤ) * κ + ρ = a := by exact_mod_cast hdiv
  have hρdZ : (ρ : ℤ) + 1 ≤ d := by exact_mod_cast hρd
  have hddZ : 8 * ((d : ℤ) * d) ≤ a := by exact_mod_cast hdd
  have htaZ : (t : ℤ) ≤ a := by exact_mod_cast hS t ht
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have hd1Z : (1 : ℤ) ≤ d := by exact_mod_cast hd1
  have ha0Z : (0 : ℤ) < a := by exact_mod_cast ha0
  have hρ0 : (0 : ℤ) ≤ ρ := by positivity
  set δ : ℤ := (d : ℤ) * t - c * a with hδ
  have hδlo : -(a : ℤ) < 8 * δ := by have := neg_abs_le δ; linarith
  have hδhi : 8 * δ < a := by have := le_abs_self δ; linarith
  -- `0 ≤ c ≤ d`
  have hc0 : 0 ≤ c := by
    by_contra hneg
    push Not at hneg
    have h1 : c * (a : ℤ) ≤ -a := by nlinarith
    have h2 : (0 : ℤ) ≤ d * t := by positivity
    linarith
  have hcd : c ≤ d := by
    by_contra hbig
    push Not at hbig
    have h1 : ((d : ℤ) + 1) * a ≤ c * a := by nlinarith
    have h2 : (d : ℤ) * t ≤ d * a := by nlinarith
    linarith
  -- `d (t - c κ) = δ + c ρ`
  have hkey : (d : ℤ) * (4 * ((t : ℤ) - c * κ)) = 4 * (δ + c * ρ) := by
    rw [hδ, ← hdivZ]; ring
  have hcρ : c * (ρ : ℤ) ≤ d * d - d := by nlinarith
  have hcρ0 : 0 ≤ c * (ρ : ℤ) := mul_nonneg hc0 hρ0
  have h2ρ : 2 * (ρ : ℤ) ≤ a := by nlinarith
  have hdpos : (0 : ℤ) < d := by linarith
  refine ⟨c, ?_⟩
  rw [← abs_of_nonneg (show (0 : ℤ) ≤ 4 by norm_num), ← abs_mul, abs_lt]
  constructor
  · have hlo : (d : ℤ) * (-(κ : ℤ)) < d * (4 * ((t : ℤ) - c * κ)) := by
      rw [hkey]; linarith
    exact lt_of_mul_lt_mul_left hlo hdpos.le
  · have hhi : (d : ℤ) * (4 * ((t : ℤ) - c * κ)) < d * κ := by
      rw [hkey]; linarith
    exact lt_of_mul_lt_mul_left hhi hdpos.le

/-- If `t` is within `κ/4` of a multiple of `κ` then `(t + ⌊κ/4⌋) mod κ < κ/2`. -/
theorem two_mul_add_div_four_mod_lt {κ t : ℕ} (hκ : 0 < κ) {c : ℤ}
    (h : 4 * |(t : ℤ) - c * κ| < κ) : 2 * ((t + κ / 4) % κ) < κ := by
  have h' : |4 * ((t : ℤ) - c * κ)| < κ := by
    rwa [abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 4)]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h'
  obtain ⟨q, hq⟩ : ∃ q, q = κ / 4 := ⟨_, rfl⟩
  rw [← hq]
  have hq1 : 4 * q ≤ κ := by omega
  have hq2 : κ < 4 * q + 4 := by omega
  set s : ℤ := (t : ℤ) - c * κ with hs
  have hr0 : 0 ≤ s + q := by omega
  have hrκ : s + q < κ := by omega
  have hmod : (((t + q) % κ : ℕ) : ℤ) = s + q := by
    rw [Int.natCast_mod]
    have e : ((t + q : ℕ) : ℤ) = (s + q) + c * κ := by push_cast; ring
    rw [e, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hr0 hrκ]
  have h2 : 2 * (s + q) < κ := by omega
  omega

/-- The modulus used by the FFK lift: if `S ⊆ [0, a]` and `(10 + κ₀) 64^{|S|} ≤ a`, there is
`κ₀ ≤ κ ≤ a` such that every shifted residue `(t + ⌊κ/4⌋) mod κ` (`t ∈ S`) is `< κ/2`. -/
theorem exists_lift_modulus (S : Finset ℕ) (a κ₀ : ℕ) (hS : ∀ t ∈ S, t ≤ a)
    (ha : (10 + κ₀) * 64 ^ S.card ≤ a) :
    ∃ κ : ℕ, 0 < κ ∧ κ₀ ≤ κ ∧ κ ≤ a ∧ ∀ t ∈ S, 2 * ((t + κ / 4) % κ) < κ := by
  obtain ⟨κ, hκ, h₀, ha', hnear⟩ := exists_nearMultiple_modulus S a κ₀ hS ha
  refine ⟨κ, hκ, h₀, ha', fun t ht => ?_⟩
  obtain ⟨c, hc⟩ := hnear t ht
  exact two_mul_add_div_four_mod_lt hκ hc

end SparseIrred.FFK
