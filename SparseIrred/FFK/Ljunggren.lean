import SparseIrred.LargeGap.Verify
import SparseIrred.FFK.Dirichlet
import SparseIrred.FFK.Lift
import SparseIrred.FFK.Eisenstein

/-!
# Irreducibility of `H_M = A + X^M (X^N - 1)` by Ljunggren's method

Write `F = gapPoly A N M = A + X^M (X^N - 1)` with `A` palindromic (`A.reverse = A`), `A(0) ≠ 0`,
`deg A < M` and `N > 0`, and write `F̃ = mirror F`.  Mathlib's `Polynomial.irreducible_of_mirror`
(Ljunggren's method) reduces `Irreducible F` to two facts.

1. `IsRelPrime F F̃` (`isRelPrime_gapPoly_mirror`).  This follows from the palindromic identity
   `X^{M+N-deg A} F - F̃ = (X^N - 1)(X^{2M+N-deg A} + 1)` (`palindromic_identity`): every common
   root of `F` and `F̃` is a root of unity, and `F` is assumed to have no root-of-unity roots.
2. The Ljunggren condition `F F̃ = k k̃ → k ∈ {±F, ±F̃}` (`ljunggren_gapPoly`).  This is the
   Filaseta–Ford–Konyagin argument (Illinois J. Math. 44 (2000), Lemma 3 and the proofs of
   Theorem 2 and of its Corollary):
   * FFK Lemma 3 (`Dirichlet.lean`) gives a modulus `κ` for which `F`, `F̃`, `k` and `k̃` all
     satisfy the lifting condition, provided `M` is above the explicit threshold `FFKThreshold`
     (`exists_modulus_gapPoly`);
   * the identity `F F̃ = k k̃` lifts to `ℤ[x][y]` without carries (`Lift.lean`);
   * the lift of `F̃` is `x^β A(x) y^ℓ - x^h (x^N - 1)` (`kLift_mirror_gapPoly`); after removing
     a power of `x` it is irreducible by Eisenstein's criterion at `(x - 1)` (`Eisenstein.lean`),
     hence prime in the UFD `ℤ[x][y]`, so it divides the lift of `k` or the lift of `k̃`;
   * specializing back to `ℤ[x]` gives `F̃ ∣ k` or `F̃ ∣ k̃`; since `k` has the same degree and
     the same weight `∑ coeff²` as `F`, this forces `k = ±F̃` or `k̃ = ±F̃`
     (`eq_or_eq_neg_of_dvd`, `ljunggren_of_modulus`).

Compared with FFK, Lemma 3 is used with cruder constants (see `Dirichlet.lean`), and Eisenstein's
criterion at `(x - 1)` replaces Capelli's theorem.

The last section instantiates `A = Apoly Φ`, `N = bigN Φ`, `M = Mval Φ` and proves
`irreducible_Hfinal : Irreducible (Hfinal Φ)` for an unsatisfiable CNF `Φ ≠ []`.  The inputs from
the construction are: `A` is palindromic with `A(0) ≠ 0` and `N > 0` (`reverse_Apoly`,
`Apoly_coeff_zero_ne_zero`, `bigN_pos`); `A` is prime to `X^N - 1`
(`isRelPrime_reverse_cPoly_Apoly`); `H_M` has no root-of-unity roots
(`satisfiable_of_rootOfUnity_root`); and `Mval Φ` is above the FFK threshold (`FFKThreshold_Mval`).
-/

open Polynomial

namespace SparseIrred.FFK

open Complexity.SAT

/-- The polynomial `F = A + X^M (X^N - 1)`. -/
noncomputable def gapPoly (A : ℤ[X]) (N M : ℕ) : ℤ[X] := A + X ^ M * (X ^ N - 1)

/-! ### Weights (`weight p = ‖p‖² = ∑ coeff²`) -/

theorem weight_eq_sum_sq (p : ℤ[X]) : (weight p : ℤ) = p.sum fun _ a => a ^ 2 := by
  rw [weight, Polynomial.sum_def]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sq_abs]

/-- `weight` may be computed over any superset of the support. -/
theorem weight_eq_sum_of_support_subset {p : ℤ[X]} {s : Finset ℕ} (h : p.support ⊆ s) :
    weight p = ∑ e ∈ s, (p.coeff e).natAbs ^ 2 := by
  rw [weight]
  refine Finset.sum_subset h fun e _ he => ?_
  rw [notMem_support_iff.mp he]
  simp

theorem termCount_le_weight (p : ℤ[X]) : termCount p ≤ weight p := by
  rw [termCount, weight, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro e he
  have h1 : (p.coeff e).natAbs ≠ 0 := by
    rw [Ne, Int.natAbs_eq_zero]; exact mem_support_iff.mp he
  have h2 : 1 ≤ (p.coeff e).natAbs := Nat.one_le_iff_ne_zero.mpr h1
  nlinarith

theorem weight_pos {p : ℤ[X]} (hp : p ≠ 0) : 0 < weight p :=
  (Finset.card_pos.mpr (support_nonempty.mpr hp)).trans_le (termCount_le_weight p)

theorem weight_C_mul (c : ℤ) (p : ℤ[X]) : weight (C c * p) = c.natAbs ^ 2 * weight p := by
  have hsub : (C c * p).support ⊆ p.support := by
    intro e he
    rw [mem_support_iff, coeff_C_mul] at he
    exact mem_support_iff.mpr (right_ne_zero_of_mul he)
  rw [weight_eq_sum_of_support_subset hsub, weight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [coeff_C_mul, Int.natAbs_mul, mul_pow]

theorem weight_neg (p : ℤ[X]) : weight (-p) = weight p := by
  simp [weight]

theorem weight_mirror (p : ℤ[X]) : weight p.mirror = weight p := by
  have h1 := coeff_mul_mirror p.mirror
  rw [mirror_mirror, mirror_natDegree, mirror_natTrailingDegree, mul_comm p.mirror p,
    coeff_mul_mirror] at h1
  have : (weight p.mirror : ℤ) = weight p := by rw [weight_eq_sum_sq, weight_eq_sum_sq, h1]
  exact_mod_cast this

theorem termCount_mirror (p : ℤ[X]) : termCount p.mirror = termCount p := by
  rw [termCount, termCount]
  have : p.mirror.support = p.support.image (revAt (p.natDegree + p.natTrailingDegree)) := by
    ext n
    simp only [mem_support_iff, coeff_mirror, Finset.mem_image]
    constructor
    · intro h; exact ⟨_, h, revAt_invol⟩
    · rintro ⟨m, hm, rfl⟩; rwa [revAt_invol]
  rw [this, Finset.card_image_of_injective _ (revAt _).injective]

/-! ### Consequences of `f f̃ = k k̃` -/

theorem natDegree_eq_of_mul_mirror_eq {f k : ℤ[X]} (h : f * f.mirror = k * k.mirror) :
    k.natDegree = f.natDegree := by
  have h1 := natDegree_mul_mirror f
  have h2 := natDegree_mul_mirror k
  rw [h] at h1
  omega

theorem natTrailingDegree_eq_of_mul_mirror_eq {f k : ℤ[X]} (h : f * f.mirror = k * k.mirror) :
    k.natTrailingDegree = f.natTrailingDegree := by
  have h1 := natTrailingDegree_mul_mirror f
  have h2 := natTrailingDegree_mul_mirror k
  rw [h] at h1
  omega

theorem weight_eq_of_mul_mirror_eq {f k : ℤ[X]} (h : f * f.mirror = k * k.mirror) :
    weight k = weight f := by
  have h1 := coeff_mul_mirror f
  have h2 := coeff_mul_mirror k
  rw [natDegree_eq_of_mul_mirror_eq h, natTrailingDegree_eq_of_mul_mirror_eq h, ← h, h1] at h2
  have : (weight k : ℤ) = weight f := by rw [weight_eq_sum_sq, weight_eq_sum_sq, h2]
  exact_mod_cast this

/-- A divisor of the same degree and the same weight is `±` the polynomial. -/
theorem eq_or_eq_neg_of_dvd {f g : ℤ[X]} (hfg : f ∣ g) (hg : g ≠ 0)
    (hdeg : g.natDegree ≤ f.natDegree) (hw : weight g = weight f) : g = f ∨ g = -f := by
  obtain ⟨q, rfl⟩ := hfg
  have hf : f ≠ 0 := left_ne_zero_of_mul hg
  have hq : q ≠ 0 := right_ne_zero_of_mul hg
  rw [natDegree_mul hf hq] at hdeg
  have hq0 : q.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hq0] at hw ⊢
  rw [mul_comm, weight_C_mul] at hw
  have hc : (q.coeff 0).natAbs ^ 2 = 1 :=
    Nat.eq_of_mul_eq_mul_right (weight_pos hf) (by rw [hw, one_mul])
  have hc1 : (q.coeff 0).natAbs = 1 := by
    rw [pow_eq_one_iff] at hc
    omega
  rcases Int.natAbs_eq_iff.mp hc1 with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

/-! ### The gap polynomial `F = A + X^M (X^N - 1)` -/

section gapPoly

variable {A : ℤ[X]} {N M : ℕ}

theorem monic_X_pow_sub_one (hN : 0 < N) : (X ^ N - 1 : ℤ[X]).Monic := by
  have h := monic_X_pow_sub_C (1 : ℤ) hN.ne'
  rwa [map_one] at h

theorem natDegree_X_pow_sub_one (N : ℕ) : (X ^ N - 1 : ℤ[X]).natDegree = N := by
  have h := natDegree_X_pow_sub_C (n := N) (r := (1 : ℤ))
  rwa [map_one] at h

theorem natDegree_X_pow_mul_X_pow_sub_one (hN : 0 < N) :
    (X ^ M * (X ^ N - 1) : ℤ[X]).natDegree = M + N := by
  rw [(monic_X_pow M).natDegree_mul (monic_X_pow_sub_one hN), natDegree_X_pow,
    natDegree_X_pow_sub_one]

theorem natDegree_gapPoly (hM : A.natDegree < M) (hN : 0 < N) :
    (gapPoly A N M).natDegree = M + N := by
  rw [gapPoly, natDegree_add_eq_right_of_natDegree_lt
    (by rw [natDegree_X_pow_mul_X_pow_sub_one hN]; omega), natDegree_X_pow_mul_X_pow_sub_one hN]

theorem monic_gapPoly (hM : A.natDegree < M) (hN : 0 < N) : (gapPoly A N M).Monic := by
  have hmon : (X ^ M * (X ^ N - 1) : ℤ[X]).Monic := (monic_X_pow M).mul (monic_X_pow_sub_one hN)
  apply hmon.add_of_right
  rw [degree_eq_natDegree hmon.ne_zero, natDegree_X_pow_mul_X_pow_sub_one hN]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast (by omega : A.natDegree < M + N))

theorem coeff_zero_gapPoly (hM : 0 < M) : (gapPoly A N M).coeff 0 = A.coeff 0 := by
  rw [gapPoly, coeff_add, coeff_X_pow_mul']
  simp [Nat.not_le.mpr hM]

theorem natTrailingDegree_gapPoly (hA0 : A.coeff 0 ≠ 0) (hM : 0 < M) :
    (gapPoly A N M).natTrailingDegree = 0 :=
  natTrailingDegree_eq_zero.mpr (Or.inr (by rw [coeff_zero_gapPoly hM]; exact hA0))

/-- `mirror F = X^{M+N-deg A} A - (X^N - 1)` for palindromic `A` with `A(0) ≠ 0`. -/
theorem mirror_gapPoly (hA : A.reverse = A) (hA0 : A.coeff 0 ≠ 0) (hM : A.natDegree < M)
    (hN : 0 < N) : (gapPoly A N M).mirror = X ^ (M + N - A.natDegree) * A - (X ^ N - 1) := by
  rw [mirror, natTrailingDegree_gapPoly hA0 (by omega), pow_zero, mul_one, reverse,
    natDegree_gapPoly hM hN, gapPoly, reflect_add]
  have h1 : reflect (M + N) A = X ^ (M + N - A.natDegree) * A := by
    have := reflect_mul (1 : ℤ[X]) A (F := M + N - A.natDegree) (G := A.natDegree) (by simp)
      le_rfl
    rw [one_mul, Nat.sub_add_cancel (by omega), reflect_one] at this
    rw [this, show reflect A.natDegree A = A.reverse from rfl, hA]
  have h2 : reflect (M + N) (X ^ M * (X ^ N - 1) : ℤ[X]) = -(X ^ N - 1) := by
    rw [reflect_mul (X ^ M) (X ^ N - 1) (F := M) (G := N) (by simp)
      (by rw [natDegree_X_pow_sub_one]), reflect_monomial, revAt_le le_rfl, Nat.sub_self,
      pow_zero, one_mul, reflect_sub, reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero,
      reflect_one]
    ring
  rw [h1, h2]
  ring

theorem coeff_zero_mirror_gapPoly (hA0 : A.coeff 0 ≠ 0) (hM : A.natDegree < M) (hN : 0 < N) :
    (gapPoly A N M).mirror.coeff 0 = 1 := by
  rw [mirror, natTrailingDegree_gapPoly hA0 (by omega), pow_zero, mul_one, coeff_zero_reverse]
  exact (monic_gapPoly hM hN).leadingCoeff

/-- The palindromic identity `X^{M+N-deg A} F - mirror F = (X^N - 1)(X^{2M+N-deg A} + 1)`. -/
theorem palindromic_identity (hA : A.reverse = A) (hA0 : A.coeff 0 ≠ 0) (hM : A.natDegree < M)
    (hN : 0 < N) :
    X ^ (M + N - A.natDegree) * gapPoly A N M - (gapPoly A N M).mirror =
      (X ^ N - 1) * (X ^ (2 * M + N - A.natDegree) + 1) := by
  rw [mirror_gapPoly hA hA0 hM hN, gapPoly,
    show 2 * M + N - A.natDegree = (M + N - A.natDegree) + M by omega, pow_add]
  ring

theorem weight_add_of_disjoint {p q : ℤ[X]} (h : Disjoint p.support q.support) :
    weight (p + q) = weight p + weight q := by
  rw [weight_eq_sum_of_support_subset support_add, Finset.sum_union h, weight, weight]
  congr 1
  · refine Finset.sum_congr rfl fun e he => ?_
    rw [coeff_add, notMem_support_iff.mp (Finset.disjoint_left.mp h he), add_zero]
  · refine Finset.sum_congr rfl fun e he => ?_
    rw [coeff_add, notMem_support_iff.mp (Finset.disjoint_right.mp h he), zero_add]

theorem weight_X_pow (k : ℕ) : weight (X ^ k : ℤ[X]) = 1 := by
  simp [weight, support_X_pow]

theorem weight_X_pow_mul_X_pow_sub_one (hN : 0 < N) :
    weight (X ^ M * (X ^ N - 1) : ℤ[X]) = 2 := by
  rw [show (X ^ M * (X ^ N - 1) : ℤ[X]) = X ^ (M + N) + -X ^ M by ring,
    weight_add_of_disjoint, weight_neg, weight_X_pow, weight_X_pow]
  rw [support_neg, support_X_pow, support_X_pow]
  simp
  omega

theorem weight_gapPoly (hM : A.natDegree < M) (hN : 0 < N) :
    weight (gapPoly A N M) = weight A + 2 := by
  rw [gapPoly, weight_add_of_disjoint, weight_X_pow_mul_X_pow_sub_one hN]
  rw [Finset.disjoint_left]
  intro e heA heB
  have h1 := le_natDegree_of_mem_supp e heA
  rw [mem_support_iff, coeff_X_pow_mul'] at heB
  split_ifs at heB with h
  · omega
  · exact heB rfl

theorem termCount_gapPoly_le : termCount (gapPoly A N M) ≤ termCount A + 2 := by
  rw [termCount, termCount, gapPoly]
  have h1 : (X ^ M * (X ^ N - 1) : ℤ[X]).support ⊆ {M + N, M} := by
    rw [show (X ^ M * (X ^ N - 1) : ℤ[X]) = X ^ (M + N) + -X ^ M by ring]
    refine support_add.trans (Finset.union_subset ?_ ?_)
    · rw [← monomial_one_right_eq_X_pow]
      exact support_monomial_subset _ _ |>.trans (by simp)
    · rw [support_neg, ← monomial_one_right_eq_X_pow]
      exact support_monomial_subset _ _ |>.trans (by simp)
  calc (A + X ^ M * (X ^ N - 1)).support.card
      ≤ (A.support ∪ (X ^ M * (X ^ N - 1) : ℤ[X]).support).card := Finset.card_le_card support_add
    _ ≤ A.support.card + (X ^ M * (X ^ N - 1) : ℤ[X]).support.card := Finset.card_union_le _ _
    _ ≤ A.support.card + ({M + N, M} : Finset ℕ).card := by
        gcongr
    _ ≤ A.support.card + 2 := by
        gcongr
        exact Finset.card_le_two

/-! ### `IsRelPrime F F̃` -/

/-- If `F` has no root-of-unity roots, `F` and its mirror are relatively prime. -/
theorem isRelPrime_gapPoly_mirror (hA : A.reverse = A) (hA0 : A.coeff 0 ≠ 0)
    (hM : A.natDegree < M) (hN : 0 < N)
    (hroot : ∀ z : ℂ, (∃ n, 0 < n ∧ z ^ n = 1) → aeval z (gapPoly A N M) ≠ 0) :
    IsRelPrime (gapPoly A N M) (gapPoly A N M).mirror := by
  have hmon := monic_gapPoly hM hN
  intro g hgF hgF'
  by_contra hunit
  rcases Nat.eq_zero_or_pos g.natDegree with hdeg | hdeg
  · -- a constant common divisor divides the monic `F`
    apply hunit
    rw [eq_C_of_natDegree_eq_zero hdeg] at hgF ⊢
    apply isUnit_C.mpr
    rw [C_dvd_iff_dvd_coeff] at hgF
    have h1 := hgF (gapPoly A N M).natDegree
    rw [coeff_natDegree, hmon.leadingCoeff] at h1
    exact isUnit_of_dvd_one h1
  · -- a non-constant common divisor has a complex root, which is a root of unity
    have hdegC : 0 < (g.map (Int.castRingHom ℂ)).degree := by
      rw [degree_map_eq_of_injective (RingHom.injective_int _)]
      exact natDegree_pos_iff_degree_pos.mp hdeg
    obtain ⟨z, hz⟩ := Complex.exists_root hdegC
    have hgz : aeval z g = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
    have hFz : aeval z (gapPoly A N M) = 0 := by
      obtain ⟨q, hq⟩ := hgF; rw [hq, map_mul, hgz, zero_mul]
    have hF'z : aeval z (gapPoly A N M).mirror = 0 := by
      obtain ⟨q, hq⟩ := hgF'; rw [hq, map_mul, hgz, zero_mul]
    have hid := congrArg (aeval z) (palindromic_identity hA hA0 hM hN)
    rw [map_sub, map_mul, hFz, hF'z, mul_zero, sub_zero, map_mul] at hid
    simp only [map_sub, map_add, map_pow, aeval_X, map_one] at hid
    rcases mul_eq_zero.mp hid.symm with h1 | h1
    · exact hroot z ⟨N, hN, sub_eq_zero.mp h1⟩ hFz
    · have h2 : z ^ ((2 * M + N - A.natDegree) * 2) = 1 := by
        rw [pow_mul, eq_neg_of_add_eq_zero_left h1]
        norm_num
      exact hroot z ⟨_, by omega, h2⟩ hFz

/-! ### The Ljunggren condition (Filaseta–Ford–Konyagin) -/

/-- The threshold on `M` above which the FFK argument applies:
`(10 + 2 max(N, deg A)) 64^{2 (‖A‖² + #A) + 8} ≤ M`, where `‖A‖² = weight A` and
`#A = termCount A` (the constants come from `Dirichlet.lean`). -/
def FFKThreshold (A : ℤ[X]) (N M : ℕ) : Prop :=
  (10 + 2 * max N A.natDegree) * 64 ^ (2 * (weight A + termCount A) + 8) ≤ M

theorem natDegree_lt_of_FFKThreshold (hM : FFKThreshold A N M) : A.natDegree < M := by
  have h1 : 1 ≤ 64 ^ (2 * (weight A + termCount A) + 8) := Nat.one_le_pow _ _ (by norm_num)
  have h2 : A.natDegree ≤ max N A.natDegree := le_max_right _ _
  unfold FFKThreshold at hM
  nlinarith

/-- The modulus: FFK Lemma 3 applied to all exponents of `F`, `F̃`, `k`, `k̃`. -/
theorem exists_modulus_gapPoly (hN : 0 < N) (hM : FFKThreshold A N M) {k : ℤ[X]}
    (hk : gapPoly A N M * (gapPoly A N M).mirror = k * k.mirror) :
    ∃ κ : ℕ, 0 < κ ∧ 2 * max N A.natDegree ≤ κ ∧ κ ≤ M + N ∧
      LiftGood κ (κ / 4) (gapPoly A N M) ∧ LiftGood κ (κ / 4) (gapPoly A N M).mirror ∧
      LiftGood κ (κ / 4) k ∧ LiftGood κ (κ / 4) k.mirror := by
  classical
  have hM' := natDegree_lt_of_FFKThreshold hM
  have hFdeg : (gapPoly A N M).natDegree = M + N := natDegree_gapPoly hM' hN
  have hF'deg : (gapPoly A N M).mirror.natDegree = M + N := by rw [mirror_natDegree, hFdeg]
  have hkdeg : k.natDegree = M + N := (natDegree_eq_of_mul_mirror_eq hk).trans hFdeg
  have hk'deg : k.mirror.natDegree = M + N := by rw [mirror_natDegree, hkdeg]
  set S := (gapPoly A N M).support ∪ (gapPoly A N M).mirror.support ∪ k.support ∪
    k.mirror.support with hS
  have hSle : ∀ t ∈ S, t ≤ M + N := by
    intro t ht
    simp only [hS, Finset.mem_union] at ht
    rcases ht with ((h | h) | h) | h
    · exact hFdeg ▸ le_natDegree_of_mem_supp t h
    · exact hF'deg ▸ le_natDegree_of_mem_supp t h
    · exact hkdeg ▸ le_natDegree_of_mem_supp t h
    · exact hk'deg ▸ le_natDegree_of_mem_supp t h
  have hkw : termCount k ≤ weight A + 2 := by
    rw [← weight_gapPoly hM' hN, ← weight_eq_of_mul_mirror_eq hk]
    exact termCount_le_weight k
  have hFw := termCount_gapPoly_le (A := A) (N := N) (M := M)
  have hcard : S.card ≤ 2 * (weight A + termCount A) + 8 := by
    have h1 : S.card ≤ termCount (gapPoly A N M) + termCount (gapPoly A N M).mirror +
        termCount k + termCount k.mirror := by
      simp only [hS, termCount]
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
      exact Finset.card_union_le _ _
    rw [termCount_mirror, termCount_mirror] at h1
    omega
  have ha : (10 + 2 * max N A.natDegree) * 64 ^ S.card ≤ M + N :=
    calc (10 + 2 * max N A.natDegree) * 64 ^ S.card
        ≤ (10 + 2 * max N A.natDegree) * 64 ^ (2 * (weight A + termCount A) + 8) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hcard)
      _ ≤ M := hM
      _ ≤ M + N := Nat.le_add_right _ _
  obtain ⟨κ, hκ, h₀, hκa, hgood⟩ := exists_lift_modulus S (M + N) _ hSle ha
  refine ⟨κ, hκ, h₀, hκa, fun e he => hgood e ?_, fun e he => hgood e ?_,
    fun e he => hgood e ?_, fun e he => hgood e ?_⟩ <;> simp [hS, he]

/-- The shape of the lift of `F̃`: `x^β A(x) y^ℓ - x^h (x^N - 1)` with `ℓ > 0`, `h = ⌊κ/4⌋`. -/
theorem kLift_mirror_gapPoly (hA : A.reverse = A) (hA0 : A.coeff 0 ≠ 0) (hM : A.natDegree < M)
    (hN : 0 < N) {κ : ℕ} (hκ : 0 < κ) (hκ₀ : 2 * max N A.natDegree ≤ κ) (hκL : κ ≤ M + N)
    (hgood : LiftGood κ (κ / 4) (gapPoly A N M).mirror) :
    ∃ ℓ β : ℕ, 0 < ℓ ∧ kLift κ (κ / 4) (gapPoly A N M).mirror =
      C (X ^ β * A) * X ^ ℓ + C (X ^ (κ / 4) * -(X ^ N - 1)) := by
  set h := κ / 4 with hh
  set s := M + N - A.natDegree with hs
  have hmir : (gapPoly A N M).mirror = X ^ s * A - (X ^ N - 1) := mirror_gapPoly hA hA0 hM hN
  -- the two ends `s` and `M + N` of the high block lie in the support of `F̃`
  have hs_supp : s ∈ (gapPoly A N M).mirror.support := by
    rw [mem_support_iff, hmir, coeff_sub, coeff_X_pow_mul', coeff_sub, coeff_X_pow, coeff_one]
    have h1 : s ≠ N := by omega
    have h2 : s ≠ 0 := by omega
    simp [h1, h2, hA0]
  have hblock : (M + N + h) / κ = (s + h) / κ :=
    add_div_eq_of_two_mul_mod_lt (by omega) (by omega) (hgood s hs_supp)
  have hv : ∀ e ≤ A.natDegree, (s + e + h) / κ = (M + N + h) / κ := by
    intro e he
    apply le_antisymm
    · exact Nat.div_le_div_right (by omega)
    · rw [hblock]; exact Nat.div_le_div_right (by omega)
  have hu : ∀ e ≤ (-(X ^ N - 1) : ℤ[X]).natDegree, (e + h) / κ = 0 := by
    intro e he
    rw [natDegree_neg, natDegree_X_pow_sub_one] at he
    exact Nat.div_eq_of_lt (by omega)
  refine ⟨(M + N + h) / κ, s + h - κ * ((M + N + h) / κ), Nat.div_pos (by omega) hκ, ?_⟩
  rw [hmir, sub_eq_add_neg, kLift_two_block _ _ hu hv]

/-- The FFK core: given a good modulus, `F F̃ = k k̃` forces `k ∈ {±F, ±F̃}`. -/
theorem ljunggren_of_modulus (hA : A.reverse = A) (hA0 : A.coeff 0 ≠ 0) (hM : A.natDegree < M)
    (hN : 0 < N) (hAB : IsRelPrime A (X ^ N - 1)) {k : ℤ[X]}
    (hk : gapPoly A N M * (gapPoly A N M).mirror = k * k.mirror) {κ : ℕ} (hκ : 0 < κ)
    (hκ₀ : 2 * max N A.natDegree ≤ κ) (hκL : κ ≤ M + N)
    (hF : LiftGood κ (κ / 4) (gapPoly A N M)) (hF' : LiftGood κ (κ / 4) (gapPoly A N M).mirror)
    (hK : LiftGood κ (κ / 4) k) (hK' : LiftGood κ (κ / 4) k.mirror) :
    k = gapPoly A N M ∨ k = -gapPoly A N M ∨ k = (gapPoly A N M).mirror ∨
      k = -(gapPoly A N M).mirror := by
  set F := gapPoly A N M with hFdef
  set h := κ / 4 with hh
  -- the no-carry product identity in `ℤ[x][y]`
  have hprod : kLift κ h F * kLift κ h F.mirror = kLift κ h k * kLift κ h k.mirror :=
    kLift_mul_eq_of_mul_eq hκ hF hF' hK hK' hk
  -- the shape of the lift of `F̃`, and its part without `x`-powers
  obtain ⟨ℓ, β, hℓ, hG₂⟩ := kLift_mirror_gapPoly hA hA0 hM hN hκ hκ₀ hκL hF'
  set m := min β h with hm
  set G : ℤ[X][X] := C (X ^ (β - m) * A) * X ^ ℓ + C (X ^ (h - m) * -(X ^ N - 1)) with hG
  have hsplit : kLift κ h F.mirror = C (X ^ m) * G := by
    have e1 : (X : ℤ[X]) ^ β = X ^ m * X ^ (β - m) := by
      rw [← pow_add, Nat.add_sub_cancel' (min_le_left _ _)]
    have e2 : (X : ℤ[X]) ^ h = X ^ m * X ^ (h - m) := by
      rw [← pow_add, Nat.add_sub_cancel' (min_le_right _ _)]
    rw [hG₂, hG, e1, e2]
    simp only [map_mul]
    ring
  have hprime : Prime G :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (irreducible_gapLift hN hℓ hA0 hAB (by omega))
  have hdvd : G ∣ kLift κ h k * kLift κ h k.mirror := by
    rw [← hprod, hsplit]
    exact Dvd.intro_left (kLift κ h F * C (X ^ m)) (by ring)
  -- specialization back to `ℤ[x]`
  have hF0 : F.mirror.coeff 0 ≠ 0 := by
    rw [coeff_zero_mirror_gapPoly hA0 hM hN]; exact one_ne_zero
  have hFne : F ≠ 0 := (monic_gapPoly hM hN).ne_zero
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_mul, mul_eq_zero, mirror_eq_zero, or_self] at hk
    exact hFne hk
  have hkdeg : k.natDegree = F.natDegree := natDegree_eq_of_mul_mirror_eq hk
  have hkw : weight k = weight F := weight_eq_of_mul_mirror_eq hk
  rcases hprime.dvd_or_dvd hdvd with h1 | h2
  · have hd := dvd_of_kLift_dvd hF0 hsplit h1
    rcases eq_or_eq_neg_of_dvd hd hk0 (by rw [mirror_natDegree, hkdeg])
      (by rw [weight_mirror, hkw]) with e | e
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr e))
  · have hd := dvd_of_kLift_dvd hF0 hsplit h2
    rcases eq_or_eq_neg_of_dvd hd (mirror_eq_zero.not.mpr hk0)
      (by rw [mirror_natDegree, mirror_natDegree, hkdeg])
      (by rw [weight_mirror, weight_mirror, hkw]) with e | e
    · left
      rw [← mirror_mirror k, e, mirror_mirror]
    · right; left
      rw [← mirror_mirror k, e, mirror_neg, mirror_mirror]

/-- The Ljunggren condition for `F = A + X^M (X^N - 1)` above the FFK threshold. -/
theorem ljunggren_gapPoly (hA : A.reverse = A) (hA0 : A.coeff 0 ≠ 0) (hN : 0 < N)
    (hAB : IsRelPrime A (X ^ N - 1)) (hM : FFKThreshold A N M) (k : ℤ[X])
    (hk : gapPoly A N M * (gapPoly A N M).mirror = k * k.mirror) :
    k = gapPoly A N M ∨ k = -gapPoly A N M ∨ k = (gapPoly A N M).mirror ∨
      k = -(gapPoly A N M).mirror := by
  obtain ⟨κ, hκ, hκ₀, hκL, hF, hF', hK, hK'⟩ := exists_modulus_gapPoly hN hM hk
  exact ljunggren_of_modulus hA hA0 (natDegree_lt_of_FFKThreshold hM) hN hAB hk hκ hκ₀ hκL
    hF hF' hK hK'

/-- Irreducibility of `F = A + X^M (X^N - 1)`: Ljunggren's method (`irreducible_of_mirror`). -/
theorem irreducible_gapPoly (hA : A.reverse = A) (hA0 : A.coeff 0 ≠ 0) (hN : 0 < N)
    (hAB : IsRelPrime A (X ^ N - 1)) (hM : FFKThreshold A N M)
    (hroot : ∀ z : ℂ, (∃ n, 0 < n ∧ z ^ n = 1) → aeval z (gapPoly A N M) ≠ 0) :
    Irreducible (gapPoly A N M) := by
  have hM' := natDegree_lt_of_FFKThreshold hM
  refine irreducible_of_mirror ?_ (ljunggren_gapPoly hA hA0 hN hAB hM)
    (isRelPrime_gapPoly_mirror hA hA0 hM' hN hroot)
  apply not_isUnit_of_natDegree_pos
  rw [natDegree_gapPoly hM' hN]
  omega

end gapPoly

/-! ### The polynomials of Theorem 8 -/

theorem Hfinal_eq_gapPoly (Φ : CNF) : Hfinal Φ = gapPoly (Apoly Φ) (bigN Φ) (Mval Φ) := by
  rw [Hfinal, Hpoly, Bpoly, gapPoly]

private theorem cPoly_eq_binomial (Φ : CNF) :
    cPoly Φ = C (1 : ℤ) * X ^ 0 + C (-1 : ℤ) * X ^ bigN Φ := by
  rw [cPoly]; simp; ring

theorem weight_cPoly (Φ : CNF) : weight (cPoly Φ) = 2 := by
  have hN := bigN_pos Φ
  rw [cPoly_eq_binomial, weight, support_binomial hN.ne (by norm_num) (by norm_num),
    Finset.sum_pair hN.ne]
  simp [coeff_X_pow, coeff_one, hN.ne, hN.ne']

theorem termCount_cPoly (Φ : CNF) : termCount (cPoly Φ) = 2 := by
  rw [termCount, cPoly_eq_binomial]
  exact card_support_binomial (bigN_pos Φ).ne (by norm_num) (by norm_num)

theorem wParam_eq (Φ : CNF) : wParam Φ = weight (Apoly Φ) + termCount (Apoly Φ) + 4 := by
  rw [wParam, weight_cPoly, termCount_cPoly]
  ring

theorem mParam_eq (Φ : CNF) : mParam Φ = max (bigN Φ) (Apoly Φ).natDegree := by
  rw [mParam, natDegree_cPoly]

/-- `(10 + 2m) 64^{2w} ≤ 2^{20(w+1)} (m+1)^6`. -/
theorem threshold_arith (w m : ℕ) :
    (10 + 2 * m) * 64 ^ (2 * w) ≤ 2 ^ (20 * (w + 1)) * (m + 1) ^ 6 := by
  have h64 : (64 : ℕ) ^ (2 * w) = 2 ^ (12 * w) := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]; ring_nf
  have h2 : (2 : ℕ) ^ (20 * (w + 1)) = 2 ^ (12 * w) * (2 ^ (8 * w) * 2 ^ 20) := by
    rw [← pow_add, ← pow_add]; ring_nf
  rw [h64, h2]
  have hm : 10 + 2 * m ≤ 2 ^ 20 * (m + 1) := by norm_num; omega
  have h1 : 1 ≤ 2 ^ (8 * w) := Nat.one_le_two_pow
  have h3 : m + 1 ≤ (m + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have h4 : 10 + 2 * m ≤ 2 ^ (8 * w) * 2 ^ 20 * (m + 1) ^ 6 :=
    calc 10 + 2 * m ≤ 2 ^ 20 * (m + 1) := hm
      _ ≤ 2 ^ 20 * (m + 1) ^ 6 := Nat.mul_le_mul_left _ h3
      _ = 1 * 2 ^ 20 * (m + 1) ^ 6 := by ring
      _ ≤ 2 ^ (8 * w) * 2 ^ 20 * (m + 1) ^ 6 := by gcongr
  calc (10 + 2 * m) * 2 ^ (12 * w) ≤ (2 ^ (8 * w) * 2 ^ 20 * (m + 1) ^ 6) * 2 ^ (12 * w) :=
        Nat.mul_le_mul_right _ h4
    _ = 2 ^ (12 * w) * (2 ^ (8 * w) * 2 ^ 20) * (m + 1) ^ 6 := by ring

/-- `M = Mval Φ` is above the FFK threshold. -/
theorem FFKThreshold_Mval (Φ : CNF) : FFKThreshold (Apoly Φ) (bigN Φ) (Mval Φ) := by
  unfold FFKThreshold
  rw [Mval, ← mParam_eq,
    show 2 * (weight (Apoly Φ) + termCount (Apoly Φ)) + 8 = 2 * wParam Φ by rw [wParam_eq]; ring]
  exact threshold_arith _ _

/-- In the unsatisfiable case `A` and `B = X^N - 1` are relatively prime in `ℤ[X]`. -/
theorem isRelPrime_Apoly_Bpoly (Φ : CNF) (hunsat : ¬Φ.Satisfiable) :
    IsRelPrime (Apoly Φ) (X ^ bigN Φ - 1) := by
  have h := isRelPrime_reverse_cPoly_Apoly Φ hunsat
  rw [reverse_cPoly, Bpoly] at h
  exact h.symm

/-- **Irreducibility of `H_M` in the unsatisfiable case**, without the large-gap hypothesis. -/
theorem irreducible_Hfinal (Φ : CNF) (hΦ : Φ ≠ []) (hunsat : ¬Φ.Satisfiable) :
    Irreducible (Hfinal Φ) := by
  rw [Hfinal_eq_gapPoly]
  refine irreducible_gapPoly (reverse_Apoly Φ) (Apoly_coeff_zero_ne_zero Φ hΦ) (bigN_pos Φ)
    (isRelPrime_Apoly_Bpoly Φ hunsat) (FFKThreshold_Mval Φ) ?_
  intro z hz h
  have h' : aeval z (Hpoly Φ (Mval Φ)) = 0 := by rw [← Hfinal, Hfinal_eq_gapPoly]; exact h
  exact hunsat (satisfiable_of_rootOfUnity_root Φ (Mval Φ) hz h')

end SparseIrred.FFK
