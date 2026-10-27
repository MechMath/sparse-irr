import SparseIrred.Construction.RootsOfUnity

/-!
# ② Excluding roots of unity of every order: the norm argument (notes p. 7)

"`H_M` has a root of unity precisely in the satisfiable case, for every `M ≥ 0`.  For if
`H_M(ζ) = 0` and `ζ` is any root of unity, then every conjugate `η` of `ζ` also satisfies
`H_M(η) = 0` and `0 ≤ S(η) = ∑_j |C_j(η)|² = |η^M (η^N - 1)| / 3 ≤ 2/3`.  The algebraic integer
`S(ζ)` has these real numbers as all its conjugates.  If it were nonzero, its integral nonzero norm
would have absolute value at least `1`, whereas the displayed bound makes it less than `1`.  Hence
`S(ζ) = 0`, and (1) gives `ζ^N = 1`.  The converse follows directly from (1).  In particular,
unsatisfiable instances give `H_M` with no cyclotomic factor."

The argument works for roots of unity of *any* order, not only `N`-th roots.
-/

open Polynomial LaurentPolynomial

namespace SparseIrred

open Complexity.SAT

/-- The norm step: an algebraic integer all of whose complex embeddings have absolute value `< 1`
is zero (its norm is an integer of absolute value `< 1`). -/
theorem eq_zero_of_isIntegral_of_forall_norm_embedding_lt_one {K : Type*} [Field K]
    [NumberField K] {α : K} (hα : IsIntegral ℤ α) (h : ∀ σ : K →+* ℂ, ‖σ α‖ < 1) : α = 0 := by
  -- the norm `N_{K/ℚ}(α)` is an algebraic integer lying in `ℚ`, hence an integer
  have hint : IsIntegral ℤ (Algebra.norm ℚ α) := Algebra.isIntegral_norm ℚ hα
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  -- its image in `ℂ` is the product of the conjugates of `α`
  have hprod : algebraMap ℚ ℂ (Algebra.norm ℚ α) = ∏ σ : K →ₐ[ℚ] ℂ, σ α :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ α
  -- there is at least one embedding
  classical
  let σ₀ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hlt : ‖∏ σ : K →ₐ[ℚ] ℂ, σ α‖ < 1 := by
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ₀)]
    have h1 : ∏ σ ∈ Finset.univ.erase σ₀, ‖σ α‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun σ _ => (h σ.toRingHom).le
    have h2 : ‖σ₀ α‖ < 1 := h σ₀.toRingHom
    calc ‖σ₀ α‖ * ∏ σ ∈ Finset.univ.erase σ₀, ‖σ α‖ ≤ ‖σ₀ α‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ < 1 := by rwa [mul_one]
  rw [← hprod, ← hn] at hlt
  have hn0 : n = 0 := by
    have : ‖((n : ℚ) : ℂ)‖ < 1 := by simpa using hlt
    rw [Complex.norm_ratCast] at this
    have : |(n : ℝ)| < 1 := by exact_mod_cast this
    rw [abs_lt] at this
    have h1 : (-1 : ℤ) < n := by exact_mod_cast this.1
    have h2 : n < 1 := by exact_mod_cast this.2
    omega
  rw [hn0, map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hn
  exact hn

/-! ### Conjugate values of `S` -/

/-- Laurent evaluation commutes with ring homomorphisms. -/
private theorem map_eval₂_laurent {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u : Rˣ) (p : ℤ[T;T⁻¹]) :
    f (LaurentPolynomial.eval₂ (Int.castRingHom R) u p) =
      LaurentPolynomial.eval₂ (Int.castRingHom S) (Units.map (f : R →* S) u) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T n a =>
    rw [eval₂_C_mul_T, eval₂_C_mul_T, map_mul, eq_intCast, eq_intCast, map_intCast, ← map_zpow]
    rfl

/-- Evaluation of `S` commutes with ring homomorphisms. -/
private theorem map_evalS {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Φ : CNF)
    (u : Rˣ) : f (evalS Φ u) = evalS Φ (Units.map (f : R →* S) u) :=
  map_eval₂_laurent f u (Spoly Φ)

/-- Conjugate roots: if `H(ζ) = 0` for a primitive `k`-th root of unity `ζ`, then `H(η) = 0` for
every primitive `k`-th root of unity `η` (the minimal polynomial of `ζ` over `ℚ` is the `k`-th
cyclotomic polynomial). -/
private theorem aeval_eq_zero_of_isPrimitiveRoot (H : ℤ[X]) {k : ℕ} (hk : 0 < k) {ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ k) (hη : IsPrimitiveRoot η k) (h : aeval ζ H = 0) :
    aeval η H = 0 := by
  have hdvd : minpoly ℚ ζ ∣ H.map (algebraMap ℤ ℚ) :=
    minpoly.dvd ℚ ζ (by rw [aeval_map_algebraMap]; exact h)
  rw [← cyclotomic_eq_minpoly_rat hζ hk] at hdvd
  obtain ⟨r, hr⟩ := hdvd
  have hc : aeval η (cyclotomic k ℚ) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]; exact hη.isRoot_cyclotomic hk
  rw [← aeval_map_algebraMap ℚ, hr, map_mul, hc, zero_mul]

/-- `H_M(η) = 3 η^D S(η) + η^M (η^N - 1)` at every unit `η`. -/
private theorem aeval_Hpoly (Φ : CNF) (M : ℕ) (η : ℂˣ) :
    aeval (η : ℂ) (Hpoly Φ M) =
      3 * (η : ℂ) ^ Dexp Φ * evalS Φ η + (η : ℂ) ^ M * ((η : ℂ) ^ bigN Φ - 1) := by
  rw [Hpoly, map_add, aeval_Apoly, map_mul, Bpoly]
  simp

/-- Every conjugate value of `S` lies in `[0, 2/3]`: if `|η| = 1` and `H_M(η) = 0`, then
`S(η) = ∑_j |C_j(η)|²` is a real number with `0 ≤ S(η) = |η^M (η^N - 1)| / 3 ≤ 2/3`. -/
theorem evalS_mem_Icc_of_aeval_Hpoly_eq_zero (Φ : CNF) (M : ℕ) (η : ℂˣ) (hη : ‖(η : ℂ)‖ = 1)
    (h : aeval (η : ℂ) (Hpoly Φ M) = 0) :
    ∃ s : ℝ, evalS Φ η = (s : ℂ) ∧ 0 ≤ s ∧ s ≤ 2 / 3 := by
  set s : ℝ := (Φ.map fun c => ‖aeval (η : ℂ) (clausePoly Φ c)‖ ^ 2).sum
  have hS : evalS Φ η = (s : ℂ) := evalS_eq_sum_normSq Φ η hη
  have hs0 : 0 ≤ s := List.sum_nonneg fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    positivity
  refine ⟨s, hS, hs0, ?_⟩
  rw [aeval_Hpoly, hS] at h
  have heq : 3 * (η : ℂ) ^ Dexp Φ * (s : ℂ) = -((η : ℂ) ^ M * ((η : ℂ) ^ bigN Φ - 1)) :=
    eq_neg_of_add_eq_zero_left h
  have hn := congrArg norm heq
  rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hη, one_pow, one_pow,
    mul_one, one_mul, Complex.norm_real, Real.norm_of_nonneg hs0] at hn
  have h3 : ‖(3 : ℂ)‖ = 3 := by simp
  rw [h3] at hn
  have hle : ‖(η : ℂ) ^ bigN Φ - 1‖ ≤ 2 := by
    calc ‖(η : ℂ) ^ bigN Φ - 1‖ ≤ ‖(η : ℂ) ^ bigN Φ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hη, one_pow, norm_one]; norm_num
  linarith

open IntermediateField in
/-- If `H_M(ζ) = 0` for a root of unity `ζ` (of any order), then `S(ζ) = 0`. -/
theorem evalS_eq_zero_of_rootOfUnity (Φ : CNF) (M : ℕ) (ζ : ℂˣ)
    (hroot : ∃ n, 0 < n ∧ (ζ : ℂ) ^ n = 1) (h : aeval (ζ : ℂ) (Hpoly Φ M) = 0) :
    evalS Φ ζ = 0 := by
  -- `ζ` is a primitive `k`-th root of unity, `k = orderOf ζ`
  set k := orderOf (ζ : ℂ)
  have hk : 0 < k := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 hroot)
  have hζ : IsPrimitiveRoot (ζ : ℂ) k := IsPrimitiveRoot.orderOf _
  -- every conjugate value of `S` has absolute value at most `2/3`
  have hconj : ∀ η : ℂˣ, IsPrimitiveRoot (η : ℂ) k → ‖evalS Φ η‖ ≤ 2 / 3 := by
    intro η hη
    obtain ⟨s, hs, hs0, hs1⟩ := evalS_mem_Icc_of_aeval_Hpoly_eq_zero Φ M η
      (hη.norm'_eq_one hk.ne') (aeval_eq_zero_of_isPrimitiveRoot _ hk hζ hη h)
    rw [hs, Complex.norm_real, Real.norm_of_nonneg hs0]
    exact hs1
  -- the number field `K = ℚ(ζ) ⊆ ℂ`
  have hiQ : IsIntegral ℚ (ζ : ℂ) := (hζ.isIntegral hk).tower_top
  have : FiniteDimensional ℚ ℚ⟮(ζ : ℂ)⟯ := IntermediateField.adjoin.finiteDimensional hiQ
  have : NumberField ℚ⟮(ζ : ℂ)⟯ := ⟨⟩
  set z : ℚ⟮(ζ : ℂ)⟯ := IntermediateField.AdjoinSimple.gen ℚ (ζ : ℂ)
  have hzζ : algebraMap ℚ⟮(ζ : ℂ)⟯ ℂ z = ζ := IntermediateField.AdjoinSimple.algebraMap_gen ℚ _
  have hz : IsPrimitiveRoot z k :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ℚ⟮(ζ : ℂ)⟯ ℂ) (by rwa [hzζ])
      (algebraMap ℚ⟮(ζ : ℂ)⟯ ℂ).injective
  -- `z` is a unit of the ring of integers (its inverse `z^{k-1}` is integral)
  let z' : NumberField.RingOfIntegers ℚ⟮(ζ : ℂ)⟯ :=
    ⟨z, (mem_integralClosure_iff _ _).2 (hz.isIntegral hk)⟩
  have hz' : z' ^ k = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact hz.pow_eq_one
  let u' : (NumberField.RingOfIntegers ℚ⟮(ζ : ℂ)⟯)ˣ := (IsUnit.of_pow_eq_one hz' hk.ne').unit
  let u : (ℚ⟮(ζ : ℂ)⟯)ˣ := Units.map (algebraMap (NumberField.RingOfIntegers ℚ⟮(ζ : ℂ)⟯)
    ℚ⟮(ζ : ℂ)⟯ : NumberField.RingOfIntegers ℚ⟮(ζ : ℂ)⟯ →* ℚ⟮(ζ : ℂ)⟯) u'
  have hu : (u : ℚ⟮(ζ : ℂ)⟯) = z := rfl
  -- `α = S(u)` is an algebraic integer
  have hαint : IsIntegral ℤ (evalS Φ u) := by
    rw [← map_evalS]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  -- all its conjugates `σ α = S(σ u)` have absolute value `≤ 2/3 < 1`
  have hα : evalS Φ u = 0 := by
    refine eq_zero_of_isIntegral_of_forall_norm_embedding_lt_one hαint fun σ => ?_
    rw [map_evalS]
    refine lt_of_le_of_lt (hconj _ ?_) (by norm_num)
    rw [Units.coe_map, MonoidHom.coe_coe, hu]
    exact hz.map_of_injective σ.injective
  -- map back to `ℂ` through the inclusion, which sends `u` to `ζ`
  have h0 := congrArg (algebraMap ℚ⟮(ζ : ℂ)⟯ ℂ) hα
  rw [map_evalS, map_zero] at h0
  have hmap : Units.map (algebraMap ℚ⟮(ζ : ℂ)⟯ ℂ : ℚ⟮(ζ : ℂ)⟯ →* ℂ) u = ζ := by
    ext
    rw [Units.coe_map, MonoidHom.coe_coe, hu, hzζ]
  rwa [hmap] at h0

/-- If `H_M` vanishes at a root of unity (of any order), then `Φ` is satisfiable. -/
theorem satisfiable_of_rootOfUnity_root (Φ : CNF) (M : ℕ) {ζ : ℂ}
    (hroot : ∃ n, 0 < n ∧ ζ ^ n = 1) (h : aeval ζ (Hpoly Φ M) = 0) : Φ.Satisfiable := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    obtain ⟨n, hn, h0⟩ := hroot
    rw [zero_pow hn.ne'] at h0
    exact zero_ne_one h0
  set η : ℂˣ := Units.mk0 ζ hζ0
  have hη : (η : ℂ) = ζ := rfl
  rw [← hη] at hroot h
  have hS : evalS Φ η = 0 := evalS_eq_zero_of_rootOfUnity Φ M η hroot h
  -- with `S(ζ) = 0`, `H_M(ζ) = ζ^M (ζ^N - 1)`, hence `ζ^N = 1`
  rw [aeval_Hpoly, hS, mul_zero, zero_add] at h
  have hN : (η : ℂ) ^ bigN Φ = 1 :=
    sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left (pow_ne_zero _ η.ne_zero))
  exact satisfiable_of_root Φ η hN hS

/-- `H_M` has a root of unity exactly in the satisfiable case, for every `M`. -/
theorem exists_rootOfUnity_root_iff (Φ : CNF) (M : ℕ) :
    (∃ ζ : ℂ, (∃ n, 0 < n ∧ ζ ^ n = 1) ∧ aeval ζ (Hpoly Φ M) = 0) ↔ Φ.Satisfiable := by
  constructor
  · rintro ⟨ζ, hroot, h⟩
    exact satisfiable_of_rootOfUnity_root Φ M hroot h
  · intro hsat
    obtain ⟨ζ, hN, hS⟩ := exists_root_of_satisfiable Φ hsat
    refine ⟨ζ, ⟨bigN Φ, bigN_pos Φ, hN⟩, ?_⟩
    rw [aeval_Hpoly, hS, hN, mul_zero, zero_add, sub_self, mul_zero]

/-- Unsatisfiable instances give `H_M` with no cyclotomic factor. -/
theorem not_cyclotomic_dvd_Hpoly (Φ : CNF) (M : ℕ) (hunsat : ¬Φ.Satisfiable) {n : ℕ}
    (hn : 0 < n) : ¬cyclotomic n ℚ ∣ (Hpoly Φ M).map (Int.castRingHom ℚ) := by
  rintro ⟨r, hr⟩
  have hη := Complex.isPrimitiveRoot_exp n hn.ne'
  set η := Complex.exp (2 * Real.pi * Complex.I / n)
  have hc : aeval η (cyclotomic n ℚ) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]; exact hη.isRoot_cyclotomic hn
  have hH : aeval η (Hpoly Φ M) = 0 := by
    rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, hr, map_mul, hc, zero_mul]
  exact hunsat (satisfiable_of_rootOfUnity_root Φ M ⟨n, hn, hη.pow_eq_one⟩ hH)

end SparseIrred
