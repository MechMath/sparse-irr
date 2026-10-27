import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# Finite-field irreducibility and Frobenius fixed points

The resultant implements the squarefreeness filter in Section 4. The fixed-point space
is defined on the actual quotient algebra `K[X]/(f)`, over any finite field `K`.
-/

open Polynomial

namespace SparseIrred.UpperBounds

/-- The resultant test is valid in every characteristic, including constant derivatives. -/
theorem resultant_derivative_ne_zero_iff {K : Type*} [Field K] [Finite K]
    (f : K[X]) (hf : f ≠ 0) :
    f.resultant f.derivative ≠ 0 ↔ Squarefree f := by
  rw [← PerfectField.separable_iff_squarefree, Polynomial.separable_def]
  constructor
  · intro h
    by_contra hc
    exact h (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hf, hc⟩)
  · exact Polynomial.resultant_ne_zero _ _

/-- Positive-degree polynomials with identically zero derivative cannot be irreducible. -/
theorem not_irreducible_of_derivative_eq_zero {K : Type*} [Field K] [Finite K]
    (f : K[X]) (hf : 0 < f.natDegree) (hd : f.derivative = 0) : ¬Irreducible f := by
  intro hirr
  have hc : IsCoprime f f.derivative := (PerfectField.separable_of_irreducible hirr)
  rw [hd, isCoprime_zero_right] at hc
  have := Polynomial.natDegree_eq_zero_of_isUnit hc
  omega

/-- The `q`-power fixed elements in a field extension are exactly the base field. -/
theorem pow_card_eq_self_iff_scalar {K L : Type*} [Field K] [Fintype K]
    [Field L] [Algebra K L] (x : L) :
    x ^ Fintype.card K = x ↔ ∃ c : K, algebraMap K L c = x := by
  classical
  let p : K[X] := X ^ Fintype.card K - X
  have hp : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have hcard : p.roots.card = p.natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X, ← Finset.card_def, Finset.card_univ]
    exact (FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card).symm
  have hr := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (algebraMap K L).injective hcard
  constructor
  · intro hx
    have hxroot : x ∈ (p.map (algebraMap K L)).roots := by
      apply (Polynomial.mem_roots ((Polynomial.map_ne_zero_iff
        (algebraMap K L).injective).mpr hp)).mpr
      simpa [p, Polynomial.IsRoot, sub_eq_zero] using hx
    rw [← hr, FiniteField.roots_X_pow_card_sub_X] at hxroot
    obtain ⟨c, _, hc⟩ := Multiset.mem_map.mp hxroot
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

/-- The linear map whose matrix is `B-I` in the paper. -/
def frobeniusDifference (K R : Type*) [Field K] [Fintype K] [CommRing R] [Algebra K R] :
    R →ₗ[K] R :=
  (FiniteField.frobeniusAlgHom K R).toLinearMap - LinearMap.id

/-- The Berlekamp fixed-point space. -/
def frobeniusFixedSpace (K R : Type*) [Field K] [Fintype K] [CommRing R] [Algebra K R] :
    Submodule K R :=
  LinearMap.ker (frobeniusDifference K R)

@[simp]
theorem mem_frobeniusFixedSpace {K R : Type*} [Field K] [Fintype K] [CommRing R]
    [Algebra K R] (x : R) :
    x ∈ frobeniusFixedSpace K R ↔ x ^ Fintype.card K = x := by
  change ((FiniteField.frobeniusAlgHom K R) x - x = 0 ↔ _)
  rw [sub_eq_zero]
  rfl

/-- Constants always belong to the Frobenius fixed-point space. -/
theorem scalar_mem_frobeniusFixedSpace {K R : Type*} [Field K] [Fintype K] [CommRing R]
    [Algebra K R] (c : K) : algebraMap K R c ∈ frobeniusFixedSpace K R := by
  rw [mem_frobeniusFixedSpace, ← map_pow, FiniteField.pow_card]

/-- For a field extension, the fixed-point space has dimension exactly one. -/
theorem finrank_frobeniusFixedSpace_field {K L : Type*} [Field K] [Fintype K]
    [Field L] [Algebra K L] : Module.finrank K (frobeniusFixedSpace K L) = 1 := by
  let oneFixed : frobeniusFixedSpace K L := ⟨1, by simp⟩
  apply finrank_eq_one oneFixed
  · intro h
    have := congrArg Subtype.val h
    exact one_ne_zero this
  · intro x
    obtain ⟨c, hc⟩ := (pow_card_eq_self_iff_scalar x.val).mp
      ((mem_frobeniusFixedSpace x.val).mp x.property)
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa [oneFixed, Algebra.smul_def] using hc

/-- Dimension one means that all fixed points are constants. -/
theorem finrank_frobeniusFixedSpace_eq_one_iff {K R : Type*} [Field K] [Fintype K]
    [CommRing R] [Nontrivial R] [Algebra K R] [FiniteDimensional K R] :
    Module.finrank K (frobeniusFixedSpace K R) = 1 ↔
      ∀ x : R, x ^ Fintype.card K = x → ∃ c : K, algebraMap K R c = x := by
  constructor
  · intro hd x hx
    have hle : Submodule.span K ({1} : Set R) ≤ frobeniusFixedSpace K R := by
      rw [Submodule.span_singleton_le_iff_mem]
      simp
    have heq : Submodule.span K ({1} : Set R) = frobeniusFixedSpace K R :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton one_ne_zero, hd])
    have hx' : x ∈ Submodule.span K ({1} : Set R) := by
      rw [heq, mem_frobeniusFixedSpace]
      exact hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx'
    exact ⟨c, by simpa [Algebra.smul_def] using hc⟩
  · intro h
    let oneFixed : frobeniusFixedSpace K R := ⟨1, by simp⟩
    apply finrank_eq_one oneFixed
    · intro he
      exact one_ne_zero (congrArg Subtype.val he)
    · intro x
      obtain ⟨c, hc⟩ := h x.val ((mem_frobeniusFixedSpace x.val).mp x.property)
      exact ⟨c, Subtype.ext (by simpa [oneFixed, Algebra.smul_def] using hc)⟩

/-- A coprime nontrivial factorization produces a nonconstant Frobenius fixed point.
This is the idempotent argument behind the Berlekamp criterion. -/
theorem exists_nonscalar_fixed_of_coprime_factors {K : Type*} [Field K] [Fintype K]
    (g h : K[X]) (hcop : IsCoprime g h) (hg : ¬IsUnit g) (hh : ¬IsUnit h) :
    ∃ x : AdjoinRoot (g * h), x ^ Fintype.card K = x ∧
      ¬∃ c : K, algebraMap K (AdjoinRoot (g * h)) c = x := by
  obtain ⟨a, b, hab⟩ := hcop
  let e := AdjoinRoot.mk (g * h) (a * g)
  have he : IsIdempotentElem e := by
    change e * e = e
    apply sub_eq_zero.mp
    change AdjoinRoot.mk (g * h) ((a * g) * (a * g) - a * g) = 0
    rw [AdjoinRoot.mk_eq_zero]
    have heq : (a * g) * (a * g) - a * g = -(a * b) * (g * h) := by
      linear_combination a * g * hab
    rw [heq]
    exact dvd_mul_left _ _
  refine ⟨e, he.pow_eq Fintype.card_pos.ne', ?_⟩
  rintro ⟨c, hc⟩
  have hdiv : g * h ∣ a * g - C c := by
    apply AdjoinRoot.mk_eq_mk.mp
    exact hc.symm
  have hgc : g ∣ C c := by
    have hd : g ∣ a * g - C c := dvd_trans (dvd_mul_right g h) hdiv
    have := dvd_sub (dvd_mul_left g a) hd
    simpa using this
  have hc0 : c = 0 := by
    by_contra hc0
    exact hg (isUnit_of_dvd_unit hgc (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)))
  rw [hc0, C_0, sub_zero] at hdiv
  have hhag : h ∣ a * g := dvd_trans (dvd_mul_left h g) hdiv
  have hhone : h ∣ (1 : K[X]) := by
    rw [← hab]
    exact dvd_add hhag (dvd_mul_left h b)
  exact hh (isUnit_of_dvd_one hhone)

/-- The algebraic Berlekamp criterion on the actual quotient of a squarefree polynomial.
The proof covers every finite characteristic and every finite base field. -/
theorem irreducible_iff_frobeniusFixedSpace_finrank {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) (hsq : Squarefree f) :
    Irreducible f ↔ Module.finrank K (frobeniusFixedSpace K (AdjoinRoot f)) = 1 := by
  have hf0 : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hf
  have : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f (by
    rw [Polynomial.degree_eq_natDegree hf0]
    exact_mod_cast hf.ne')
  have : FiniteDimensional K (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hf0).basis
  constructor
  · intro hi
    have : Fact (Irreducible f) := ⟨hi⟩
    exact finrank_frobeniusFixedSpace_field
  · intro hd
    have hscalar := finrank_frobeniusFixedSpace_eq_one_iff.mp hd
    refine ⟨?_, ?_⟩
    · intro hu
      have := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · intro g h heq
      by_contra hn
      push Not at hn
      have hcop : IsCoprime g h :=
        isRelPrime_iff_isCoprime.mp (IsRelPrime.of_squarefree_mul (heq ▸ hsq))
      obtain ⟨x, hx, hnc⟩ := exists_nonscalar_fixed_of_coprime_factors g h hcop hn.1 hn.2
      subst f
      exact hnc (hscalar x hx)

end SparseIrred.UpperBounds
