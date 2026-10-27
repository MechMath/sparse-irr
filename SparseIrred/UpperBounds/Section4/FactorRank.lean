import SparseIrred.UpperBounds.FrobeniusMatrix
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The number of factors and the Frobenius fixed space

This module proves the full dimension statement in Section 4, equation (49), using
the Chinese remainder decomposition of the actual quotient algebra. The number of
distinct normalized irreducible factors is defined from `normalizedFactors`.
-/

open Polynomial UniqueFactorizationMonoid

namespace SparseIrred.UpperBounds

/-- An algebra isomorphism identifies the two spaces of Frobenius fixed points. -/
noncomputable def frobeniusFixedSpaceEquiv {K R S : Type*}
    [Field K] [Fintype K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (e : R ≃ₐ[K] S) : frobeniusFixedSpace K R ≃ₗ[K] frobeniusFixedSpace K S :=
  e.toLinearEquiv.ofSubmodules _ _ (by
    ext y
    simp only [Submodule.mem_map, mem_frobeniusFixedSpace]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e x ^ Fintype.card K = e x
      simpa only [map_pow] using congrArg e hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      simpa only [map_pow] using congrArg e.symm hy)

/-- Chinese remainder decomposition for a product of pairwise coprime polynomials. -/
noncomputable def adjoinRootProductEquiv {K ι : Type*} [Field K] [Fintype ι]
    (g : ι → K[X]) (hg : Pairwise (fun i j ↦ IsCoprime (g i) (g j))) :
    AdjoinRoot (∏ i, g i) ≃ₐ[K] (∀ i, AdjoinRoot (g i)) := by
  let I : ι → Ideal K[X] := fun i ↦ Ideal.span {g i}
  have hI : Pairwise (fun i j ↦ IsCoprime (I i) (I j)) := fun i j hij ↦
    (Ideal.isCoprime_span_singleton_iff _ _).mpr (hg hij)
  have heq : Ideal.span {∏ i, g i} = ⨅ i, I i :=
    (Ideal.iInf_span_singleton (fun i j hij ↦ hg hij)).symm
  let e : AdjoinRoot (∏ i, g i) ≃+* (∀ i, AdjoinRoot (g i)) :=
    (Ideal.quotEquivOfEq heq).trans (Ideal.quotientInfRingEquivPiQuotient I hI)
  exact { e with commutes' := fun c ↦ rfl }

/-- In a product of field extensions, each factor contributes one fixed dimension. -/
theorem finrank_frobeniusFixedSpace_pi {K ι : Type*} [Field K] [Fintype K]
    [Fintype ι] (L : ι → Type*) [∀ i, Field (L i)] [∀ i, Algebra K (L i)] :
    Module.finrank K (frobeniusFixedSpace K (∀ i, L i)) = Fintype.card ι := by
  let c : (ι → K) →ₗ[K] frobeniusFixedSpace K (∀ i, L i) :=
    { toFun := fun x ↦ ⟨fun i ↦ algebraMap K (L i) (x i), by
        rw [mem_frobeniusFixedSpace]
        funext i
        exact (pow_card_eq_self_iff_scalar _).mpr ⟨x i, rfl⟩⟩
      map_add' := by intros; apply Subtype.ext; ext; simp
      map_smul' := by intros; apply Subtype.ext; ext; simp [Algebra.smul_def] }
  have hc : Function.Bijective c := by
    constructor
    · intro x y h
      funext i
      exact (algebraMap K (L i)).injective (congrArg (fun z ↦ z.val i) h)
    · intro y
      have hy (i) : ∃ a : K, algebraMap K (L i) a = y.val i :=
        (pow_card_eq_self_iff_scalar _).mp
          (congrFun ((mem_frobeniusFixedSpace y.val).mp y.property) i)
      choose a ha using hy
      exact ⟨a, Subtype.ext (funext ha)⟩
  exact (LinearEquiv.ofBijective c hc).finrank_eq.symm.trans (Module.finrank_pi K)

/-- Full fixed-space dimension for a specified coprime family of irreducible factors. -/
theorem finrank_frobeniusFixedSpace_product {K ι : Type*} [Field K] [Fintype K]
    [Fintype ι] (g : ι → K[X]) (hirr : ∀ i, Irreducible (g i))
    (hcop : Pairwise (fun i j ↦ IsCoprime (g i) (g j))) :
    Module.finrank K (frobeniusFixedSpace K (AdjoinRoot (∏ i, g i))) =
      Fintype.card ι := by
  have : ∀ i : ι, Fact (Irreducible (g i)) := fun i ↦ ⟨hirr i⟩
  exact (frobeniusFixedSpaceEquiv (adjoinRootProductEquiv g hcop)).finrank_eq.trans
    (finrank_frobeniusFixedSpace_pi (fun i ↦ AdjoinRoot (g i)))

/-- The distinct normalized irreducible factors of a polynomial. -/
noncomputable def distinctFactorSet {K : Type*} [Field K] (f : K[X]) : Finset K[X] := by
  classical
  exact (normalizedFactors f).toFinset

/-- The number `r` in the paper: distinct factors, with multiplicities discarded. -/
noncomputable def distinctFactorCount {K : Type*} [Field K] (f : K[X]) : ℕ :=
  (distinctFactorSet f).card

theorem irreducible_of_mem_distinctFactorSet {K : Type*} [Field K] (f : K[X])
    (g : distinctFactorSet f) : Irreducible (g : K[X]) := by
  classical
  exact UniqueFactorizationMonoid.irreducible_of_normalized_factor _
    (Multiset.mem_toFinset.mp g.property)

theorem distinctFactorSet_pairwise_coprime {K : Type*} [Field K] (f : K[X]) :
    Pairwise (fun g h : distinctFactorSet f ↦ IsCoprime (g : K[X]) (h : K[X])) := by
  classical
  intro g h hne
  apply (irreducible_of_mem_distinctFactorSet f g).coprime_iff_not_dvd.mpr
  intro hd
  apply hne
  apply Subtype.ext
  exact UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
    (Multiset.mem_toFinset.mp g.property) (Multiset.mem_toFinset.mp h.property)
    ((irreducible_of_mem_distinctFactorSet f g).associated_of_dvd
      (irreducible_of_mem_distinctFactorSet f h) hd)

theorem distinctFactorSet_prod_associated {K : Type*} [Field K] (f : K[X])
    (hf : f ≠ 0) (hsq : Squarefree f) :
    Associated (∏ g : distinctFactorSet f, (g : K[X])) f := by
  classical
  rw [Finset.prod_coe_sort (distinctFactorSet f) (fun p ↦ p)]
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf).mp hsq
  change Associated ((normalizedFactors f).toFinset.prod id) f
  rw [Finset.prod, Multiset.map_id, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  exact UniqueFactorizationMonoid.prod_normalizedFactors hf

/-- Equation (49): for every nonzero squarefree polynomial, the dimension of the
Frobenius fixed space is exactly its number of distinct irreducible factors. -/
theorem finrank_frobeniusFixedSpace_eq_distinctFactorCount {K : Type*}
    [Field K] [Fintype K] (f : K[X]) (hf : f ≠ 0) (hsq : Squarefree f) :
    Module.finrank K (frobeniusFixedSpace K (AdjoinRoot f)) = distinctFactorCount f := by
  classical
  let g : distinctFactorSet f → K[X] := fun g ↦ g.val
  have he := AdjoinRoot.algEquivOfAssociated K f (∏ i, g i)
    (distinctFactorSet_prod_associated f hf hsq).symm
  exact (frobeniusFixedSpaceEquiv he).finrank_eq.trans
    ((finrank_frobeniusFixedSpace_product g (irreducible_of_mem_distinctFactorSet f)
      (distinctFactorSet_pairwise_coprime f)).trans (by simp [distinctFactorCount]))

/-- The full rank identity in (49), including polynomials with more than one factor. -/
theorem frobeniusMatrix_rank_add_distinctFactorCount {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : f ≠ 0) (hsq : Squarefree f) :
    (frobeniusMatrix (AdjoinRoot.powerBasis hf) - 1).rank + distinctFactorCount f =
      f.natDegree := by
  have hr := frobenius_rank_add_fixedSpace (AdjoinRoot.powerBasis hf).basis
  rw [finrank_frobeniusFixedSpace_eq_distinctFactorCount f hf hsq] at hr
  simpa only [Fintype.card_fin, frobeniusMatrix, AdjoinRoot.powerBasis_dim] using hr

/-- Equivalently, the rank is the degree minus the number of distinct factors. -/
theorem frobeniusMatrix_rank_eq_degree_sub_distinctFactorCount {K : Type*}
    [Field K] [Fintype K] (f : K[X]) (hf : f ≠ 0) (hsq : Squarefree f) :
    (frobeniusMatrix (AdjoinRoot.powerBasis hf) - 1).rank =
      f.natDegree - distinctFactorCount f := by
  have := frobeniusMatrix_rank_add_distinctFactorCount f hf hsq
  omega

end SparseIrred.UpperBounds
