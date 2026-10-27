import SparseIrred.Machine.StrClause
import SparseIrred.Machine.StrCnf
import SparseIrred.Machine.Bounds

/-!
# The main branch `x ↦ encPoly (H_M)` as a string function

`hmCoreStr qs t T` computes `encITerms (hmCore qs Ψ)` from the unary prime list
`qs = frame (qs.map unaryN)`, the renumbered formula `t = encCNFU Ψ` (clauses of at most three
literals) and a unary ruler `T` of length at least `20 (w+1)`:

  `N = bigNStr qs`, `cs = frame [C_j]` (`csStr`), `K = degreeStr (flatten cs)`,
  `S_raw = flatten [C_j · reflect_K C_j]` (`sRawStr`),
  `S = canonITermsStr (normalizeZStr S_raw)`, `A = aTermsStr S`, output `outStr N A T`.

`hmStr x` composes the parser, the renumbering, the prime generation with the ruler
`primeRuler x` (length `primeBound |x|`) and `hmCoreStr` with the ruler `wRuler x` (length
`wBound |x|`, which is at least `20 (w+1)` by `twenty_mul_wD_succ_le`).  Both rulers are
`List.replicate`s of explicit polynomial length; their Cobham membership goes through
`SparseGcd.polyUnary`.
-/

open Complexity SparseDiv SparseDiv.StringArith SparseDiv.Appendix SparseGcd Complexity.SAT

namespace SparseIrred.Machine

open SparseIrred

/-! ### Stages -/

/-- The framed list of the clause raw term lists `C_j`. -/
def csStr (qs N t : List Bool) : List Bool := mapBlocks (clauseStr qs N) t

theorem csStr_eq (qs : List ℕ) (N : ℕ) (Ψ : CNF) (h3 : ∀ c ∈ Ψ, c.length ≤ 3) :
    csStr (frame (qs.map unaryN)) (encNat N) (encCNFU Ψ) =
      frame ((Ψ.map (clauseTermsD qs N)).map encITerms) := by
  rw [csStr, encCNFU, mapBlocks_frame, List.map_map, List.map_map]
  exact congrArg frame (List.map_congr_left fun c hc => clauseStr_eq qs N c (h3 c hc))

theorem cobham_csStr_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v => csStr (g₀ v) (g₁ v) (g₂ v) := by
  unfold csStr
  exact TermsStr.cobham_mapBlocks_comp (F := fun c v => clauseStr (g₀ v) (g₁ v) c)
    (cobham_clauseStr_comp (TermsStr.cobham_tail_comp h₀) (TermsStr.cobham_tail_comp h₁) (.proj 0))
    h₂

/-- The offset `K`: the largest raw exponent of all `C_j`. -/
def offsetStr (cs : List Bool) : List Bool := degreeStr (TermsStr.flattenBlocks cs)

theorem offsetStr_eq (Cs : List ITerms) :
    offsetStr (frame (Cs.map encITerms)) = encNat (offsetD Cs) := by
  rw [offsetStr, flattenBlocks_frame_encITerms, degreeStr_encITerms]
  rfl

/-- The raw list of `X^K S(X) = ∑_j C_j(X) · X^K C_j(X⁻¹)`. -/
def sRawStr (K cs : List Bool) : List Bool :=
  TermsStr.flattenBlocks (mapBlocks (fun C => mulITermsStr C (reflectStr K C)) cs)

theorem sRawStr_eq (K : ℕ) (Cs : List ITerms) :
    sRawStr (encNat K) (frame (Cs.map encITerms)) = encITerms (sRawD K Cs) := by
  rw [sRawStr, mapBlocks_frame, List.map_map]
  have h : ((fun C => mulITermsStr C (reflectStr (encNat K) C)) ∘ encITerms) =
      encITerms ∘ fun C => mulITerms C (reflectITerms K C) := by
    funext C
    simp only [Function.comp_apply, reflectStr_eq, mulITermsStr_eq]
  rw [h, ← List.map_map, flattenBlocks_frame_encITerms, sRawD, List.flatMap_def]

theorem cobham_sRawStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => sRawStr (g₀ v) (g₁ v) := by
  unfold sRawStr
  exact TermsStr.cobham_flattenBlocks_comp
    (TermsStr.cobham_mapBlocks_comp (F := fun C v => mulITermsStr C (reflectStr (g₀ v) C))
      (cobham_mulITermsStr_comp (.proj 0)
        (cobham_reflectStr_comp (TermsStr.cobham_tail_comp h₀) (.proj 0))) h₁)

/-- The canonical list of `X^K S`. -/
def sNormStr (qs t : List Bool) : List Bool :=
  canonITermsStr (normalizeZStr
    (sRawStr (offsetStr (csStr qs (bigNStr qs) t)) (csStr qs (bigNStr qs) t)))

theorem sNormStr_eq (qs : List ℕ) (Ψ : CNF) (h3 : ∀ c ∈ Ψ, c.length ≤ 3) :
    sNormStr (frame (qs.map unaryN)) (encCNFU Ψ) = encITerms (sNormD qs Ψ) := by
  rw [sNormStr, bigNStr_eq, csStr_eq qs _ Ψ h3, offsetStr_eq, sRawStr_eq,
    canonITermsStr_normalizeZStr]
  rfl

theorem cobham_sNormStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => sNormStr (g₀ v) (g₁ v) := by
  unfold sNormStr offsetStr
  have hN := cobham_bigNStr_comp h₀
  have hcs := cobham_csStr_comp h₀ hN h₁
  exact cobham_canonITermsStr_comp (cobham_normalizeZStr_comp
    (cobham_sRawStr_comp (cobham_degreeStr_comp (TermsStr.cobham_flattenBlocks_comp hcs)) hcs))

/-- The code of `H_M` from the unary prime list, the renumbered formula and a unary ruler. -/
def hmCoreStr (qs t T : List Bool) : List Bool :=
  outStr (bigNStr qs) (aTermsStr (sNormStr qs t)) T

theorem hmCoreStr_eq (qs : List ℕ) (Ψ : CNF) (h3 : ∀ c ∈ Ψ, c.length ≤ 3) (T : List Bool)
    (hT : 20 * (wD (hmA qs Ψ) + 1) ≤ T.length) :
    hmCoreStr (frame (qs.map unaryN)) (encCNFU Ψ) T = encITerms (hmCore qs Ψ) := by
  rw [hmCoreStr, sNormStr_eq qs Ψ h3, aTermsStr_eq, bigNStr_eq]
  exact outStr_eq _ _ T hT

theorem cobham_hmCoreStr_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v => hmCoreStr (g₀ v) (g₁ v) (g₂ v) := by
  unfold hmCoreStr
  exact cobham_outStr_comp (cobham_bigNStr_comp h₀)
    (cobham_aTermsStr_comp (cobham_sNormStr_comp h₀ h₁)) h₂

/-! ### Rulers -/

/-- Unary ruler for the prime candidates. -/
def primeRuler (x : List Bool) : List Bool := List.replicate (primeBound x.length) true

/-- Unary ruler for `20 (w+1)`. -/
def wRuler (x : List Bool) : List Bool := List.replicate (wBound x.length) true

theorem primeRuler_eq (x : List Bool) : primeRuler x = unaryN (primeBound x.length) := rfl

theorem length_wRuler (x : List Bool) : (wRuler x).length = wBound x.length := by
  simp [wRuler]

theorem cobham_primeRuler : Cobham fun v : Fin 1 → List Bool => primeRuler (v 0) := by
  refine (cobham_polyUnary (Polynomial.C 64 * (Polynomial.X + Polynomial.C 2) ^ 2 + Polynomial.C 1)
    (Cobham.proj (n := 1) 0)).of_eq fun v => ?_
  rw [polyUnary_eq, primeRuler, primeBound, unaryN]
  simp

theorem cobham_wRuler : Cobham fun v : Fin 1 → List Bool => wRuler (v 0) := by
  refine (cobham_polyUnary
    (Polynomial.C 20 * (Polynomial.C 5 +
      Polynomial.C 9 *
        (Polynomial.X * (Polynomial.C 64 * (Polynomial.X + Polynomial.C 2) ^ 2) ^ 6) ^ 2
      + Polynomial.X * (Polynomial.C 64 * (Polynomial.X + Polynomial.C 2) ^ 2) ^ 6))
    (Cobham.proj (n := 1) 0)).of_eq fun v => ?_
  rw [polyUnary_eq, wRuler, wBound, rawBound, unaryN]
  simp

/-! ### The main branch -/

/-- The main branch of the reduction: the code of `H_M` from the code `x` of the formula. -/
def hmStr (x : List Bool) : List Bool :=
  hmCoreStr (primesStr (numVarsU (pairSnd (parseCnfStr x))) (primeRuler x))
    (renumStr (pairSnd (parseCnfStr x))) (wRuler x)

theorem hmStr_eq {x : List Bool} {Φ : CNF} (hx : CNF.decode3? x = some Φ) :
    hmStr x = encITerms (hmTerms (primeBound x.length) Φ) := by
  obtain ⟨rfl, h3⟩ := CNF.decode3?_eq_some_iff.1 hx
  have hp : pairSnd (parseCnfStr Φ.encode) = encCNFU Φ :=
    pairSnd_parseCnfStr (CNF.decode?_encode Φ)
  have hT := twenty_mul_wD_succ_le Φ h3
  rw [← length_wRuler] at hT
  rw [hmStr, hp, numVarsU_eq, primeRuler_eq, primesStr_eq, renumStr_eq, hmTerms,
    firstOddPrimes_encode]
  exact hmCoreStr_eq _ _ (clause_length_le_of_is3CNF (is3CNF_renumber h3)) _ hT

theorem cobham_hmStr : Cobham fun v : Fin 1 → List Bool => hmStr (v 0) := by
  have hp : Cobham fun v : Fin 1 → List Bool => parseCnfStr (v 0) :=
    FP_subset_CobhamFP parseCnfStr_mem_FP
  have ht := cobham_pairSnd_comp hp
  unfold hmStr
  exact cobham_hmCoreStr_comp (cobham_primesStr_comp (cobham_numVarsU_comp ht) cobham_primeRuler)
    (cobham_renumStr_comp ht) cobham_wRuler

end SparseIrred.Machine
