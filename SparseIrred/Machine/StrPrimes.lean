import SparseIrred.Machine.StrArith

/-!
# The first `n` odd primes and `N = ∏ q_i` as strings

Candidates `c < T` are enumerated in unary by `TermsStr.idxBlocks` (`T` is a unary ruler of
length `primeBound |x|`, a polynomial in the input length).  Primality of a unary candidate is
trial division by every `d < c` (`dvdBits` on the binary forms).  Primes are kept in unary
(`frame (qs.map unaryN)`): the `r < q_i` loop of `P⁻_i` needs `q_i` in unary, and the binary form
is recomputed by `unaryToBinStr`.
-/

open Complexity SparseDiv SparseDiv.StringArith SparseGcd

namespace SparseIrred.Machine

/-! ### Trial division -/

theorem dvdBits_encNat (c d : ℕ) (hd : d ≠ 0) :
    dvdBits (encNat c) (encNat d) = [decide (d ∣ c)] := by
  have hd' : decNat (encNat d) ≠ 0 := by rwa [decNat_encNat]
  rcases isZeroBits_flag (modBits (encNat c) (encNat d)) with h | h
  · have h1 : dvdBits (encNat c) (encNat d) = [true] := h
    have h2 := (dvdBits_eq_true_iff _ _ hd').1 h1
    rw [decNat_encNat, decNat_encNat] at h2
    rw [h1]
    simp [h2]
  · have h1 : dvdBits (encNat c) (encNat d) = [false] := h
    have h2 : ¬ d ∣ c := fun hdc => by
      have := (dvdBits_eq_true_iff (encNat c) (encNat d) hd').2
        (by rwa [decNat_encNat, decNat_encNat])
      rw [h1] at this
      simp at this
    rw [h1]
    simp [h2]

/-- One trial-division step for the candidate (in binary) `cB` and the unary divisor `d`:
keep `acc` true iff `d < 2` or `d ∤ c`. -/
def tdStep (cB acc d : List Bool) : List Bool :=
  andBit acc (orBit (Cobham.lenLeFlag [true] d) (notBit (dvdBits cB (unaryToBinStr d))))

/-- `[true]` iff the unary `c` is an odd prime (`3 ≤ c` and no divisor `2 ≤ d < c`). -/
def isOddPrimeU (c : List Bool) : List Bool :=
  andBit (Cobham.lenLeFlag c [true, true, true])
    (foldBlocks (tdStep (unaryToBinStr c)) [true] (TermsStr.idxBlocks c))

theorem isOddPrimeU_eq (c : ℕ) : isOddPrimeU (unaryN c) = [decide (3 ≤ c ∧ c.Prime)] := by
  have hstep : ∀ (d : ℕ) (b : Bool), tdStep (encNat c) [b] (unaryN d) =
      [b && decide (d < 2 ∨ ¬ d ∣ c)] := by
    intro d b
    rw [tdStep, lenLeFlag_eq_decide, length_unaryN, List.length_singleton]
    by_cases hd : d < 2
    · have : d ≤ 1 := by omega
      simp [this, hd, orBit]
    · have : ¬ d ≤ 1 := by omega
      rw [unaryToBinStr_unaryN, dvdBits_encNat c d (by omega)]
      simp [this, hd]
  have key : ∀ (ds : List ℕ) (b : Bool), (ds.map unaryN).foldl (tdStep (encNat c)) [b] =
      [b && decide (∀ d ∈ ds, d < 2 ∨ ¬ d ∣ c)] := by
    intro ds
    induction ds with
    | nil => intro b; simp
    | cons d ds ih =>
      intro b
      rw [List.map_cons, List.foldl_cons, hstep, ih]
      simp only [List.mem_cons, forall_eq_or_imp, Bool.decide_and, Bool.and_assoc]
  rw [isOddPrimeU, lenLeFlag_eq_decide, unaryToBinStr_unaryN, TermsStr.idxBlocks_unaryN,
    foldBlocks_frame, key, andBit_single, Bool.true_and, length_unaryN]
  simp only [List.length_cons, List.length_nil, List.mem_range]
  by_cases h3 : 3 ≤ c
  · have hp : (∀ d < c, d ≤ 1 ∨ ¬ d ∣ c) ↔ c.Prime := by
      rw [Nat.prime_def_lt']
      constructor
      · intro h
        exact ⟨by omega, fun m hm hmc => (h m hmc).resolve_left (by omega)⟩
      · rintro ⟨-, h⟩ d hd
        by_cases hd2 : d ≤ 1
        · exact Or.inl hd2
        · exact Or.inr (h d (by omega) hd)
    simpa [h3] using hp
  · simp [h3]

theorem cobham_isOddPrimeU_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => isOddPrimeU (g v) := by
  have hstep : Cobham fun w : Fin 3 → List Bool => tdStep (w 2) (w 0) (w 1) := by
    unfold tdStep
    exact Cobham.andFn (.proj 0) (Cobham.orFn (Cobham.lenLeFlag_mem (Cobham.const _) (.proj 1))
      (Cobham.notFn (cobham_dvdBits_comp (.proj 2) (cobham_comp₁ cobham_unaryToBinStr (.proj 1)))))
  have h : Cobham fun v : Fin 2 → List Bool => foldBlocks (tdStep (v 1)) [true] (v 0) :=
    (cobham_foldBlocks (n := 1) hstep (init := fun _ => [true]) (Cobham.const _) 1 fun w => by
      rw [tdStep, length_andBit]
      omega).of_eq fun v => rfl
  unfold isOddPrimeU
  exact Cobham.andFn (Cobham.lenLeFlag_mem hg (Cobham.const _))
    ((Cobham.comp₂ h (TermsStr.cobham_idxBlocks_comp hg)
      (cobham_comp₁ cobham_unaryToBinStr hg)).of_eq fun v => by simp)

/-! ### Filtering the candidates -/

/-- The odd primes below `|T|`, in unary, framed. -/
def oddPrimesStr (T : List Bool) : List Bool :=
  foldBlocks (fun acc c => caseBit₀ (isOddPrimeU c) (acc ++ delimit c) acc) []
    (TermsStr.idxBlocks T)

theorem oddPrimesStr_eq (T : ℕ) :
    oddPrimesStr (unaryN T) = frame ((oddPrimesBelow T).map unaryN) := by
  have key : ∀ (cs : List ℕ) (acc : List (List Bool)),
      (cs.map unaryN).foldl (fun acc c => caseBit₀ (isOddPrimeU c) (acc ++ delimit c) acc)
          (frame acc) =
        frame (acc ++ (cs.filter fun c => decide (3 ≤ c ∧ c.Prime)).map unaryN) := by
    intro cs
    induction cs with
    | nil => intro acc; simp
    | cons c cs ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, isOddPrimeU_eq]
      by_cases h : 3 ≤ c ∧ c.Prime
      · simp only [h, and_self, decide_true, caseBit₀_cons, Bool.cond_true]
        rw [show frame acc ++ delimit (unaryN c) = frame (acc ++ [unaryN c]) by
          rw [frame_append, SparseGcd.frame_singleton], ih,
          List.filter_cons_of_pos (by simpa using h)]
        simp
      · simp only [h, decide_false, caseBit₀_cons, Bool.cond_false]
        rw [ih, List.filter_cons_of_neg (by simpa using h)]
  rw [oddPrimesStr, TermsStr.idxBlocks_unaryN, foldBlocks_frame,
    show ([] : List Bool) = frame [] from rfl, key, List.nil_append]
  rfl

theorem cobham_oddPrimesStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => oddPrimesStr (g v) := by
  have hstep : Cobham fun w : Fin 2 → List Bool =>
      caseBit₀ (isOddPrimeU (w 1)) (w 0 ++ delimit (w 1)) (w 0) :=
    Cobham.iteFn (cobham_isOddPrimeU_comp (.proj 1))
      (Cobham.appendFn (.proj 0) (TermsStr.cobham_delimit_comp (.proj 1))) (.proj 0)
  have h : Cobham fun v : Fin 1 → List Bool =>
      foldBlocks (fun acc c => caseBit₀ (isOddPrimeU c) (acc ++ delimit c) acc) [] (v 0) :=
    (cobham_foldBlocks (n := 0) hstep (init := fun _ => []) Cobham.empty 2 fun w => by
      rcases SparseGcd.caseBit₀_cases (isOddPrimeU (w 1)) (w 0 ++ delimit (w 1)) (w 0)
        with h | h <;>
      · rw [h]
        try simp only [List.length_append, delimit_length]
        omega).of_eq fun v => rfl
  unfold oddPrimesStr
  exact (Cobham.comp h fun _ : Fin 1 => TermsStr.cobham_idxBlocks_comp hg).of_eq fun v => rfl

/-- The first `|nU|` odd primes below `|T|`. -/
def primesStr (nU T : List Bool) : List Bool := takeBlocksStr nU (oddPrimesStr T)

theorem primesStr_eq (n T : ℕ) :
    primesStr (unaryN n) (unaryN T) = frame ((firstOddPrimes T n).map unaryN) := by
  rw [primesStr, oddPrimesStr_eq, takeBlocksStr_frame, ← List.map_take]
  rfl

theorem cobham_primesStr_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) : Cobham fun v => primesStr (g₀ v) (g₁ v) := by
  unfold primesStr
  exact TermsStr.cobham_takeBlocksStr_comp h₀ (cobham_oddPrimesStr_comp h₁)

/-! ### `N = ∏ q_i` -/

/-- `N` in binary from the unary prime list. -/
def bigNStr (qs : List Bool) : List Bool := prodStr (mapBlocks unaryToBinStr qs)

theorem prodStr_frame_encNat (ℓ : List ℕ) : prodStr (frame (ℓ.map encNat)) = encNat ℓ.prod := by
  have key : ∀ (ℓ : List ℕ) (a : ℕ),
      (ℓ.map encNat).foldl (fun acc b => canonBits (mulBits acc b)) (encNat a) =
        encNat (a * ℓ.prod) := by
    intro ℓ
    induction ℓ with
    | nil => intro a; simp
    | cons q ℓ ih =>
      intro a
      rw [List.map_cons, List.foldl_cons, canonBits, decNat_mulBits, decNat_encNat, decNat_encNat,
        ih, List.prod_cons, mul_assoc]
  rw [prodStr, foldBlocks_frame, ← TermsStr.encNat_one, key, one_mul]

theorem bigNStr_eq (qs : List ℕ) : bigNStr (frame (qs.map unaryN)) = encNat qs.prod := by
  rw [bigNStr, mapBlocks_frame, List.map_map]
  have h : (unaryToBinStr ∘ unaryN) = encNat := funext unaryToBinStr_unaryN
  rw [h, prodStr_frame_encNat]

theorem cobham_bigNStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v => bigNStr (g v) := by
  unfold bigNStr
  exact cobham_comp₁ cobham_prodStr
    (TermsStr.cobham_mapBlocks_comp (F := fun b _ => unaryToBinStr b)
      (cobham_comp₁ cobham_unaryToBinStr (.proj 0)) hg)

end SparseIrred.Machine
