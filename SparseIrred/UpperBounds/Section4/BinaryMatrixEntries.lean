import SparseIrred.UpperBounds.Section4.BinaryAddressBasic

/-! # Actual binary entry queries for the two matrices in Theorem 18 -/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Matrix Complexity SparseDiv SparseDiv.StringArith

def sylvesterEntryStr (coeff derivCoeff : List Bool → List Bool)
    (degree derivativeDegree zero query : List Bool) : List Bool :=
  let i := pairFst query
  let j := pairSnd query
  let k := canonBits (subBits j degree)
  binaryLt j degree
    (binaryLt i j zero
      (binaryLt (addBits j derivativeDegree) i zero (derivCoeff (canonBits (subBits i j)))))
    (binaryLt i k zero
      (binaryLt (addBits k degree) i zero (coeff (canonBits (subBits i k)))))

def companionEntryStr (coeff : List Bool → List Bool)
    (mul : List Bool → List Bool → List Bool) (neg : List Bool → List Bool)
    (degree inverse zero one query : List Bool) : List Bool :=
  let i := pairFst query
  let next := canonBits (succBits (pairSnd query))
  binaryEq next degree (neg (mul (coeff i) inverse)) (binaryEq i next one zero)

theorem cobham_sylvesterEntryStr {n : ℕ}
    {coeff deriv : (Fin n → List Bool) → List Bool → List Bool}
    (hc : ∀ q, Cobham q → Cobham fun u ↦ coeff u (q u))
    (hd : ∀ q, Cobham q → Cobham fun u ↦ deriv u (q u))
    {d e z q : (Fin n → List Bool) → List Bool}
    (hdeg : Cobham d) (he : Cobham e) (hz : Cobham z) (hq : Cobham q) :
    Cobham fun u ↦ sylvesterEntryStr (coeff u) (deriv u) (d u) (e u) (z u) (q u) := by
  have hi := cobham_pairFst_comp hq
  have hj := cobham_pairSnd_comp hq
  have hk := cobham_canonBits_comp (cobham_subBits_comp hj hdeg)
  exact cobham_binaryLt hj hdeg
    (cobham_binaryLt hi hj hz (cobham_binaryLt (cobham_addBits_comp hj he) hi hz
      (hd _ (cobham_canonBits_comp (cobham_subBits_comp hi hj)))))
    (cobham_binaryLt hi hk hz (cobham_binaryLt (cobham_addBits_comp hk hdeg) hi hz
      (hc _ (cobham_canonBits_comp (cobham_subBits_comp hi hk)))))

theorem cobham_companionEntryStr {n : ℕ}
    {coeff neg : (Fin n → List Bool) → List Bool → List Bool}
    {mul : (Fin n → List Bool) → List Bool → List Bool → List Bool}
    (hc : ∀ q, Cobham q → Cobham fun u ↦ coeff u (q u))
    (hm : ∀ a b, Cobham a → Cobham b → Cobham fun u ↦ mul u (a u) (b u))
    (hn : ∀ a, Cobham a → Cobham fun u ↦ neg u (a u))
    {d inv z o q : (Fin n → List Bool) → List Bool}
    (hd : Cobham d) (hi : Cobham inv) (hz : Cobham z) (ho : Cobham o) (hq : Cobham q) :
    Cobham fun u ↦ companionEntryStr (coeff u) (mul u) (neg u)
      (d u) (inv u) (z u) (o u) (q u) := by
  have hj := cobham_canonBits_comp (cobham_succBits_comp (cobham_pairSnd_comp hq))
  exact cobham_binaryEq hj hd
    (hn _ (hm _ _ (hc _ (cobham_pairFst_comp hq)) hi))
    (cobham_binaryEq (cobham_pairFst_comp hq) hj ho hz)

theorem sylvesterEntryStr_correct {K : Type*} [Field K] (f : K[X]) (enc : K → List Bool)
    (coeff deriv : List Bool → List Bool)
    (hc : ∀ i, coeff (encNat i) = enc (f.coeff i))
    (hd : ∀ i, deriv (encNat i) = enc (f.derivative.coeff i)) (i j : ℕ) :
    sylvesterEntryStr coeff deriv (encNat f.natDegree) (encNat f.derivative.natDegree)
      (enc 0) (pair (encNat i) (encNat j)) = enc (coefficientSylvesterEntry f i j) := by
  have hsub (a b : ℕ) : canonBits (subBits (encNat a) (encNat b)) = encNat (a - b) := by
    rw [canonBits, decNat_subBits, decNat_encNat, decNat_encNat]
  simp only [sylvesterEntryStr, pairFst_pair, pairSnd_pair, binaryLt,
    decNat_encNat, decNat_addBits, hsub, hc, hd, coefficientSylvesterEntry]
  by_cases hji : j < f.natDegree
  · by_cases hij : i < j
    · have hle : ¬j ≤ i := by omega
      simp [hji, hij, hle]
    · by_cases hei : j + f.derivative.natDegree < i
      · have hle : ¬i ≤ j + f.derivative.natDegree := by omega
        simp [hji, hij, hei, hle]
      · simp [hji, hij, hei, show j ≤ i by omega,
          show i ≤ j + f.derivative.natDegree by omega, coeff_derivative]
  · by_cases hij : i < j - f.natDegree
    · have hle : ¬j - f.natDegree ≤ i := by omega
      simp [hji, hij, hle]
    · by_cases hei : j - f.natDegree + f.natDegree < i
      · have hle : ¬i ≤ j - f.natDegree + f.natDegree := by omega
        simp [hji, hij, hei, hle]
      · simp [hji, hij, hei, show j - f.natDegree ≤ i by omega,
          show i ≤ j - f.natDegree + f.natDegree by omega]

theorem companionEntryStr_correct {K : Type*} [Field K] (f : K[X]) (enc : K → List Bool)
    (coeff : List Bool → List Bool) (mul : List Bool → List Bool → List Bool)
    (neg : List Bool → List Bool)
    (hc : ∀ i, coeff (encNat i) = enc (f.coeff i))
    (hm : ∀ a b, mul (enc a) (enc b) = enc (a * b))
    (hn : ∀ a, neg (enc a) = enc (-a)) (i j : Fin f.natDegree) :
    companionEntryStr coeff mul neg (encNat f.natDegree) (enc f.leadingCoeff⁻¹)
      (enc 0) (enc 1) (pair (encNat i.val) (encNat j.val)) = enc (coefficientCompanion f i j) := by
  have hs : canonBits (succBits (encNat j.val)) = encNat (j.val + 1) := by
    rw [canonBits, decNat_succBits, decNat_encNat]
  simp only [companionEntryStr, pairFst_pair, pairSnd_pair, hs, binaryEq,
    decNat_encNat, hc, hm, hn, coefficientCompanion]
  split_ifs <;> rfl

end SparseIrred.UpperBounds.Section4
