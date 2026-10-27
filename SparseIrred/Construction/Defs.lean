import Mathlib
import Complexitylib.SAT.ThreeSAT

/-!
# The polynomial `H_M` of Theorem 8 (notes of 28 Sep 2026, pp. 7–8)

Given a CNF `Φ` (complexitylib's `Complexity.SAT.CNF`), the notes construct

* `q_i` — the first `n` distinct odd primes, where `n` is the number of variables of `Φ`;
* `N = ∏ q_i`, `m_i = N / q_i`;
* `P⁺_i = X^{m_i} - 1` (positive literal), `P⁻_i = ∑_{r<q_i} X^{r m_i}` (negative literal);
* `C_j` — the product of the literal polynomials of clause `j` (empty product `1`);
* `S = ∑_j C_j(X) C_j(X⁻¹)` in the Laurent polynomial ring `ℤ[T;T⁻¹]`;
* `D = max {|e| : [X^e] S ≠ 0}` computed on the true (collected) support of `S`;
* `A = 3 X^D S`, `B = X^N - 1`, `H_M = A + X^M B`;
* `c = 1 - X^N`, `‖h‖ = ∑_e ([X^e] h)^2`, `m = max(deg c, deg A)`,
  `w = ‖c‖ + ‖A‖ + #supp c + #supp A`, `M = 2^{20(w+1)} (m+1)^6`.

## Variable numbering

complexitylib variables are arbitrary natural numbers (unary in the input code).  Only the variables
that actually occur are numbered: an occurring variable `v` receives index `varIdx Φ v`, the number
of occurring variables smaller than `v`.  Hence `n = numVars Φ` is the number of distinct occurring
variables, which is at most the number of literal occurrences.  Non-occurring variables never enter
the construction.

`A` is extracted from the Laurent polynomial `3 T^D S` with `LaurentPolynomial.trunc` (which keeps
the nonnegative part); the lemma `toLaurent_Apoly` (file `Construction/Laurent.lean`) proves that
nothing is lost, i.e. `toLaurent A = 3 T^D S` ("negative exponent elimination").
-/

open Polynomial LaurentPolynomial

namespace SparseIrred

open Complexity.SAT

/-! ### Variables -/

/-- Variable `v` occurs in the formula `Φ`. -/
def Occurs (Φ : CNF) (v : ℕ) : Prop := ∃ c ∈ Φ, ∃ l ∈ c, l.var = v

instance (Φ : CNF) (v : ℕ) : Decidable (Occurs Φ v) := by
  unfold Occurs; infer_instance

/-- The occurring variables of `Φ`, in increasing order. -/
def varList (Φ : CNF) : List ℕ := (List.range (Φ.maxVar + 1)).filter fun v => decide (Occurs Φ v)

/-- `n` of the notes: the number of distinct variables occurring in `Φ`. -/
def numVars (Φ : CNF) : ℕ := (varList Φ).length

/-- Index of variable `v`: the number of occurring variables smaller than `v`. -/
def varIdx (Φ : CNF) (v : ℕ) : ℕ := ((List.range v).filter fun u => decide (Occurs Φ u)).length

/-! ### Primes -/

/-- The `i`-th odd prime, `0`-indexed: `3, 5, 7, 11, …`. -/
noncomputable def oddPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i + 1)

/-- `N = ∏_{i < n} q_i`. -/
noncomputable def bigN (Φ : CNF) : ℕ := ∏ i ∈ Finset.range (numVars Φ), oddPrime i

/-- `m_i = N / q_i`. -/
noncomputable def mExp (Φ : CNF) (i : ℕ) : ℕ := bigN Φ / oddPrime i

/-! ### Literal and clause polynomials -/

/-- `P⁺_i = X^{m_i} - 1`. -/
noncomputable def posLitPoly (Φ : CNF) (i : ℕ) : ℤ[X] := X ^ mExp Φ i - 1

/-- `P⁻_i = ∑_{r=0}^{q_i - 1} X^{r m_i}`. -/
noncomputable def negLitPoly (Φ : CNF) (i : ℕ) : ℤ[X] :=
  ∑ r ∈ Finset.range (oddPrime i), X ^ (r * mExp Φ i)

/-- The polynomial attached to a literal (`sign = true` is the positive literal). -/
noncomputable def litPoly (Φ : CNF) (l : Lit) : ℤ[X] :=
  if l.sign then posLitPoly Φ (varIdx Φ l.var) else negLitPoly Φ (varIdx Φ l.var)

/-- `C_j`: the product of the literal polynomials of a clause (the empty product is `1`). -/
noncomputable def clausePoly (Φ : CNF) (c : Clause) : ℤ[X] := (c.map (litPoly Φ)).prod

/-! ### The Laurent polynomial `S` and the polynomials `A`, `B`, `H_M` -/

/-- `S = ∑_j C_j(X) C_j(X⁻¹) ∈ ℤ[T;T⁻¹]`. -/
noncomputable def Spoly (Φ : CNF) : ℤ[T;T⁻¹] :=
  (Φ.map fun c => toLaurent (clausePoly Φ c) * invert (toLaurent (clausePoly Φ c))).sum

/-- `D = max {|e| : [X^e] S ≠ 0}` over the true support of `S` (and `0` if `S = 0`). -/
noncomputable def Dexp (Φ : CNF) : ℕ := (Spoly Φ).coeff.support.sup Int.natAbs

/-- `A = 3 X^D S`, extracted as an ordinary polynomial (see `toLaurent_Apoly`). -/
noncomputable def Apoly (Φ : CNF) : ℤ[X] :=
  LaurentPolynomial.trunc ((3 : ℤ[T;T⁻¹]) * T (Dexp Φ : ℤ) * Spoly Φ)

/-- `B = X^N - 1`. -/
noncomputable def Bpoly (Φ : CNF) : ℤ[X] := X ^ bigN Φ - 1

/-- `H_M = A + X^M B`. -/
noncomputable def Hpoly (Φ : CNF) (M : ℕ) : ℤ[X] := Apoly Φ + X ^ M * Bpoly Φ

/-- Evaluation of the Laurent polynomial `S` at a unit `u` of a commutative ring. -/
noncomputable def evalS {K : Type*} [CommRing K] (Φ : CNF) (u : Kˣ) : K :=
  LaurentPolynomial.eval₂ (Int.castRingHom K) u (Spoly Φ)

/-! ### The parameters `‖·‖`, `m`, `w`, `M` -/

/-- The notes' weight `‖h‖ = ∑_e ([X^e] h)^2` (a natural number). -/
noncomputable def weight (h : ℤ[X]) : ℕ := ∑ e ∈ h.support, (h.coeff e).natAbs ^ 2

/-- The number of nonzero terms of `h`. -/
noncomputable def termCount (h : ℤ[X]) : ℕ := h.support.card

/-- `c = 1 - X^N`. -/
noncomputable def cPoly (Φ : CNF) : ℤ[X] := 1 - X ^ bigN Φ

/-- `w = ‖c‖ + ‖d‖ + t` with `d = A` and `t` the total number of nonzero terms of `c` and `d`. -/
noncomputable def wParam (Φ : CNF) : ℕ :=
  weight (cPoly Φ) + weight (Apoly Φ) + termCount (cPoly Φ) + termCount (Apoly Φ)

/-- `m = max (deg c, deg d)` with `d = A`. -/
noncomputable def mParam (Φ : CNF) : ℕ := max (cPoly Φ).natDegree (Apoly Φ).natDegree

/-- `M = 2^{20(w+1)} (m+1)^6` (equation (3) of the notes). -/
noncomputable def Mval (Φ : CNF) : ℕ := 2 ^ (20 * (wParam Φ + 1)) * (mParam Φ + 1) ^ 6

/-- The output polynomial `H_M` with `M = Mval Φ`. -/
noncomputable def Hfinal (Φ : CNF) : ℤ[X] := Hpoly Φ (Mval Φ)

end SparseIrred
