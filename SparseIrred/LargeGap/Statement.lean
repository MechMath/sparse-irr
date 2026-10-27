import SparseIrred.Construction.Defs

/-!
# The large-gap theorem of Sawin–Shusterman–Stoll, as an explicit statement

W. Sawin, M. Shusterman, M. Stoll, *Irreducibility of polynomials with a large gap*
(arXiv:1803.10811, Acta Arith. 192 (2020)).  For `c, d ∈ ℤ[x]` put
`f_L(x) = x^L c(x⁻¹) + d(x)`.  The notes (p. 7–8) use the combination of

* Theorem 1.2 (Schinzel): under `c(0) d(0) ≠ 0`, `gcd_{ℤ[x]}(c̃, d) = 1`, `c ≠ ±d` and
  "(c, d) not Capellian", the non-reciprocal part of `f_L` is irreducible for `L > N₀`;
* Theorem 1.5 (Filaseta–Ford–Konyagin): one may take
  `N₀ ≤ N_FFK = deg c + 2 max {5^{4w-15}, max(deg c, deg d) (5^{2w-8} + 1/4)}` with
  `w = ‖c‖ + ‖d‖ + t`, `t` the total number of nonzero terms of `c` and `d`;
* Corollary 1.3: if `L > max {N₀, N₁}` the non-cyclotomic part of `f_L` is irreducible, where
  `N₁ = deg c + deg d + (2m / log θ) log W` if `m ≤ 27` and
  `N₁ = deg c + deg d + m (log 6m)^3 log W` otherwise, `m = max(deg c, deg d)`,
  `W = ‖c‖ + ‖d‖`, `θ ≈ 1.17628` Lehmer's constant (the unique real root `> 1` of Lehmer's
  polynomial).

`SSSLargeGap` below is this combined statement.  It is not proved here and is never assumed as an
axiom: theorems depending on it take it as an explicit hypothesis.  For the specific polynomials of
Theorem 8 the needed irreducibility is proved unconditionally by a different route in
`SparseIrred/FFK`.

Conventions (following the SSS paper):

* `‖h‖ = ∑_e ([x^e] h)^2` (`weight`), "irreducible" means irreducible over `ℚ`;
* `c̃ = x^{deg c} c(x⁻¹)` is `Polynomial.reverse`;
* `gcd_{ℤ[x]}(c̃, d) = 1` is `IsRelPrime c.reverse d` in `ℤ[X]` (every common divisor is a unit);
* `(c, d)` is *Capellian* when `-d(x)/c(x⁻¹)` is a `p`-th power in `ℚ(x)` for some prime `p`, or
  `d(x)/c(x⁻¹)` is `4` times a fourth power in `ℚ(x)` (SSS Definition 1.1);
* the *non-cyclotomic part* of `f` is `f` divided by all its irreducible factors that are cyclotomic
  polynomials; `NoncyclotomicPartIrreducible f` says: whenever `f = (∏ Φ_n) · g` with `g` free of
  cyclotomic factors, `g` is irreducible in `ℚ[X]`;
* `x^L c(x⁻¹) = x^{L - deg c} c̃(x)` for `L ≥ deg c` (and the bound forces `L > deg c`).
-/

open Polynomial

namespace SparseIrred

/-- `c(X⁻¹)` as an element of `ℚ(X)`. -/
noncomputable def invSubst (c : ℤ[X]) : RatFunc ℚ :=
  (c.map (Int.castRingHom ℚ)).eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X⁻¹)

/-- `d(X)` as an element of `ℚ(X)`. -/
noncomputable def toRatFunc (d : ℤ[X]) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (d.map (Int.castRingHom ℚ))

/-- SSS Definition 1.1: `(c, d)` is Capellian. -/
def Capellian (c d : ℤ[X]) : Prop :=
  (∃ p : ℕ, p.Prime ∧ ∃ r : RatFunc ℚ, -(toRatFunc d / invSubst c) = r ^ p) ∨
    ∃ r : RatFunc ℚ, toRatFunc d / invSubst c = 4 * r ^ 4

/-- The non-cyclotomic part of `f` is irreducible over `ℚ`. -/
def NoncyclotomicPartIrreducible (f : ℤ[X]) : Prop :=
  ∀ (s : Multiset ℕ) (g : ℚ[X]), (∀ n ∈ s, 0 < n) →
    f.map (Int.castRingHom ℚ) = (s.map fun n => cyclotomic n ℚ).prod * g →
    (∀ n : ℕ, 0 < n → ¬cyclotomic n ℚ ∣ g) → Irreducible g

/-- Lehmer's polynomial `x^10 + x^9 - x^7 - x^6 - x^5 - x^4 - x^3 + x + 1`. -/
noncomputable def lehmerPoly : ℤ[X] :=
  X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

/-- SSS Theorem 1.5: `N_FFK = deg c + 2 max {5^{4w-15}, max(deg c, deg d) (5^{2w-8} + 1/4)}`. -/
noncomputable def ffkBound (c d : ℤ[X]) : ℝ :=
  let w : ℤ := weight c + weight d + termCount c + termCount d
  (c.natDegree : ℝ) + 2 * max ((5 : ℝ) ^ (4 * w - 15))
    ((max c.natDegree d.natDegree : ℕ) * ((5 : ℝ) ^ (2 * w - 8) + 1 / 4))

/-- SSS Corollary 1.3: the bound `N₁` (natural logarithms). -/
noncomputable def sssN1 (θ : ℝ) (c d : ℤ[X]) : ℝ :=
  let m : ℕ := max c.natDegree d.natDegree
  let W : ℝ := weight c + weight d
  (c.natDegree : ℝ) + d.natDegree +
    if m ≤ 27 then 2 * m / Real.log θ * Real.log W
    else m * Real.log (6 * m) ^ 3 * Real.log W

/-- Theorems 1.2 + 1.5 and Corollary 1.3 of Sawin–Shusterman–Stoll, as used in the notes.
The Lehmer constant is quantified as "any real root `θ > 1` of Lehmer's polynomial"; such a root is
unique (`lehmerPoly_root_unique`), so this is exactly the published statement. -/
def SSSLargeGap : Prop :=
  ∀ (c d : ℤ[X]) (L : ℕ) (θ : ℝ), 1 < θ → aeval θ lehmerPoly = 0 →
    c.coeff 0 ≠ 0 → d.coeff 0 ≠ 0 → IsRelPrime c.reverse d → c ≠ d → c ≠ -d →
    ¬Capellian c d → max (ffkBound c d) (sssN1 θ c d) < L →
    NoncyclotomicPartIrreducible (X ^ (L - c.natDegree) * c.reverse + d)

end SparseIrred
