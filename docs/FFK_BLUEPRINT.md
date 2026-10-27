# Blueprint: irreducibility of `H_M` via Filaseta–Ford–Konyagin + Ljunggren (no large-gap hypothesis)

Goal: the frozen theorem `Hfinal_irreducible_of_unsat` (`SparseIrred/FFK/Main.lean`):
for an unsatisfiable CNF `Φ`, `Irreducible (Hfinal Φ)` in `ℤ[X]`.

**Status: proved.** `Hfinal_irreducible_of_unsat` (`FFK/Main.lean`) is proved by
`FFK.irreducible_Hfinal`; `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`
(see `docs/AXIOMS.txt`).

| File | Content |
|---|---|
| `SparseIrred/FFK/Dirichlet.lean` | FFK Lemma 3 (box principle; modulus `κ`) |
| `SparseIrred/FFK/Lift.lean` | `κ`-lift `ℤ[x] → ℤ[x][y]`, specialization, no-carry identity, blocks |
| `SparseIrred/FFK/Eisenstein.lean` | Eisenstein at `(x - 1) ⊂ ℤ[x]` for `a y^ℓ + b` |
| `SparseIrred/FFK/Ljunggren.lean` | weights, `mirror F`, `IsRelPrime F F̃`, Ljunggren condition, threshold, assembly |

All declarations live in the namespace `SparseIrred.FFK`.

---

## 0. Setting and notation

- `F = gapPoly A N M := A + X^M (X^N - 1)`, with:
  - `A.reverse = A` (palindromic);
  - `A(0) ≠ 0`;
  - `D := deg A < M` (for `A = Apoly Φ`, `D = 2·Dexp Φ`);
  - `N > 0`.
- Write `B = X^N - 1`, `L = M + N`, and `F̃ = mirror F`.
- `weight p = ∑ coeff²` (as in `Defs.lean`); `termCount p = #supp p`.
- In `ℤ[X][X]` the **outer** variable plays the role of `y`, and `C X` is `x`.
- The "3 divides every coefficient of `A`" hypothesis is **not** used here. It is used only in the
  norm argument of `Construction/Norm.lean` (the bound `2/3`), which provides "no root-of-unity
  roots".

**Top-level structure.** `Polynomial.irreducible_of_mirror` (Ljunggren's method, in mathlib) needs
three inputs:

- (a) `¬IsUnit F`;
- (b) the **Ljunggren condition**: `∀ k, F·F̃ = k·k̃ → k ∈ {F, -F, F̃, -F̃}`;
- (c) `IsRelPrime F F̃`.

(c) comes from the palindromic identity and the absence of root-of-unity roots. (b) is FFK with
Eisenstein in place of Capelli.

---

## 1. `Dirichlet.lean` — FFK Lemma 3 with crude constants

FFK's own lemma uses 5 boxes per coordinate and needs `a_r ≥ max{2·5^{2r-1}, k₀(5^{r-1}+1/4)}`.
We use 8 boxes per coordinate and the simpler choice `κ = ⌊a/d⌋`. The price is `64^{|S|}` in
place of `≈ 25^{|S|}`, which `M = 2^{20(w+1)}(m+1)^6` easily absorbs (§5.4).

**D1 `exists_simultaneous_approx`** (proved, ~25 lines + the private helper `approx_of_same_box`, ~30 lines).
- *Statement:* `S : Finset ℕ`, `0 < a` ⟹ `∃ d, 1 ≤ d ≤ 8^{|S|} ∧ ∀ t ∈ S, ∃ c : ℤ, 8·|d·t − c·a| < a`.
- *Proof:*
  1. For `i = 0, …, 8^{|S|}`, put `i` in the box `(⌊8·((i·t) mod a)/a⌋)_{t∈S} ∈ (S → Fin 8)`. There are `8^{|S|}` boxes, so two indices `i < j` share a box.
  2. Take `d = j − i` and `c = ⌊jt/a⌋ − ⌊it/a⌋`.
  3. Then `d t − c a = (jt mod a) − (it mod a)`.
  4. Both residues lie in the same interval `[qa/8, (q+1)a/8)`, so `8·|d t − c a| < a`.

**D2 `exists_nearMultiple_modulus`** (proved, ~60 lines).
- *Statement:* `S ⊆ [0, a]` and `(10 + κ₀)·64^{|S|} ≤ a` ⟹ `∃ κ, 0 < κ ∧ κ₀ ≤ κ ≤ a ∧ ∀ t ∈ S, ∃ c : ℤ, 4·|t − cκ| < κ`.
- *Proof:*
  1. Take `d, c_t` from D1, and let `δ_t = d t − c_t a`, so `8|δ_t| < a`.
  2. Set `κ = ⌊a/d⌋` and `ρ = a mod d < d`.
  3. **`0 ≤ c_t ≤ d`:** from `c_t a = d t − δ_t` with `0 ≤ t ≤ a` and `|δ_t| < a/8`.
  4. **Key identity:** `d·(t − c_t κ) = δ_t + c_t ρ`, using `a = dκ + ρ`.
  5. `8 d² ≤ a`, since `d ≤ 8^{|S|}`, so `8d² ≤ 8·64^{|S|} ≤ a`.
  6. Upper bound: `4(δ + cρ) < a/2 + 4d(d − 1) ≤ a − d < dκ`.
  7. Lower bound: `4(δ + cρ) > −a/2 ≥ ρ − a = −dκ`, using `2ρ < 2d ≤ a`.
  8. Divide by `d > 0`.
  9. `κ₀ ≤ κ` because `κ₀ d ≤ κ₀ 8^{|S|} ≤ a`. `κ ≥ 1` because `d ≤ a`.

**D3 `two_mul_add_div_four_mod_lt`** (proved, ~20 lines).
- *Statement:* `0 < κ`, `4|t − cκ| < κ` ⟹ `2·((t + ⌊κ/4⌋) mod κ) < κ`.
- *Proof:*
  1. Let `s = t − cκ`, so `−κ < 4s < κ`, and let `q = ⌊κ/4⌋`, so `4q ≤ κ < 4q + 4`.
  2. Then `r := s + q` satisfies `0 ≤ r < κ` (integrality gives `−s ≤ q`) and `2r < κ`.
  3. Since `t + q = r + cκ`, we get `(t + q) mod κ = r`. The proof works in `ℤ` via `Int.natCast_mod` and `Int.emod_eq_of_lt`.
  4. This is FFK's "`d_j mod k ∈ [0, k/4) ∪ (3k/4, k)` ⟹ `d̄_j < k/2`".

**D4 `exists_lift_modulus`** (proved, D2 + D3).
- *Statement:* same hypotheses as D2 ⟹ `∃ κ, 0 < κ ∧ κ₀ ≤ κ ≤ a ∧ ∀ t ∈ S, 2·((t + κ/4) mod κ) < κ`.

---

## 2. `Lift.lean` — the `κ`-lift and the no-carry identity

**Definitions.**
- `kLift κ h f := ∑_e f_e · x^{(e+h) mod κ} · y^{(e+h) div κ}`.
- `LiftGood κ h f := ∀ e ∈ supp f, 2·((e+h) mod κ) < κ`.
- `XDegLE α P := ∀ j, natDegree (P.coeff j) ≤ α`.

**Lemmas:**

- **L1 `kLift_monomial`, `kLift_zero`, `kLift_add`, `kLift_neg`, `kLift_sub`, `kLift_sum`** (proved). `kLift κ h` is additive; `kLiftHom` packages it as an `AddMonoidHom`.
- **L2 `eval_kLift`** (proved): `(kLift κ h f)(x, x^κ) = x^h f`. By induction on `f`, using `(e+h) mod κ + κ·((e+h) div κ) = e + h`.
- **L3 `XDegLE.mul`** (proved): `XDegLE α P → XDegLE β Q → XDegLE (α+β) (P Q)`.
- **L4 `xDegLE_kLift`** (proved): `LiftGood κ h f → XDegLE ((κ−1)/2) (kLift κ h f)`.
- **L5 `coeff_eval_X_pow`** (proved, the no-carry core).
  - *Statement:* for `XDegLE α P`, `α < κ` and `i < κ`: `[x^{κj+i}] P(x, x^κ) = [x^i y^j] P`.
  - *Proof:* in `∑_{j'} P_{j'} x^{κ j'}`, a term with `j' < j` would need exponent `κ(j−j') + i ≥ κ > α` (zero); a term with `j' > j` starts above `κj + i`.
- **L6 `eq_of_eval_X_pow_eq`** (proved): specialization `y ↦ x^κ` is injective on `XDegLE α` for `α < κ`.
- **L7 `kLift_mul_eq_of_mul_eq`** (proved; FFK (9)).
  - *Statement:* `0 < κ`, all four of `f₁, f₂, g₁, g₂` are `LiftGood κ h`, and `f₁f₂ = g₁g₂` ⟹ `kLift f₁ · kLift f₂ = kLift g₁ · kLift g₂`.
  - *Proof:* both sides specialize to `x^{2h} f₁f₂`. Both are `XDegLE (2⌊(κ−1)/2⌋)` and `2⌊(κ−1)/2⌋ < κ`. Apply L6.
- **L8 `add_div_eq_of_two_mul_mod_lt`** (proved; FFK's same-block argument).
  - *Statement:* `s ≤ t`, `2(t − s) ≤ κ`, `2((s+h) mod κ) < κ` ⟹ `⌊(t+h)/κ⌋ = ⌊(s+h)/κ⌋`.
  - *Proof:* if the quotients differed, then `t − s ≥ κ − ((s+h) mod κ) > κ/2`.
  - *Note:* only the lower endpoint needs the lifting condition.
- **L9 `kLift_X_pow_mul`** (proved).
  - *Statement:* if `∀ e ≤ deg g, ⌊(s+e+h)/κ⌋ = ℓ`, then `kLift κ h (X^s g) = C(X^{s+h−κℓ} g) · y^ℓ`.
  - *Proof:* expand `g` monomially (`as_sum_range_C_mul_X_pow`). Then `(s+e+h) mod κ = (s+h−κℓ) + e`, with `κℓ ≤ s+h` from `e = 0`.
- **L10 `kLift_two_block`** (proved): under the two block hypotheses (low block `u` with y-degree `0`, high block `X^s v` with y-degree `ℓ`), `kLift κ h (X^s v + u) = C(X^{s+h−κℓ} v) y^ℓ + C(X^h u)`.
- **L11 `dvd_of_kLift_dvd`** (proved; specialization of divisibility).
  - *Statement:* `f(0) ≠ 0`, `kLift f = C(x^m)·P` and `P ∣ kLift g` ⟹ `f ∣ g`.
  - *Proof:*
    1. Apply `evalRingHom (x^κ)`: `x^h f = x^m P(x,x^κ)`, which divides `x^m x^h g`.
    2. Cancel `x^h`.
    3. Use `IsRelPrime f (x^m)`, which holds because `x` is irreducible and `x ∤ f`.

---

## 3. `Eisenstein.lean` — Eisenstein at `(x − 1)` instead of Capelli

- **E1 `irreducible_C_mul_X_pow_add_C`** (proved, ~50 lines).
  - *Statement:* `ℓ > 0`, `a(1) ≠ 0`, `b = (x−1)·b₁`, `b₁(1) ≠ 0` and `IsRelPrime a b` in `ℤ[x]` ⟹ `a·y^ℓ + b` is irreducible in `ℤ[x][y]`.
  - *Proof:* `Polynomial.irreducible_of_eisenstein_criterion` with `P = span{x − 1}`:
    - `P` is prime, by `prime_X_sub_C` and `Ideal.span_singleton_prime`;
    - membership in `P` is "vanishes at 1";
    - leading coefficient `a ∉ P`;
    - the middle coefficients are `0`;
    - `b ∈ P`;
    - `b ∉ P² = span{(x−1)²}`: cancel `x − 1` to get `(x−1) ∣ b₁`, which contradicts `b₁(1) ≠ 0`;
    - primitivity: `C r ∣ f` gives `r ∣ a` and `r ∣ b`, so `IsRelPrime` applies.
- **E2 `eval_one_ne_zero_of_isRelPrime`** (proved): `IsRelPrime A (X^N − 1) → A(1) ≠ 0`, since `x − 1` would divide both.
- **E3 `isRelPrime_X_pow_mul`** (proved): `IsRelPrime A B`, `A(0), B(0) ≠ 0`, `i = 0 ∨ j = 0` ⟹ `IsRelPrime (x^i A) (x^j B)`.
- **E4 `X_pow_sub_one_eq_mul_geom`** (proved): `X^N − 1 = (X − 1)·∑_{k<N} X^k`.
- **E5 `irreducible_gapLift`** (proved).
  - *Statement:* `N > 0`, `ℓ > 0`, `A(0) ≠ 0`, `IsRelPrime A (X^N − 1)` and `i = 0 ∨ j = 0` ⟹ `C(x^i A)·y^ℓ + C(x^j·(−(x^N − 1)))` is irreducible.
  - *Proof:* E1 with `b₁ = −x^j ∑_{k<N} x^k`, so `b₁(1) = −N ≠ 0`, together with E2, E3 and `IsRelPrime.neg_right`.

Why the lift of `F̃` and not of `F`: the lift of `F` is `x^h A + x^β B y^ℓ`, which is Eisenstein
only after reversing in `y` (its leading coefficient `x^β B` lies in `P`). The lift of `F̃` is
`x^β A y^ℓ − x^h B`, which is Eisenstein directly. Only one irreducible lift is needed (§4, K3).

---

## 4. `Ljunggren.lean`

### 4.1 Weights

All of these are proved:

- `weight_eq_sum_sq`: `(weight p : ℤ) = p.sum (· ^ 2)`.
- `weight_eq_sum_of_support_subset`.
- `termCount_le_weight`: each nonzero integer has `|a| ≥ 1`.
- `weight_pos`.
- `weight_C_mul`: `weight (C c · p) = |c|²·weight p`.
- `weight_neg`.
- `weight_mirror`: via `coeff_mul_mirror` applied to `p.mirror` together with `mirror_mirror`.
- `termCount_mirror`: the support of the mirror is the image of `supp p` under `revAt`.
- `weight_add_of_disjoint`.
- `weight_X_pow`.

### 4.2 Consequences of `f f̃ = k k̃`

All proved, from `natDegree_mul_mirror`, `natTrailingDegree_mul_mirror` and `coeff_mul_mirror`
(the middle coefficient):

- `natDegree_eq_of_mul_mirror_eq`;
- `natTrailingDegree_eq_of_mul_mirror_eq`;
- `weight_eq_of_mul_mirror_eq`.

**`eq_or_eq_neg_of_dvd`** (proved).
- *Statement:* `f ∣ g`, `g ≠ 0`, `deg g ≤ deg f` and `weight g = weight f` ⟹ `g = ±f`.
- *Proof:* `g = f·q` with `deg q = 0`, so `q = C c`. Then `|c|²·w = w` with `w > 0`, so `c = ±1`.

### 4.3 The gap polynomial

All proved:

- `natDegree_gapPoly` (`= M + N`) and `monic_gapPoly`.
- `coeff_zero_gapPoly` and `natTrailingDegree_gapPoly` (`= 0`).
- **`mirror_gapPoly`**: `F̃ = X^{L−D}·A − (X^N − 1)`.
  - `mirror = reverse = reflect L`.
  - `reflect L A = X^{L−D}·reflect D A = X^{L−D}·A`, by `reflect_mul` with `1` and palindromy.
  - `reflect L (X^M B) = reflect M X^M · reflect N B = 1 − X^N`.
- `coeff_zero_mirror_gapPoly`: `F̃(0) = lead F = 1`.
- **`palindromic_identity`**: `X^{L−D}·F − F̃ = (X^N − 1)(X^{2M+N−D} + 1)`, a ring identity once `2M+N−D = (L−D) + M`.
- `weight_gapPoly`: `weight F = weight A + 2`. The supports `supp A ⊆ [0, D]` and `supp(X^M B) ⊆ [M, ∞)` are disjoint, and `X^M B = X^{L} − X^M`.
- `termCount_gapPoly_le`: `termCount F ≤ termCount A + 2`.

### 4.4 `IsRelPrime F F̃` — `isRelPrime_gapPoly_mirror` (proved, ~35 lines)

Hypothesis: `∀ z ∈ ℂ` that is a root of unity, `F(z) ≠ 0`. Let `g` be a common divisor of `F` and `F̃`.

- If `deg g = 0`, then `g = C c` and `c ∣ lead F = 1`, so `g` is a unit.
- Otherwise `g` has a complex root `z` (`Complex.exists_root`), so `F(z) = F̃(z) = 0`.
  - Evaluating the palindromic identity gives `(z^N − 1)(z^E + 1) = 0`, with `E = 2M+N−D > 0`.
  - So `z^N = 1`, or `z^{2E} = 1`. Either way `z` is a root of unity with `F(z) = 0`, a contradiction.

### 4.5 The FFK core

**`FFKThreshold A N M`** `:= (10 + 2·max(N, D))·64^{2(weight A + termCount A)+8} ≤ M`.
- `natDegree_lt_of_FFKThreshold` gives `D < M`.

**K1 `exists_modulus_gapPoly`** (proved, ~45 lines).
- *Statement:* `N > 0`, the threshold, and `F F̃ = k k̃` ⟹ `∃ κ, 0 < κ ∧ 2·max(N, D) ≤ κ ∧ κ ≤ L`, with `F, F̃, k, k̃` all `LiftGood κ ⌊κ/4⌋`.
- *Proof:*
  1. Let `S = supp F ∪ supp F̃ ∪ supp k ∪ supp k̃`. It lies in `[0, L]`, because all four have degree `L` (4.2).
  2. `|S| ≤ 2·termCount F + 2·termCount k` (by `termCount_mirror`).
  3. `termCount F ≤ termCount A + 2`, and `termCount k ≤ weight k = weight F = weight A + 2`.
  4. Hence `|S| ≤ 2(weight A + termCount A) + 8`.
  5. Apply D4 with `a = L` and `κ₀ = 2·max(N, D)`.
  6. This is FFK's set `T` (their `|T| ≤ 2‖F‖² + 2r − 5`); we do not need their sharper count.

**K2 `kLift_mirror_gapPoly`** (proved, ~30 lines).
- *Statement:* the hypotheses on `A, N, M`, together with `0 < κ`, `2·max(N, D) ≤ κ ≤ L` and `LiftGood κ h F̃` (`h = ⌊κ/4⌋`) ⟹ `∃ ℓ β, ℓ > 0 ∧ kLift κ h F̃ = C(x^β A)·y^ℓ + C(x^h·(−(x^N − 1)))`.
- *Proof:*
  1. Write `F̃ = X^s A + (−B)` with `s = L − D`.
  2. **Low block:** for `e ≤ N`, `e + h ≤ N + κ/4 < κ` (since `2N ≤ κ`), so its y-degree is `0`.
  3. **High block, ends in the support:** `s ∈ supp F̃`, because its coefficient is `A(0)`: `s > N` since `M > D`, so `B` contributes nothing there. `L ∈ supp F̃` too.
  4. **Same y-degree:** `2(L − s) = 2D ≤ κ`, so L8 gives `⌊(L+h)/κ⌋ = ⌊(s+h)/κ⌋ =: ℓ`. Monotonicity then gives the same `ℓ` for every `s + e`, `e ≤ D`.
  5. `ℓ ≥ 1` because `κ ≤ L`.
  6. Apply L10, with `β = s + h − κℓ`.
- *Compared with FFK:* they use `κ < 4L/3`; we have `κ ≤ L`, which is simpler.

**K3 `ljunggren_of_modulus`** (proved, ~55 lines).
- *Statement:* the hypotheses, `IsRelPrime A (X^N − 1)`, `F F̃ = k k̃`, and `κ` as produced by K1 ⟹ `k ∈ {F, −F, F̃, −F̃}`.
- *Proof:*
  1. **Product identity:** L7 gives `G₁G₂ = H₁H₂`, where `G₁ = kLift F`, `G₂ = kLift F̃`, `H₁ = kLift k`, `H₂ = kLift k̃`.
  2. **Split off the `x`-power:** K2 gives `G₂ = C(x^m)·G`, with `m = min(β, h)` and `G = C(x^{β−m}A)·y^ℓ + C(x^{h−m}·(−B))`. One of the two exponents `β − m`, `h − m` is `0`.
  3. **`G` is prime:** E5 makes `G` irreducible. `ℤ[X][X]` is a UFD, so `G` is prime.
  4. **`G` divides a lift of `k` or `k̃`:** `G ∣ G₂ ∣ G₁G₂ = H₁H₂`, so `G ∣ H₁` or `G ∣ H₂`.
  5. **Specialize:** L11, with `F̃(0) = 1 ≠ 0`, gives `F̃ ∣ k` or `F̃ ∣ k̃`.
  6. **Same degree and weight:** `deg k = deg k̃ = deg F̃ = L` and `weight k = weight k̃ = weight F = weight F̃`. By `eq_or_eq_neg_of_dvd`, `k = ±F̃`, or `k̃ = ±F̃`.
  7. In the second case, `k = mirror k̃ = ±F` (`mirror_mirror`, `mirror_neg`).

**K4 `ljunggren_gapPoly`** (proved): K1 + K3 give the Ljunggren condition above the threshold.

**K5 `irreducible_gapPoly`** (proved).
- *Statement:* `A` palindromic, `A(0) ≠ 0`, `N > 0`, `IsRelPrime A (X^N − 1)`, the threshold, and no root-of-unity roots ⟹ `Irreducible F`.
- *Proof:* `irreducible_of_mirror` with (a) positive degree, (b) K4, (c) 4.4.

### 4.6 Specialization to Theorem 8 (all proved)

- `Hfinal_eq_gapPoly`: `Hfinal Φ = gapPoly (Apoly Φ) (bigN Φ) (Mval Φ)`, by unfolding. Plain `rfl` times out on `Mval`.
- `weight_cPoly = 2` and `termCount_cPoly = 2`: `cPoly = 1 − X^N`, by `support_binomial`.
- `wParam_eq`: `wParam Φ = weight A + termCount A + 4`.
- `mParam_eq`: `mParam Φ = max(N, deg A)`, by `natDegree_cPoly`.
- **`threshold_arith`**: `(10 + 2m)·64^{2w} ≤ 2^{20(w+1)}(m+1)^6`. Here `64^{2w} = 2^{12w}` and `10 + 2m ≤ 2^{20}(m+1) ≤ 2^{8w}·2^{20}·(m+1)^6`.
- **`FFKThreshold_Mval`**: since `2(weight A + termCount A) + 8 = 2·wParam Φ`, the threshold for `Mval Φ` is exactly `threshold_arith`.
- `isRelPrime_Apoly_Bpoly`: from `isRelPrime_reverse_cPoly_Apoly` and `reverse_cPoly`.
- **`irreducible_Hfinal (Φ) (hΦ : Φ ≠ []) (hunsat : ¬Φ.Satisfiable) : Irreducible (Hfinal Φ)`**: K5 with `reverse_Apoly`, `Apoly_coeff_zero_ne_zero`, `bigN_pos`, `isRelPrime_Apoly_Bpoly`, `FFKThreshold_Mval`. The no-root-of-unity hypothesis comes from `satisfiable_of_rootOfUnity_root` and `hunsat`.

---

## 5. Index bookkeeping (summary of every bound)

Throughout: `L = M + N`, `D = deg A`, `h = ⌊κ/4⌋`, `w_A = weight A`, `t_A = termCount A`.

1. **The set `S`.** `S` is the union of the supports of `F, F̃, k, k̃`. It lies in `[0, L]` and `|S| ≤ 2(w_A + t_A) + 8`.
2. **The box principle.**
   - `1 ≤ d ≤ 8^{|S|}` and `8|dt − c_t L| < L`.
   - `κ = ⌊L/d⌋` and `ρ = L mod d`.
   - `0 ≤ c_t ≤ d` and `d(t − c_tκ) = δ_t + c_tρ`.
   - `4|t − c_tκ| < κ` needs `8d² ≤ L`; `κ ≥ κ₀` needs `κ₀d ≤ L`.
   - Both follow from `(10 + κ₀)·64^{|S|} ≤ L`.
3. **Near a multiple ⟹ small shifted residue.** `4|t − cκ| < κ` ⟹ `(t + h) mod κ = t − cκ + h ∈ [0, κ/2)`.
4. **Exponents of the lifts and their products.**
   - Every `x`-exponent of a lift is `≤ ⌊(κ−1)/2⌋`.
   - Products have `x`-exponents `≤ 2⌊(κ−1)/2⌋ ≤ κ − 1`: no carries.
5. **Blocks and `y`-degrees.**
   - Low block of `F̃` (exponents `0..N`): `N + h < κ` because `2N ≤ κ`; `y`-degree `0`.
   - High block of `F̃` (exponents `L−D..L`): width `D`, and `2D ≤ κ`.
   - Its `y`-degree is `ℓ = ⌊(L+h)/κ⌋ ≥ 1` because `κ ≤ L`.
   - Its `x`-offset is `β = L − D + h − κℓ`.
6. **Removing the `x`-power.** `m = min(β, h)`, so one of `β − m`, `h − m` is `0`. This is FFK's "`x^{−m}G` with `m` maximal".
7. **Specialization.**
   - `G₂(x, x^κ) = x^h F̃`, so `G(x, x^κ) = x^{h−m} F̃`.
   - A divisor relation `G ∣ H_i` becomes `F̃ ∣ x^m·(k or k̃)`, hence `F̃ ∣ k or k̃`, because `F̃(0) = 1`.
8. **Final numbers for `Φ`.**
   - `w = wParam = w_A + t_A + 4`, `m = mParam = max(N, D)`.
   - The requirement `(10 + 2m)·64^{2w} ≤ 2^{20(w+1)}(m+1)^6` holds for all `w, m`. The exponent slack is `2^{8w+20}` against `2^{12w}`.

## 6. Upstream black boxes (frozen statements)

| Lemma | File |
|---|---|
| `reverse_Apoly`, `Apoly_coeff_zero_ne_zero`, `bigN_pos` | `Construction/Laurent.lean` |
| `satisfiable_of_rootOfUnity_root` | `Construction/Norm.lean` |
| `reverse_cPoly`, `natDegree_cPoly`, `isRelPrime_reverse_cPoly_Apoly` | `LargeGap/Verify.lean` |

`Ljunggren.lean` imports `SparseIrred.LargeGap.Verify`, which imports `Construction.Norm`.

## 7. Numerical sanity checks performed (Python, `scratchpad/ffk/*.py`)

- **Dirichlet lemma.** The 8-box pigeonhole with `κ = ⌊a/d⌋` was checked on 3000 random sets with `a ≥ (10 + κ₀)·64^{|S|}`. In every case: `c_t ∈ [0, d]`, `4|t − c_tκ| < κ`, `2((t + ⌊κ/4⌋) mod κ) < κ`, and `κ₀ ≤ κ ≤ a`.
- **Lift structure.** Checked on 385 random palindromic `A` with coefficients in `3ℤ`, `N ∈ {3, 5, 15}`, `M ≤ 400`, and brute-force `κ ∈ [2m, L]` satisfying the lifting condition:
  - `mirror F = X^{L−D}A − B`;
  - the palindromic identity;
  - `G₂(x, x^κ) = x^h F̃`;
  - all `x`-exponents of `G₂` are `< κ/2`;
  - `G₂ = x^h(1 − x^N) + x^β A y^ℓ` with `ℓ ≥ 1`;
  - the no-carry specialization of `G₁G₂` equals `x^{2h} F F̃`.

## 8. Dependency graph

```
Dirichlet: D1 → D2 → D4 ← D3
Lift:      L1 → L2 → {L6, L7, L11};  L3, L4 → L7;  L5 → L6 → L7;  L9 → L10
Eisenstein: E2, E3, E4 → E5 ← E1
Ljunggren: 4.1, 4.2, 4.3 → 4.4 (IsRelPrime)
           D4 + 4.1–4.3 → K1;  L8 + L10 + 4.3 → K2;  L7 + L11 + E5 + K2 + 4.2 → K3
           K1 + K3 → K4;  K4 + 4.4 + irreducible_of_mirror → K5
           K5 + 4.6 + upstream → irreducible_Hfinal → (Main) Hfinal_irreducible_of_unsat
```
