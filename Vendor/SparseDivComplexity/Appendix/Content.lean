import Mathlib

/-!
# Appendix A.1 — content split and Gauss's lemma for integer divisibility

For sparse `f, g ∈ ℤ[X]` with `g ≠ 0`, `c = cont(g)`, `G = g / c` primitive:

* `g ∣ f` in `ℤ[X]` iff `c` divides every coefficient of `f` and `G ∣ f / c` in `ℤ[X]`;
* (Gauss) for primitive `G`, `G ∣ F` in `ℤ[X]` iff `G ∣ F` in `ℚ[X]`
  (`Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`).

Together with the boundary cases (`g = 0`, `f = 0`, constant `g`, degree comparison) these are the
"preliminary reductions" of Appendix A.1. The bit-complexity of the normalization and of the integer
gcd / divisibility tests is a separate (unfinished) item; see `docs/STATUS.md`.
-/

open Polynomial

namespace SparseDiv.Appendix

/-- `0 ∣ f` iff `f = 0`. -/
theorem zero_dvd_iff' (f : ℤ[X]) : (0 : ℤ[X]) ∣ f ↔ f = 0 := zero_dvd_iff

/-- A nonzero constant divides `f` iff it divides every coefficient. -/
theorem C_dvd_iff_forall_coeff (c : ℤ) (f : ℤ[X]) : C c ∣ f ↔ ∀ n, c ∣ f.coeff n :=
  C_dvd_iff_dvd_coeff c f

/-- After excluding `f = 0`, a divisor of larger degree cannot divide. -/
theorem not_dvd_of_natDegree_lt {f g : ℤ[X]} (hf : f ≠ 0) (h : f.natDegree < g.natDegree) :
    ¬ g ∣ f :=
  fun hdvd ↦ absurd (natDegree_le_of_dvd hdvd hf) (not_le.mpr h)

/-- The content divides every coefficient, so `f = C (cont f) * primPart f`. -/
theorem eq_C_content_mul_primPart' (f : ℤ[X]) : f = C f.content * f.primPart :=
  eq_C_content_mul_primPart f

/-- **Content split.** For `g ≠ 0` with `c = cont g` and `G = primPart g`:
`g ∣ f ↔ (∀ n, c ∣ f.coeff n) ∧ G ∣ f /ₘ …`; stated with the quotient polynomial `f₀` satisfying
`f = C c * f₀`. -/
theorem dvd_iff_content_dvd_and_primPart_dvd {f g : ℤ[X]} (hg : g ≠ 0) :
    g ∣ f ↔ ∃ f₀ : ℤ[X], f = C g.content * f₀ ∧ g.primPart ∣ f₀ := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨g.primPart * h, by rw [← mul_assoc, ← eq_C_content_mul_primPart], dvd_mul_right _ _⟩
  · rintro ⟨f₀, rfl, hdvd⟩
    calc g = C g.content * g.primPart := eq_C_content_mul_primPart g
      _ ∣ C g.content * f₀ := mul_dvd_mul_left _ hdvd

/-- The quotient `f / c` exists iff `c` divides every coefficient. -/
theorem exists_eq_C_mul_iff (c : ℤ) (f : ℤ[X]) (hc : c ≠ 0) :
    (∃ f₀ : ℤ[X], f = C c * f₀) ↔ ∀ n, c ∣ f.coeff n :=
  C_dvd_iff_dvd_coeff c f

/-- **Gauss's lemma, primitive-divisor form**: for primitive `G`, divisibility in `ℤ[X]` and in
`ℚ[X]` agree. -/
theorem primitive_dvd_iff_map_dvd_map {G F : ℤ[X]} (hG : G.IsPrimitive) :
    G ∣ F ↔ G.map (Int.castRingHom ℚ) ∣ F.map (Int.castRingHom ℚ) :=
  IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast G F hG

/-- The primitive part of a nonzero polynomial is primitive and has the same degree. -/
theorem isPrimitive_primPart' (g : ℤ[X]) : g.primPart.IsPrimitive := isPrimitive_primPart g

theorem natDegree_primPart' (g : ℤ[X]) : g.primPart.natDegree = g.natDegree :=
  natDegree_primPart g

/-- Reduction modulo a prime of a primitive polynomial is nonzero. -/
theorem map_ne_zero_of_isPrimitive {G : ℤ[X]} (hG : G.IsPrimitive) {p : ℕ} (hp : p.Prime) :
    G.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro h
  have hdvd : C (p : ℤ) ∣ G := by
    rw [C_dvd_iff_dvd_coeff]
    intro n
    have hn := congrArg (fun q ↦ q.coeff n) h
    simp only [coeff_map, coeff_zero, eq_intCast] at hn
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn
  have h1 : (p : ℤ) ∣ G.content := dvd_content_iff_C_dvd.mpr hdvd
  rw [hG.content_eq_one] at h1
  exact hp.ne_one (Nat.dvd_one.mp (by exact_mod_cast h1))

/-- **NO instances stay NO**: if `G ∣ F` in `ℤ[X]` then `(G mod p) ∣ (F mod p)` for every `p`. -/
theorem map_dvd_map_of_dvd {G F : ℤ[X]} (h : G ∣ F) (p : ℕ) :
    G.map (Int.castRingHom (ZMod p)) ∣ F.map (Int.castRingHom (ZMod p)) :=
  Polynomial.map_dvd _ h

end SparseDiv.Appendix
