module

public import CatalanCore.Arith.Hybrid.RankGLE
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

/-!
# UF moments: the Gauss DVR `ℤ_(p)[X]_{(p)}`

The second-order expansions of (S7) invert the core fiber blocks, whose determinants are monic,
hence nonzero modulo `p`.  We work in the localization `GaussLoc p` of `ℤ_(p)[X]` at the prime
`(p) = ker φ_p`, with the residue map `res : GaussLoc p → 𝔽_p(X)` extending `φ_p`.

* `isUnit_of_phiP_ne`: every `g` with `φ_p g ≠ 0` (e.g. a monic core determinant) is a unit;
* `res_eq_zero_iff`: `res x = 0 ↔ p ∣ x` (a DVR with uniformizer `p`);
* `dvd_of_local`: a `p^k`-divisibility proved in `GaussLoc p` holds in `ℤ_(p)[X]`, with the same
  reduced quotient.  This transfers the local computation back to the moment hypotheses.
-/

open Polynomial CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable (p : ℕ) [Fact p.Prime]

/-- The Gauss prime `(p) = ker φ_p` of `ℤ_(p)[X]`. -/
noncomputable def gaussIdeal : Ideal (LocRing p)[X] := RingHom.ker (phiP p)

instance gaussIdeal_isPrime : (gaussIdeal p).IsPrime := RingHom.ker_isPrime (phiP p)

/-- The Gauss DVR `ℤ_(p)[X]_{(p)}`. -/
abbrev GaussLoc : Type := Localization.AtPrime (gaussIdeal p)

lemma mem_primeCompl_iff (s : (LocRing p)[X]) :
    s ∈ (gaussIdeal p).primeCompl ↔ phiP p s ≠ 0 := by
  change s ∉ gaussIdeal p ↔ _
  rw [gaussIdeal, RingHom.mem_ker]

/-- The residue map `GaussLoc p → 𝔽_p(X)`. -/
noncomputable def res : GaussLoc p →+* RatFunc (ZMod p) :=
  IsLocalization.lift (M := (gaussIdeal p).primeCompl) (S := GaussLoc p) (g := phiP p)
    (fun s => isUnit_iff_ne_zero.2 ((mem_primeCompl_iff p s).1 s.2))

lemma res_algebraMap (g : (LocRing p)[X]) :
    res p (algebraMap (LocRing p)[X] (GaussLoc p) g) = phiP p g :=
  IsLocalization.lift_eq _ _

/-- The uniformizer `p` in `GaussLoc p`. -/
noncomputable abbrev piL : GaussLoc p :=
  algebraMap (LocRing p)[X] (GaussLoc p) (C ((p : ℕ) : LocRing p))

lemma res_piL : res p (piL p) = 0 := by
  rw [res_algebraMap, phiP_eq_zero_iff]

lemma isUnit_of_phiP_ne {g : (LocRing p)[X]} (hg : phiP p g ≠ 0) :
    IsUnit (algebraMap (LocRing p)[X] (GaussLoc p) g) :=
  IsLocalization.map_units (GaussLoc p) (⟨g, (mem_primeCompl_iff p g).2 hg⟩ :
    (gaussIdeal p).primeCompl)

/-- **`GaussLoc p` is a DVR with uniformizer `p`:** the kernel of `res` is `(p)`. -/
theorem res_eq_zero_iff (x : GaussLoc p) : res p x = 0 ↔ piL p ∣ x := by
  constructor
  · intro h
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (gaussIdeal p).primeCompl x
    have h1 : phiP p a = phiP p s * 0 :=
      (IsLocalization.lift_mk'_spec (M := (gaussIdeal p).primeCompl) (S := GaussLoc p) _ _ _ _).1 h
    rw [mul_zero, phiP_eq_zero_iff] at h1
    obtain ⟨b, rfl⟩ := h1
    exact ⟨IsLocalization.mk' (GaussLoc p) b s,
      (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm⟩
  · rintro ⟨y, rfl⟩
    rw [map_mul, res_piL, zero_mul]

lemma algebraMap_injective :
    Function.Injective (algebraMap (LocRing p)[X] (GaussLoc p)) :=
  IsLocalization.injective (GaussLoc p) (Ideal.primeCompl_le_nonZeroDivisors (gaussIdeal p))

/-- **Transfer of divisibility.**  If `g = p^k x` in `GaussLoc p` then `g = p^k q` in `ℤ_(p)[X]`
with `φ_p q = res x`. -/
theorem dvd_of_local (g : (LocRing p)[X]) (k : ℕ) (x : GaussLoc p)
    (h : algebraMap (LocRing p)[X] (GaussLoc p) g = piL p ^ k * x) :
    ∃ q : (LocRing p)[X], g = C ((p : ℕ) : LocRing p) ^ k * q ∧ phiP p q = res p x := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (gaussIdeal p).primeCompl x
  have hs : phiP p (s : (LocRing p)[X]) ≠ 0 := (mem_primeCompl_iff p s).1 s.2
  have hπ : Prime (C ((p : ℕ) : LocRing p)) := Polynomial.prime_C_iff.2 (prime_p p)
  rw [← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq,
    ← map_mul] at h
  have h2 := algebraMap_injective p h
  have hnd : ¬ C ((p : ℕ) : LocRing p) ∣ (s : (LocRing p)[X]) := by
    rw [← phiP_eq_zero_iff]; exact hs
  obtain ⟨q, hq⟩ := hπ.pow_dvd_of_dvd_mul_right k hnd ⟨b, h2⟩
  refine ⟨q, hq, ?_⟩
  have hne : C ((p : ℕ) : LocRing p) ^ k ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have h3 : q * s = b := by
    apply mul_left_cancel₀ hne
    rw [← h2, hq]; ring
  symm
  refine (IsLocalization.lift_mk'_spec (M := (gaussIdeal p).primeCompl) (S := GaussLoc p) _ _ _ _).2 ?_
  rw [← h3, map_mul, mul_comm]

end CatalanCore.Uniform.Content.UFMoments
