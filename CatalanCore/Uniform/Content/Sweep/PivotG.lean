module

public import CatalanCore.Uniform.Content.Sweep.PFacts
public import CatalanCore.Uniform.Content.Sweep.Gen
public import CatalanCore.Uniform.Content.Sweep.ND
public import CatalanCore.Uniform.Content.Sweep.Schur

@[expose] public section

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support
/-!
# Lemma G for the plane 2 matrix (lane H, wave H2b; ledger P204)

Transfer of the abstract `Gen.lemmaG` to the plane 2 matrix `Qent` over any commutative
`ℤ_(p)`-algebra `R`, in the ring `S2 = R / (p²)`: F1 (`PFacts.F1`) is the congruent hypothesis, F2
(`PFacts.F2`, with `ddR_cong` replacing the inverse of `t - n` by that of the residues) the non-congruent
one, `Bm_symm` and `Bm_halves`/`sigR_halves` the symmetry and halves, and `sum_dd_dvd` the residue sum
`∑_{a ≠ ω} (a - ω)⁻¹ ≡ 0 (mod p)`.  The class solutions `Yr` of the class equations are hypotheses of
`lemmaG_S` (they exist by Theorem ND, in `Sweep.Classes`).
-/

namespace CatalanCore.Uniform.Content.Sweep

section Transfer

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [Algebra (LocRing p) R]

/-- The ring `R / (p²)`. -/
abbrev S2 (p : ℕ) (R : Type*) [CommRing R] : Type _ := R ⧸ Ideal.span {(p : R) ^ 2}

/-- The quotient map. -/
def pi2 (p : ℕ) (R : Type*) [CommRing R] : R →+* S2 p R := Ideal.Quotient.mk _

theorem pi2_eq_iff {x y : R} : pi2 p R x = pi2 p R y ↔ (p : R) ^ 2 ∣ x - y := by
  unfold pi2
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

theorem pi2_eq_zero_iff {x : R} : pi2 p R x = 0 ↔ (p : R) ^ 2 ∣ x := by
  have := pi2_eq_iff (p := p) (x := x) (y := 0)
  rw [map_zero, sub_zero] at this
  exact this

theorem pi2_p_mul_eq {x y : R} (h : (p : R) ∣ x - y) : pi2 p R (p : R) * pi2 p R x = pi2 p R (p : R) * pi2 p R y := by
  rw [← map_mul, ← map_mul, pi2_eq_iff, ← mul_sub]
  obtain ⟨c, hc⟩ := h
  rw [hc]; exact ⟨c, by ring⟩

theorem pi2_P_sq : pi2 p R (p : R) * pi2 p R (p : R) = 0 := by
  rw [← map_mul, ← pow_two]
  unfold pi2
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- The inverse of the residue difference, as an element of `R`. -/
noncomputable def ddR (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra (LocRing p) R]
    (a b : ℕ) : R := algebraMap (LocRing p) R (invZ p ((b : ℤ) - a))

theorem toR_inv_eq {n t : ℕ} (hz : ¬ (p : ℤ) ∣ (t : ℤ) - n) :
    toR p ((((t : ℚ) - n)⁻¹)) = (algebraMap (LocRing p) R (invZ p ((t : ℤ) - n)) : R) := by
  have hinv : (((t : ℚ) - n)⁻¹) ∈ LocRing p := by
    have := inv_int_mem (p := p) hz; push_cast at this; exact this
  rw [toR_of_mem hinv]
  congr 1
  apply Subtype.ext
  rw [coe_invZ, if_neg hz]; push_cast; rfl

theorem invZ_cong {x y : ℤ} (h : (p : ℤ) ∣ x - y) :
    (p : LocRing p) ∣ invZ p x - invZ p y := by
  rw [← redQ_eq_zero_iff, map_sub, redQ_invZ, redQ_invZ]
  have : (x : ZMod p) = y := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) p).2 h
    push_cast at this; exact sub_eq_zero.1 this
  rw [this, sub_self]

theorem ddR_cong {u t : ℕ} (hz : ¬ (p : ℤ) ∣ (t : ℤ) - u) :
    (p : R) ∣ toR p ((((t : ℚ) - u)⁻¹)) - ddR (p := p) (u % p) (t % p) := by
  rw [toR_inv_eq hz]
  unfold ddR
  rw [← map_sub]
  have h1 : (p : ℤ) ∣ (t : ℤ) - ((t % p : ℕ) : ℤ) := ⟨(t : ℤ) / p, by
    have : ((t % p : ℕ) : ℤ) = (t : ℤ) % p := by push_cast; rfl
    rw [this, Int.emod_def]; ring⟩
  have h2 : (p : ℤ) ∣ (u : ℤ) - ((u % p : ℕ) : ℤ) := ⟨(u : ℤ) / p, by
    have : ((u % p : ℕ) : ℤ) = (u : ℤ) % p := by push_cast; rfl
    rw [this, Int.emod_def]; ring⟩
  obtain ⟨c, hc⟩ := invZ_cong (p := p) (x := (t : ℤ) - u) (y := ((t % p : ℕ) : ℤ) - ((u % p : ℕ) : ℤ)) (by
    have := dvd_sub h1 h2
    convert this using 1; ring)
  rw [hc, map_mul, map_natCast]
  exact Dvd.intro _ rfl




end Transfer

/-! ### Lemma G for the plane 2 matrix -/

section Inst

open CatalanCore.Uniform.Content.Sweep.Gen

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ)
  {R : Type*} [CommRing R] [Algebra (LocRing p) R]

/-- The vector index `b ∈ {0,1}`: `Γ^0 = 1`, `Γ^1 = σ`, over `R`. -/
noncomputable def GamR (b h l : ℕ) : R := if b = 0 then 1 else sigR (p := p) v u (l, h)

theorem Bm_symm (ξ : R) (h l j : ℕ) : Bm (p := p) v u ξ h l j = Bm (p := p) v u ξ h j l := by
  unfold Bm
  by_cases hlj : l = j
  · subst hlj; rfl
  · rw [if_neg hlj, if_neg (Ne.symm hlj)]
    congr 1
    have h1 : (l : ℚ) - j ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hlj)
    have h2 : (j : ℚ) - l ≠ 0 := sub_ne_zero.2 (by exact_mod_cast Ne.symm hlj)
    field_simp
    ring

theorem sum_dd_dvd (hp5 : 5 ≤ p) (ω : ℕ) :
    (p : R) ∣ ∑ a ∈ (range p).erase ω, ddR (p := p) (R := R) ω a := by
  have hp0 : 0 < p := hp.out.pos
  have hz : ddR (p := p) (R := R) ω ω = (0 : R) := by
    unfold ddR; simp [invZ]
  have hfull : ∑ a ∈ (range p).erase ω, ddR (p := p) (R := R) ω a = ∑ a ∈ range p, ddR (p := p) (R := R) ω a := by
    by_cases hω : ω ∈ range p
    · rw [← Finset.add_sum_erase _ _ hω, hz, zero_add]
    · rw [Finset.erase_eq_of_notMem hω]
  rw [hfull]
  unfold ddR
  rw [← map_sum]
  have : (p : LocRing p) ∣ ∑ a ∈ range p, invZ p ((a : ℤ) - ω) := by
    rw [← redQ_eq_zero_iff, map_sum]
    simp only [redQ_invZ]
    have := sum_range_cast (p := p) (fun y => (y - (ω : ZMod p))⁻¹) 0
    simp only [Nat.zero_add] at this
    push_cast
    have e := Equiv.sum_comp (Equiv.subRight (ω : ZMod p)) (fun y => y⁻¹)
    simp only [Equiv.subRight_apply] at e
    rw [this, e]
    exact sum_inv_zmod hp5
  obtain ⟨c, hc⟩ := this
  rw [hc, map_mul, map_natCast]
  exact Dvd.intro _ rfl




/-- The data of `lemmaG` for the plane 2 matrix, in `S = R / (p²)`. -/
noncomputable def qS (ξ : R) (n t : ℕ) : S2 p R := pi2 p R (Qent (p := p) v u ξ n t)
noncomputable def BmS (ξ : R) (h l j : ℕ) : S2 p R := pi2 p R (Bm (p := p) v u ξ (min h 1) l j)
noncomputable def sgS (j h : ℕ) : S2 p R := pi2 p R (sigR (p := p) v u (j, min h 1))
noncomputable def ddS (a b : ℕ) : S2 p R := pi2 p R (ddR (p := p) a b)
noncomputable def YvS (Yr : ℕ → ℕ → ℕ → ℕ → R) (b h o j : ℕ) : S2 p R := pi2 p R (Yr b (min h 1) o j)

theorem half_le_one' {u : ℤ} (t : ℕ) : half p u t ≤ 1 := by unfold half; split_ifs <;> omega

theorem lemmaG_S (hodd : p % 2 = 1) (hp5 : 5 ≤ p) {κ k' π N' : ℕ} (hN : 2 * N' < p * p)
    (hH : (κ + 2 * k') * p ≤ N') (ξ : R)
    (Yr : ℕ → ℕ → ℕ → ℕ → R)
    (hclassR : ∀ b h o, o ≤ 1 → h ≤ 1 → ∀ l ∈ Cper κ k' (1 - o),
      ∑ j ∈ Cper κ k' o, Bm (p := p) v u ξ h l j * Yr b h o j = GamR (p := p) v u b h l)
    (hYhR : ∀ b o, o ≤ 1 → ∀ j ∈ Cper κ k' o, (p : R) ∣ Yr b 1 o j - Yr b 0 o j)
    (n : ℕ) (hn : n < N') (b : ℕ) (hb : b ≤ 1) :
    ∑ t ∈ PCs p κ k' π, qS v u ξ n t *
        (Gen.eps (pi2 p R (p : R)) p κ k' π (sgS v u) (ddS) (YvS Yr) (t % p) *
          YvS Yr b (half p u t) (oc p κ π (t % p)) (t / p)) =
      Gen.eps (pi2 p R (p : R)) p κ k' π (sgS v u) (ddS) (YvS Yr) (n % p) *
          (∑ j ∈ Cper κ k' (oc p κ π (n % p)),
            BmS v u ξ (half p u n) (n / p) j * YvS Yr b (half p u n) (oc p κ π (n % p)) j) +
        pi2 p R (p : R) * delta κ k' (sgS v u) (YvS Yr) * Eres p κ π ddS (n % p) *
          Gam (sgS v u) b (half p u n) (n / p) := by
  have hp0 : 0 < p := hp.out.pos
  have hPS := pi2_P_sq (p := p) (R := R)
  have hper : ∀ j, j < κ + 2 * k' → (j + 1) * p ≤ N' := fun j hj => by nlinarith
  have hmemt : ∀ t ∈ PCs p κ k' π, t < N' := by
    intro t ht
    rw [mem_PCs (p := p) (κ := κ) (k' := k') (π := π) hp0] at ht
    have hj := ((mem_Cper (κ := κ) (k' := k')).1 ht).1
    have : t / p < κ + 2 * k' := hj
    have h1 := (Nat.div_lt_iff_lt_mul hp0).1 this
    nlinarith
  refine lemmaG (pi2 p R (p : R)) p π (sgS v u) ddS (YvS Yr) hPS hp0 N' (half p u)
    (fun t => by unfold half; rw [Nat.mod_mod]) half_le_one' (qS v u ξ) (BmS v u ξ) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    n hn b hb
  · -- F1
    intro n' hn' t ht hm
    unfold qS BmS
    rw [pi2_eq_iff, min_eq_left (half_le_one' _)]
    exact F1 v u hodd hp5 hN ξ hn' (lt_of_lt_of_le (hmemt t ht) le_rfl) hm
  · -- F2
    intro n' hn' t ht hm
    unfold qS sgS ddS
    have hz : ¬ (p : ℤ) ∣ (t : ℤ) - n' := by
      intro hd
      apply hm
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((t : ℤ) - n') p).2 hd
      push_cast at this
      rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff'] at this
      exact this.symm
    have h2 := F2 v u hodd hp5 hN ξ hn' (hmemt t ht) hm
    unfold cell at h2
    have h3 := ddR_cong (p := p) (R := R) hz
    rw [min_eq_left (half_le_one' t), min_eq_left (half_le_one' n')]
    simp only [← map_sub, ← map_mul]
    rw [pi2_eq_iff]
    have e : Qent (p := p) v u ξ n' t -
        (p : R) * (sigR (p := p) v u (t / p, half p u t) - sigR (p := p) v u (n' / p, half p u n')) *
          ddR (p := p) (n' % p) (t % p) =
        (Qent (p := p) v u ξ n' t - (p : R) * (sigR (p := p) v u (t / p, half p u t) - sigR (p := p) v u (n' / p, half p u n')) *
          toR p ((((t : ℚ) - n')⁻¹))) +
        (p : R) * (sigR (p := p) v u (t / p, half p u t) - sigR (p := p) v u (n' / p, half p u n')) *
          (toR p ((((t : ℚ) - n')⁻¹)) - ddR (p := p) (n' % p) (t % p)) := by
      ring
    rw [e]
    obtain ⟨c, hc⟩ := h3
    refine dvd_add h2 ?_
    rw [hc]
    exact ⟨(sigR (p := p) v u (t / p, half p u t) - sigR (p := p) v u (n' / p, half p u n')) * c, by ring⟩
  · intro h l j
    unfold BmS
    rw [Bm_symm v u ξ (min h 1) l j]
  · -- halves of sigma
    intro j hj h hh
    unfold sgS
    obtain rfl | rfl : h = 0 ∨ h = 1 := by omega
    · rfl
    · simp only [min_self, Nat.zero_min]
      exact pi2_p_mul_eq (sigR_halves v u hodd hN (hper j hj))
  · intro b o ho j hj h hh
    unfold YvS
    obtain rfl | rfl : h = 0 ∨ h = 1 := by omega
    · rfl
    · simp only [min_self, Nat.zero_min]
      exact pi2_p_mul_eq (hYhR b o ho j hj)
  · intro ω hω
    unfold ddS
    rw [← map_sum, ← map_mul, pi2_eq_zero_iff]
    obtain ⟨c, hc⟩ := sum_dd_dvd (p := p) (R := R) hp5 ω
    rw [hc]
    exact ⟨c, by ring⟩
  · intro b h o ho l hl
    have e := congrArg (pi2 p R) (hclassR b (min h 1) o ho (min_le_right _ _) l hl)
    rw [map_sum] at e
    simp only [map_mul] at e
    unfold Gam sgS BmS YvS
    unfold GamR at e
    by_cases hb0 : b = 0
    · simp only [hb0, if_true, map_one] at e ⊢; exact e
    · simp only [hb0, if_false] at e ⊢; exact e

end Inst

/-! ### General integer-pole transfer at fixed mod-p² precision (Q05)

The complete period class has one half-independent source. Order changes the
concrete period levels, not the residue cancellation engine. Actual class solutions
are hypotheses; no automatic nondegeneracy assertion is made.
-/
namespace HPole
open CatalanCore.Uniform.Content.Sweep.Gen
variable {p : ℕ} [hp : Fact p.Prime]
  {R : Type*} [CommRing R] [Algebra (LocRing p) R]

noncomputable def qS (ord : ℕ) (d : ℕ → ℚ) (ξ : R) (n t : ℕ) : S2 p R :=
  pi2 p R (Qh (p := p) ord d ξ n t)
noncomputable def BmS (ord : ℕ) (d : ℕ → ℚ) (ξ : R) (_half l j : ℕ) : S2 p R :=
  pi2 p R (Bm (p := p) ord d ξ l j)
noncomputable def sgS (ord : ℕ) (d : ℕ → ℚ) (j _half : ℕ) : S2 p R :=
  pi2 p R (sigR (p := p) ord d j)
noncomputable def YvS (Yr : ℕ → ℕ → ℕ → R) (b _half o j : ℕ) : S2 p R :=
  pi2 p R (Yr b o j)

theorem lemmaG_S (ord : ℕ) (hord : 3 ≤ ord) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (ord - 1), d j ∈ LocRing p) (hp5 : 5 ≤ p) {κ k' π N' : ℕ} (hN : 2 * N' < p * p)
    (hH : (κ + 2 * k') * p ≤ N') (ξ : R)
    (Yr : ℕ → ℕ → ℕ → R)
    (hclassR : ∀ b o, o ≤ 1 → ∀ l ∈ Cper κ k' (1 - o),
      ∑ j ∈ Cper κ k' o, Bm (p := p) ord d ξ l j * Yr b o j =
        if b = 0 then 1 else sigR (p := p) ord d l)
    (n : ℕ) (hn : n < N') (b : ℕ) (hb : b ≤ 1) :
    ∑ t ∈ PCs p κ k' π, qS ord d ξ n t *
        (Gen.eps (pi2 p R (p : R)) p κ k' π (sgS ord d) (ddS) (YvS Yr) (t % p) *
          YvS Yr b (0) (oc p κ π (t % p)) (t / p)) =
      Gen.eps (pi2 p R (p : R)) p κ k' π (sgS ord d) (ddS) (YvS Yr) (n % p) *
          (∑ j ∈ Cper κ k' (oc p κ π (n % p)),
            BmS ord d ξ (0) (n / p) j * YvS Yr b (0) (oc p κ π (n % p)) j) +
        pi2 p R (p : R) * delta κ k' (sgS ord d) (YvS Yr) * Eres p κ π ddS (n % p) *
          Gam (sgS ord d) b (0) (n / p) := by
  have hp0 : 0 < p := hp.out.pos
  have hPS := pi2_P_sq (p := p) (R := R)
  have hmemt : ∀ t ∈ PCs p κ k' π, t < N' := by
    intro t ht
    rw [mem_PCs (p := p) (κ := κ) (k' := k') (π := π) hp0] at ht
    have hj := ((mem_Cper (κ := κ) (k' := k')).1 ht).1
    have : t / p < κ + 2 * k' := hj
    have h1 := (Nat.div_lt_iff_lt_mul hp0).1 this
    nlinarith
  refine Gen.lemmaG (pi2 p R (p : R)) p π (sgS ord d) ddS (YvS Yr) hPS hp0 N'
    (fun _ => 0) (fun _ => rfl) (fun _ => by omega)
    (qS ord d ξ) (BmS ord d ξ) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    n hn b hb
  · -- F1
    intro n' hn' t ht hm
    unfold qS BmS
    rw [pi2_eq_iff]
    exact F1 ord hord d hd ξ (by nlinarith) (by have := hmemt t ht; nlinarith) hm
  · -- F2
    intro n' hn' t ht hm
    unfold qS sgS ddS
    have hz : ¬ (p : ℤ) ∣ (t : ℤ) - n' := by
      intro hd
      apply hm
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((t : ℤ) - n') p).2 hd
      push_cast at this
      rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff'] at this
      exact this.symm
    have h2 := F2 ord hord d hd ξ (by nlinarith : n' < p * p)
      (by have := hmemt t ht; nlinarith : t < p * p) hm
    have h3 := ddR_cong (p := p) (R := R) hz
    simp only [← map_sub, ← map_mul]
    rw [pi2_eq_iff]
    have e : Qh (p := p) ord d ξ n' t -
        (p : R) * (sigR (p := p) ord d (t / p) - sigR (p := p) ord d (n' / p)) *
          ddR (p := p) (n' % p) (t % p) =
        (Qh (p := p) ord d ξ n' t - (p : R) * (sigR (p := p) ord d (t / p) - sigR (p := p) ord d (n' / p)) *
          toR p ((((t : ℚ) - n')⁻¹))) +
        (p : R) * (sigR (p := p) ord d (t / p) - sigR (p := p) ord d (n' / p)) *
          (toR p ((((t : ℚ) - n')⁻¹)) - ddR (p := p) (n' % p) (t % p)) := by
      ring
    rw [e]
    obtain ⟨c, hc⟩ := h3
    refine dvd_add h2 ?_
    rw [hc]
    exact ⟨(sigR (p := p) ord d (t / p) - sigR (p := p) ord d (n' / p)) * c, by ring⟩
  · intro h l j
    unfold BmS
    rw [Bm_symm ord d ξ l j]
  · intro j hj h hh
    rfl
  · intro b o ho j hj h hh
    rfl
  · intro ω hω
    unfold ddS
    rw [← map_sum, ← map_mul, pi2_eq_zero_iff]
    obtain ⟨c, hc⟩ := sum_dd_dvd (p := p) (R := R) hp5 ω
    rw [hc]
    exact ⟨c, by ring⟩
  · intro b h o ho l hl
    have e := congrArg (pi2 p R) (hclassR b o ho l hl)
    rw [map_sum] at e
    simp only [map_mul] at e
    unfold Gam sgS BmS YvS
    by_cases hb0 : b = 0
    · simp only [hb0, if_true, map_one] at e ⊢; exact e
    · simp only [hb0, if_false] at e ⊢; exact e

end HPole

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.lemmaG_S
#print axioms CatalanCore.Uniform.Content.Sweep.sum_dd_dvd

#print axioms CatalanCore.Uniform.Content.Sweep.HPole.lemmaG_S
