module

public import CatalanCore.Zeta5.Padic.Dist
public import CatalanCore.Zeta5.Parity.DirectGen

@[expose] public section

/-!
# ZC06(b), part 3: the leading term of `τ_X` modulo `p`

For a numerator `A` with local valuations `v_p^G(A(m + p x)) ≥ e(m mod p)` and a separated pole set
`Pl`, put `β ≤ e(c) - #Pl_c` for every class.  Then (`tauX_lead`)

* the `X`-coefficient of `τ_X(A/Π)` (`= -∑ res`) has valuation `≥ β + 1`;
* the constant coefficient `z` satisfies `v_p(p^{4-β} z) ≥ 0` and
  `p^{4-β} z ≡ ∑_{c < p} [e(c) - #Pl_c = β] ū_c⁻¹ locSym(I_c, ā_c) (mod p)`,

where at the residue `c` the local pole set is `I_c = {k : c + p k ∈ Pl}`, the local numerator is
`ā_c = p^{-e(c)} A(c + p x) mod p`, and `ū_c = ∏_{r ∈ Pl, r ≢ c} (c - r) mod p`.

The polynomial part is identified at the polynomial level: reducing the partial-fraction identity
at `x = c + p X` gives `ā_c = B_{I_c} · ū_c R̄_c + (deg < #I_c)`, so `ū_c R̄_c = ā_c div B_{I_c}`.
-/

open Finset Polynomial

namespace Apery

section lead
variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Harmonic numbers at large indices -/

lemma filter_dvd_Icc (N : ℕ) :
    (Icc 1 N).filter (fun v => p ∣ v) = (Icc 1 (N / p)).image (fun u => p * u) := by
  have hp0 := hp.out.pos
  ext v
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, u, rfl⟩
    refine ⟨u, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos u with h | h
      · subst h; simp at h1
      · exact h
    · rw [Nat.le_div_iff_mul_le hp0, Nat.mul_comm]; exact h2
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨Nat.mul_pos hp0 h1, ?_⟩, dvd_mul_right p u⟩
    rw [Nat.le_div_iff_mul_le hp0, Nat.mul_comm] at h2; exact h2

/-- `p⁵ H⁽⁵⁾_N ≡ H⁽⁵⁾_{⌊N/p⌋} (mod p⁵)` for `N < p²`. -/
lemma VG_H5_split (N : ℕ) : VG p ((p : ℚ) ^ 5 * H5 N - H5 (N / p)) 5 := by
  have hp0 := hp.out.pos
  unfold H5
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun v => p ∣ v), filter_dvd_Icc N,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp0 h), mul_add, Finset.mul_sum]
  have h1 : ∑ u ∈ Icc 1 (N / p), (p : ℚ) ^ 5 * (1 / ((p * u : ℕ) : ℚ) ^ 5) =
      ∑ u ∈ Icc 1 (N / p), 1 / (u : ℚ) ^ 5 := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu0 : (u : ℚ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hu).1; exact_mod_cast (by omega : u ≠ 0)
    have hp0' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    push_cast; field_simp
  rw [h1, add_sub_cancel_left, Finset.mul_sum]
  refine VG.sum _ fun v hv => ?_
  rw [Finset.mem_filter, Finset.mem_Icc] at hv
  have hv0 : (v : ℚ) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
  have hval : padicValRat p ((v : ℚ) ^ 5) = 0 := by
    rw [padicValRat.pow, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hv.2]; simp
  have hinv : VG p (1 / (v : ℚ) ^ 5) 0 := by
    rw [one_div]
    have := VG.inv (p := p) (r := 0) (pow_ne_zero 5 hv0) (by rw [hval]; simp)
    simpa using this
  have h5 : VG p ((p : ℚ) ^ 5) 5 := by
    have := VG.primePow (p := p) (5 : ℤ); simpa using this
  have := h5.mul hinv
  simpa using this

lemma dd_cast (x : ℤ) : ((dd x : ℕ) : ℤ) = if 0 ≤ x then x else -x - 1 := by
  unfold dd; split_ifs with h
  · exact Int.toNat_of_nonneg h
  · exact Int.toNat_of_nonneg (by omega)

/-- `⌊d(c + p k)/p⌋ = d(k)` for `0 ≤ c < p`. -/
lemma dd_local {c : ℕ} (hc : c < p) (k : ℤ) : dd ((c : ℤ) + p * k) / p = dd k := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hc' : (c : ℤ) < p := by exact_mod_cast hc
  have key : ∃ d : ℤ, 0 ≤ d ∧ d < p ∧ ((dd ((c : ℤ) + p * k) : ℕ) : ℤ) = p * (dd k : ℤ) + d := by
    rw [dd_cast, dd_cast]
    rcases le_or_gt 0 k with hk | hk
    · refine ⟨c, by positivity, hc', ?_⟩
      have : 0 ≤ (c : ℤ) + p * k := add_nonneg (by positivity) (mul_nonneg hp0.le hk)
      rw [if_pos this, if_pos hk]; ring
    · refine ⟨p - 1 - c, by omega, by omega, ?_⟩
      have : (c : ℤ) + p * k < 0 := by nlinarith
      rw [if_neg (by omega), if_neg (by omega)]; ring
  obtain ⟨d, hd0, hdp, he⟩ := key
  have : ((dd ((c : ℤ) + p * k) / p : ℕ) : ℤ) = (dd k : ℤ) := by
    rw [Int.natCast_div, he, add_comm, Int.add_mul_ediv_left _ _ hp0.ne',
      Int.ediv_eq_zero_of_lt hd0 hdp, zero_add]
  exact_mod_cast this

/-- `p⁵ H⁽⁵⁾_{d(c + p k)}` is integral and reduces to `H⁽⁵⁾_{d(k)}`. -/
lemma H5_local {c : ℕ} (hc : c < p) {k : ℤ} (hd : dd ((c : ℤ) + p * k) < p ^ 2) :
    VG p ((p : ℚ) ^ 5 * H5 (dd ((c : ℤ) + p * k))) 0 ∧
      (((p : ℚ) ^ 5 * H5 (dd ((c : ℤ) + p * k)) : ℚ) : ZMod p) = H5w (ZMod p) k := by
  have hsplit := VG_H5_split (p := p) (dd ((c : ℤ) + p * k))
  rw [dd_local hc] at hsplit
  have hlt : dd k < p := by
    rw [← dd_local (p := p) hc k]
    exact (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by rw [show p * p = p ^ 2 by ring]; exact hd)
  have hk0 : VG p (H5 (dd k)) 0 := VG_H5_lt hlt
  have hs0 : VG p ((p : ℚ) ^ 5 * H5 (dd ((c : ℤ) + p * k)) - H5 (dd k)) 0 :=
    hsplit.mono (by norm_num)
  have hs1 : VG p ((p : ℚ) ^ 5 * H5 (dd ((c : ℤ) + p * k)) - H5 (dd k)) 1 :=
    hsplit.mono (by norm_num)
  have e : (p : ℚ) ^ 5 * H5 (dd ((c : ℤ) + p * k)) =
      H5 (dd k) + ((p : ℚ) ^ 5 * H5 (dd ((c : ℤ) + p * k)) - H5 (dd k)) := by ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact hk0.add hs0
  · rw [e, red_add hk0 hs0, red_zero_of_VG_one hs1, add_zero]; rfl

/-! ### Local coordinates at a residue -/

/-- the local coordinate `k` of a pole `r = c + p k`. -/
def kloc (p c : ℕ) (r : ℤ) : ℤ := (r - c) / p

/-- the poles outside the residue class of `c`. -/
def plo (p : ℕ) (Pl : Finset ℤ) (c : ℕ) : Finset ℤ :=
  Pl.filter fun r : ℤ => ¬ (r : ZMod p) = (c : ZMod p)

/-- the local pole set `I_c = {k : c + p k ∈ Pl}`. -/
def locI (p : ℕ) (Pl : Finset ℤ) (c : ℕ) : Finset ℤ := (plc p Pl (c : ZMod p)).image (kloc p c)

/-- the far unit `ū_c = ∏_{r ≢ c} (c - r)`. -/
noncomputable def locU (p : ℕ) (Pl : Finset ℤ) (c : ℕ) : ZMod p :=
  ∏ r ∈ plo p Pl c, ((c : ZMod p) - (r : ZMod p))

/-- the local substitution `x = c + p X`. -/
noncomputable def locN (p : ℕ) [Fact p.Prime] (A : ℚ[X]) (e c : ℕ) : (ZMod p)[X] :=
  redP p (C ((p : ℚ) ^ (-(e : ℤ))) * A.comp (Gc p c))

/-- the tightness indicator of the residue `c`. -/
noncomputable def tind (p : ℕ) (eF : ZMod p → ℕ) (Pl : Finset ℤ) (β : ℤ) (c : ℕ) : ZMod p :=
  if (eF (c : ZMod p) : ℤ) - (plc p Pl (c : ZMod p)).card = β then 1 else 0

/-- **the local symbol of the residue `c`.** -/
noncomputable def locSymb (p : ℕ) [Fact p.Prime] (A : ℚ[X]) (eF : ZMod p → ℕ) (Pl : Finset ℤ)
    (β : ℤ) (c : ℕ) : ZMod p :=
  tind p eF Pl β c * (locU p Pl c)⁻¹ * locSym p (locI p Pl c) (locN p A (eF (c : ZMod p)) c)

lemma kloc_spec {c : ℕ} {r : ℤ} (hr : (r : ZMod p) = (c : ZMod p)) : r = c + p * kloc p c r := by
  have h := (zmod_eq_iff_dvd (p := p) (a := r) (b := (c : ℤ))).mp (by rw [hr, Int.cast_natCast])
  unfold kloc
  rw [Int.mul_ediv_cancel' h]; ring

lemma mem_plc_spec {Pl : Finset ℤ} {c : ℕ} {r : ℤ} (hr : r ∈ plc p Pl (c : ZMod p)) :
    r ∈ Pl ∧ (r : ZMod p) = (c : ZMod p) ∧ r = c + p * kloc p c r := by
  unfold plc at hr; rw [Finset.mem_filter] at hr
  exact ⟨hr.1, hr.2, kloc_spec hr.2⟩

lemma kloc_injOn (Pl : Finset ℤ) (c : ℕ) : Set.InjOn (kloc p c) (plc p Pl (c : ZMod p)) := by
  intro r hr s hs h
  have h1 := (mem_plc_spec (p := p) hr).2.2
  have h2 := (mem_plc_spec (p := p) hs).2.2
  calc r = c + p * kloc p c r := h1
    _ = c + p * kloc p c s := by rw [h]
    _ = s := h2.symm

lemma card_locI (Pl : Finset ℤ) (c : ℕ) : (locI p Pl c).card = (plc p Pl (c : ZMod p)).card :=
  Finset.card_image_of_injOn (kloc_injOn Pl c)

lemma locI_sub_unit {Pl : Finset ℤ} (hsep : Sep p Pl) {c : ℕ} {r s : ℤ}
    (hr : r ∈ plc p Pl (c : ZMod p)) (hs : s ∈ plc p Pl (c : ZMod p)) (hne : r ≠ s) :
    ¬ (p : ℤ) ∣ kloc p c r - kloc p c s := by
  intro hd
  have hr' := mem_plc_spec (p := p) hr
  have hs' := mem_plc_spec (p := p) hs
  apply hsep r hr'.1 s hs'.1 hne (by rw [hr'.2.1, hs'.2.1])
  have e : r - s = p * (kloc p c r - kloc p c s) := by linear_combination hr'.2.2 - hs'.2.2
  rw [e, pow_two]; exact mul_dvd_mul_left _ hd

lemma mem_plo {Pl : Finset ℤ} {c : ℕ} {r : ℤ} :
    r ∈ plo p Pl c ↔ r ∈ Pl ∧ ¬ (r : ZMod p) = (c : ZMod p) := by
  unfold plo; rw [Finset.mem_filter]

lemma plo_unit {Pl : Finset ℤ} {c : ℕ} {r : ℤ} (hr : r ∈ plo p Pl c) (k : ℤ) :
    ¬ (p : ℤ) ∣ (c : ℤ) - r + p * k := by
  intro hd
  apply (mem_plo.mp hr).2
  have h2 : (p : ℤ) ∣ (c : ℤ) - r := by
    have := dvd_sub hd (dvd_mul_right (p : ℤ) k); simpa using this
  have := (zmod_eq_iff_dvd (p := p) (a := (c : ℤ)) (b := r)).mpr h2
  rw [Int.cast_natCast] at this; exact this.symm

lemma locU_ne_zero (Pl : Finset ℤ) (c : ℕ) : locU p Pl c ≠ 0 := by
  unfold locU
  refine Finset.prod_ne_zero_iff.mpr fun r hr => sub_ne_zero.mpr fun h => ?_
  exact (mem_plo.mp hr).2 h.symm

/-! ### Products of linear factors at `x = c + p X` -/

/-- the far factors at `x = c + p X`. -/
noncomputable def farP (p : ℕ) (S : Finset ℤ) (c : ℕ) : ℚ[X] :=
  ∏ s ∈ plo p S c, (C ((c : ℚ) - s) + C (p : ℚ) * X)

lemma prod_comp_Gc (S : Finset ℤ) (c : ℕ) :
    (∏ s ∈ S, (X - C (s : ℚ))).comp (Gc p c) =
      C ((p : ℚ) ^ (plc p S (c : ZMod p)).card) *
        piF ((plc p S (c : ZMod p)).image (kloc p c)) * farP p S c := by
  rw [Polynomial.prod_comp,
    ← Finset.prod_filter_mul_prod_filter_not S (fun r : ℤ => (r : ZMod p) = (c : ZMod p))]
  congr 1
  · rw [piF, Finset.prod_image (fun a ha b hb h => kloc_injOn S c ha hb h)]
    have hfac : ∀ x ∈ plc p S (c : ZMod p), (X - C (x : ℚ)).comp (Gc p c) =
        C (p : ℚ) * (X - C ((kloc p c x : ℤ) : ℚ)) := by
      intro x hx
      have hx' : (x : ℚ) = c + p * (kloc p c x : ℚ) := by
        exact_mod_cast (mem_plc_spec (p := p) hx).2.2
      rw [sub_comp, X_comp, C_comp, Gc, hx', C_add, C_mul]; ring
    change ∏ x ∈ plc p S (c : ZMod p), (X - C (x : ℚ)).comp (Gc p c) = _
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, ← C_pow]
  · unfold farP plo
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [sub_comp, X_comp, C_comp, Gc, C_sub]; ring

lemma GV_piF (I : Finset ℤ) : GV p (piF I : ℚ[X]) 0 :=
  GV_prod0 _ _ fun k _ => by simpa using GV.X.sub (GV.C (VG.intCast (p := p) k))

lemma redP_piF (I : Finset ℤ) : redP p (piF I : ℚ[X]) = piF I := by
  unfold piF
  rw [redP_prod _ _ fun k _ => by simpa using GV.X.sub (GV.C (VG.intCast (p := p) k))]
  exact Finset.prod_congr rfl fun k _ => GV_redP_X_sub_C k

lemma natDegree_piF {F : Type*} [Field F] (I : Finset ℤ) : (piF I : F[X]).natDegree = I.card := by
  unfold piF
  rw [natDegree_prod_of_monic _ _ fun r _ => monic_X_sub_C _,
    Finset.sum_congr rfl fun x _ => natDegree_X_sub_C _]
  simp

lemma GV_farP (S : Finset ℤ) (c : ℕ) : GV p (farP p S c) 0 := by
  unfold farP
  refine GV_prod0 _ _ fun s _ => ?_
  have h1 : VG p ((c : ℚ) - s) 0 := by
    have := VG.intCast (p := p) ((c : ℤ) - s); simpa using this
  have := (GV.C h1).add (((GV.C (VG.natCast (p := p) p)).mul GV.X).mono (by norm_num))
  simpa using this

lemma redP_farP (S : Finset ℤ) (c : ℕ) :
    redP p (farP p S c) = C (∏ s ∈ plo p S c, ((c : ZMod p) - (s : ZMod p))) := by
  unfold farP
  rw [redP_prod _ _ fun s _ => by
    have h1 : VG p ((c : ℚ) - s) 0 := by
      have := VG.intCast (p := p) ((c : ℤ) - s); simpa using this
    have := (GV.C h1).add (((GV.C (VG.natCast (p := p) p)).mul GV.X).mono (by norm_num))
    simpa using this, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  have h1 : VG p ((c : ℚ) - s) 0 := by
    have := VG.intCast (p := p) ((c : ℤ) - s); simpa using this
  rw [redP_add (GV.C h1) ((GV.C (VG.natCast (p := p) p)).mul GV.X |>.mono (by norm_num)),
    redP_C, redP_C_mul (VG.natCast p) GV.X, redP_X, red_natCast, ZMod.natCast_self, C_0, zero_mul,
    add_zero]
  congr 1
  rw [show ((c : ℚ) - s) = (((c : ℤ) - s : ℤ) : ℚ) by push_cast; ring, red_intCast]
  push_cast; ring

lemma VG_eval_int {P : ℚ[X]} (hP : GV p P 0) (k : ℤ) : VG p (P.eval (k : ℚ)) 0 := by
  rw [eval_eq_sum_range_le P le_rfl]
  refine VG.sum _ fun n _ => ?_
  have := (hP n).mul ((VG.intCast (p := p) k).pow n)
  simpa using this

lemma VG_pow_nat (n : ℕ) : VG p ((p : ℚ) ^ n) n := by
  have := VG.primePow (p := p) (n : ℤ); simpa using this

/-- the `p`-adic unit `((z : ℤ) : ℚ)⁻¹` for `p ∤ z`. -/
lemma VG_inv_int_unit {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : VG p ((z : ℚ)⁻¹) 0 := by
  have hz : (z : ℚ) ≠ 0 := by
    have : z ≠ 0 := fun h0 => h (h0 ▸ dvd_zero _)
    exact_mod_cast this
  have := VG.inv (p := p) (r := 0) hz (by rw [padicValRat_int_eq_zero h]; simp)
  simpa using this

lemma plc_erase (Pl : Finset ℤ) (c : ℕ) (r : ℤ) :
    plc p (Pl.erase r) (c : ZMod p) = (plc p Pl (c : ZMod p)).erase r := by
  unfold plc; rw [Finset.filter_erase]

lemma plo_erase_of_plc {Pl : Finset ℤ} {c : ℕ} {r : ℤ} (hr : r ∈ plc p Pl (c : ZMod p)) :
    plo p (Pl.erase r) c = plo p Pl c := by
  unfold plo; rw [Finset.filter_erase]
  exact Finset.erase_eq_of_notMem fun h => (Finset.mem_filter.mp h).2 (mem_plc_spec hr).2.1

lemma plc_erase_of_plo {Pl : Finset ℤ} {c : ℕ} {r : ℤ} (hr : r ∈ plo p Pl c) :
    plc p (Pl.erase r) (c : ZMod p) = plc p Pl (c : ZMod p) := by
  rw [plc_erase]
  exact Finset.erase_eq_of_notMem fun h => (mem_plo.mp hr).2 (mem_plc_spec h).2.1

lemma image_erase_kloc {Pl : Finset ℤ} {c : ℕ} {r : ℤ} (hr : r ∈ plc p Pl (c : ZMod p)) :
    ((plc p Pl (c : ZMod p)).erase r).image (kloc p c) = (locI p Pl c).erase (kloc p c r) := by
  ext k
  simp only [locI, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨s, ⟨hsr, hs⟩, rfl⟩
    exact ⟨fun h => hsr (kloc_injOn Pl c hs hr h), s, hs, rfl⟩
  · rintro ⟨hk, s, hs, rfl⟩
    exact ⟨s, ⟨fun h => hk (h ▸ rfl), hs⟩, rfl⟩

/-! ### The local hypotheses -/

lemma hAloc_nat {A : ℚ[X]} {eF : ZMod p → ℕ}
    (hAloc : ∀ m : ℤ, GV p (A.comp (C (m : ℚ) + C (p : ℚ) * X)) (eF (m : ZMod p))) (c : ℕ) :
    GV p (A.comp (Gc p c)) (eF (c : ZMod p)) := by
  have := hAloc (c : ℤ); simpa [Gc] using this

lemma GV_locNum {A : ℚ[X]} {e c : ℕ} (h : GV p (A.comp (Gc p c)) e) :
    GV p (C ((p : ℚ) ^ (-(e : ℤ))) * A.comp (Gc p c)) 0 := by
  have := GV.C_mul (VG.primePow (p := p) (-(e : ℤ))) h
  refine this.mono (le_of_eq ?_); push_cast; ring

/-- `p^{d} N` with `d ≥ 0` reduces to `[d = 0] N̄`. -/
lemma redP_pow_mul {N : ℚ[X]} (hN : GV p N 0) {d : ℤ} (hd : 0 ≤ d) :
    GV p (C ((p : ℚ) ^ d) * N) 0 ∧
      redP p (C ((p : ℚ) ^ d) * N) = C (if d = 0 then (1 : ZMod p) else 0) * redP p N := by
  have h1 := GV.C_mul (VG.primePow (p := p) d) hN
  refine ⟨h1.mono (by simp; exact_mod_cast hd), ?_⟩
  split_ifs with h0
  · subst h0; simp
  · rw [C_0, zero_mul]
    exact redP_eq_zero_of_GV_one (h1.mono (by
      have : (1 : ℤ) ≤ d := by omega
      simp; exact_mod_cast this))

/-! ### The polynomial part at a residue -/

/-- the coefficient of the residue term `r` in the scaled local identity. -/
noncomputable def tcoef (p : ℕ) (A : ℚ[X]) (Pl : Finset ℤ) (β : ℤ) (c : ℕ) (r : ℤ) : ℚ :=
  (p : ℚ) ^ (-((plc p Pl (c : ZMod p)).card : ℤ) - β) * resP A Pl r *
    (p : ℚ) ^ (plc p (Pl.erase r) (c : ZMod p)).card

/-- the residue term `r` of the scaled local identity. -/
noncomputable def Tt (p : ℕ) (A : ℚ[X]) (Pl : Finset ℤ) (β : ℤ) (c : ℕ) (r : ℤ) : ℚ[X] :=
  C (tcoef p A Pl β c r) * piF (locI p (Pl.erase r) c) * farP p (Pl.erase r) c

/-- **The local partial-fraction identity** at `x = c + p X`, scaled by `p^{-ℓ-β}`. -/
lemma local_identity (A : ℚ[X]) (Pl : Finset ℤ) (β : ℤ) (c : ℕ) :
    C ((p : ℚ) ^ (-((plc p Pl (c : ZMod p)).card : ℤ) - β)) * A.comp (Gc p c) =
      C ((p : ℚ) ^ (-β)) * (polyPart A Pl).comp (Gc p c) * piF (locI p Pl c) * farP p Pl c +
        ∑ r ∈ Pl, Tt p A Pl β c r := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpf := congrArg (fun F => F.comp (Gc p c)) (partial_fractionsP A Pl)
  simp only [add_comp, mul_comp, Polynomial.sum_comp, C_comp] at hpf
  rw [hpf, piPl, prod_comp_Gc, mul_add, Finset.mul_sum]
  congr 1
  · have hs : (p : ℚ) ^ (-((plc p Pl (c : ZMod p)).card : ℤ) - β) *
        (p : ℚ) ^ (plc p Pl (c : ZMod p)).card = (p : ℚ) ^ (-β) := by
      rw [← zpow_natCast, ← zpow_add₀ hp0]; congr 1; ring
    rw [← hs, C_mul]; unfold locI; ring
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [Tt, tcoef, prod_comp_Gc, C_mul, C_mul]; unfold locI; ring

lemma VG_tcoef_plc (A : ℚ[X]) (eF : ZMod p → ℕ)
    (hAloc : ∀ m : ℤ, GV p (A.comp (C (m : ℚ) + C (p : ℚ) * X)) (eF (m : ZMod p)))
    (Pl : Finset ℤ) (hsep : Sep p Pl) (β : ℤ) (c : ℕ)
    {r : ℤ} (hr : r ∈ plc p Pl (c : ZMod p)) :
    VG p (tcoef p A Pl β c r) ((eF (c : ZMod p) : ℚ) - (plc p Pl (c : ZMod p)).card - β) := by
  have hr' := mem_plc_spec (p := p) hr
  have h1 := VG_res_gen A eF hAloc Pl hsep hr'.1
  rw [hr'.2.1] at h1
  have hcard : (plc p (Pl.erase r) (c : ZMod p)).card = (plc p Pl (c : ZMod p)).card - 1 := by
    rw [plc_erase, Finset.card_erase_of_mem hr]
  have hℓ1 : 1 ≤ (plc p Pl (c : ZMod p)).card := Finset.card_pos.mpr ⟨r, hr⟩
  unfold tcoef
  rw [hcard]
  have := ((VG.primePow (p := p) (-((plc p Pl (c : ZMod p)).card : ℤ) - β)).mul h1).mul
    (VG_pow_nat (p := p) ((plc p Pl (c : ZMod p)).card - 1))
  refine this.mono (le_of_eq ?_)
  push_cast [hℓ1]; ring

lemma VG_tcoef_plo (A : ℚ[X]) (eF : ZMod p → ℕ)
    (hAloc : ∀ m : ℤ, GV p (A.comp (C (m : ℚ) + C (p : ℚ) * X)) (eF (m : ZMod p)))
    (Pl : Finset ℤ) (hsep : Sep p Pl) (β : ℤ)
    (hβ : ∀ c : ZMod p, (β : ℚ) ≤ (eF c : ℚ) - (plc p Pl c).card) (c : ℕ)
    {r : ℤ} (hr : r ∈ plo p Pl c) : VG p (tcoef p A Pl β c r) 1 := by
  have h1 := VG_res_gen A eF hAloc Pl hsep (mem_plo.mp hr).1
  have hcard : (plc p (Pl.erase r) (c : ZMod p)).card = (plc p Pl (c : ZMod p)).card := by
    rw [plc_erase_of_plo hr]
  unfold tcoef
  rw [hcard]
  have := ((VG.primePow (p := p) (-((plc p Pl (c : ZMod p)).card : ℤ) - β)).mul h1).mul
    (VG_pow_nat (p := p) ((plc p Pl (c : ZMod p)).card))
  refine this.mono ?_
  have := hβ (r : ZMod p)
  push_cast; linarith

theorem redP_local_polyPart (A : ℚ[X]) (eF : ZMod p → ℕ)
    (hAloc : ∀ m : ℤ, GV p (A.comp (C (m : ℚ) + C (p : ℚ) * X)) (eF (m : ZMod p)))
    (Pl : Finset ℤ) (hsep : Sep p Pl) (hdeg : A.natDegree - Pl.card + 1 < p ^ 2)
    (β : ℤ) (hβ : ∀ c : ZMod p, (β : ℚ) ≤ (eF c : ℚ) - (plc p Pl c).card) (c : ℕ) (hc : c < p) :
    GV p (C ((p : ℚ) ^ (-β)) * (polyPart A Pl).comp (Gc p c)) 0 ∧
    redP p (C ((p : ℚ) ^ (-β)) * (polyPart A Pl).comp (Gc p c)) =
      C ((locU p Pl c)⁻¹ * tind p eF Pl β c) *
        (locN p A (eF (c : ZMod p)) c /ₘ piF (locI p Pl c)) := by
  classical
  have hNi : GV p (C ((p : ℚ) ^ (-(eF (c : ZMod p) : ℤ))) * A.comp (Gc p c)) 0 :=
    GV_locNum (hAloc_nat hAloc c)
  have hQdeg : (polyPart A Pl).natDegree < p ^ 2 :=
    lt_of_le_of_lt (natDegree_polyPart_le A Pl) (by omega)
  have hv : ∀ m : ℕ, VG p ((polyPart A Pl).eval (m : ℚ)) β := fun m => by
    have := VG_polyPart_eval_gen A eF hAloc Pl hsep (β : ℚ) hβ (m : ℤ)
    simpa using this
  have hRi : GV p (C ((p : ℚ) ^ (-β)) * (polyPart A Pl).comp (Gc p c)) 0 := fun j =>
    (GV_local_poly hQdeg hv c hc j).mono (by split_ifs <;> norm_num)
  refine ⟨hRi, ?_⟩
  have hid := local_identity (p := p) A Pl β c
  have hβc := hβ (c : ZMod p)
  have hL : C ((p : ℚ) ^ (-((plc p Pl (c : ZMod p)).card : ℤ) - β)) * A.comp (Gc p c) =
      C ((p : ℚ) ^ ((eF (c : ZMod p) : ℤ) - (plc p Pl (c : ZMod p)).card - β)) *
        (C ((p : ℚ) ^ (-(eF (c : ZMod p) : ℤ))) * A.comp (Gc p c)) := by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [← mul_assoc, ← C_mul, ← zpow_add₀ hp0]; congr 3; ring
  have hd0 : 0 ≤ (eF (c : ZMod p) : ℤ) - (plc p Pl (c : ZMod p)).card - β := by
    have : (β : ℚ) ≤ (eF (c : ZMod p) : ℚ) - (plc p Pl (c : ZMod p)).card := hβc
    have h' : β ≤ (eF (c : ZMod p) : ℤ) - (plc p Pl (c : ZMod p)).card := by exact_mod_cast this
    omega
  obtain ⟨_, hLr⟩ := redP_pow_mul (p := p) hNi hd0
  have htind : (if (eF (c : ZMod p) : ℤ) - (plc p Pl (c : ZMod p)).card - β = 0 then (1 : ZMod p)
      else 0) = tind p eF Pl β c := by
    unfold tind
    by_cases h : (eF (c : ZMod p) : ℤ) - (plc p Pl (c : ZMod p)).card = β
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  -- split the residue sum
  have hsplit : ∑ r ∈ Pl, Tt p A Pl β c r =
      ∑ r ∈ plc p Pl (c : ZMod p), Tt p A Pl β c r + ∑ r ∈ plo p Pl c, Tt p A Pl β c r := by
    unfold plc plo
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hTc : ∀ r ∈ plc p Pl (c : ZMod p), GV p (Tt p A Pl β c r) 0 := fun r hr => by
    have h1 : VG p (tcoef p A Pl β c r) 0 := (VG_tcoef_plc A eF hAloc Pl hsep β c hr).mono (by linarith)
    unfold Tt
    have := ((GV.C h1).mul (GV_piF (p := p) (locI p (Pl.erase r) c))).mul
      (GV_farP (p := p) (Pl.erase r) c)
    exact this.mono (by norm_num)
  have hTo : GV p (∑ r ∈ plo p Pl c, Tt p A Pl β c r) 1 := by
    refine GV.sum _ fun r hr => ?_
    unfold Tt
    have := ((GV.C (VG_tcoef_plo A eF hAloc Pl hsep β hβ c hr)).mul
      (GV_piF (p := p) (locI p (Pl.erase r) c))).mul (GV_farP (p := p) (Pl.erase r) c)
    exact this.mono (by norm_num)
  -- reduce the identity
  have hpiFi := GV_piF (p := p) (locI p Pl c)
  have hfi := GV_farP (p := p) Pl c
  have hRP : GV p (C ((p : ℚ) ^ (-β)) * (polyPart A Pl).comp (Gc p c) * piF (locI p Pl c)) 0 :=
    (hRi.mul hpiFi).mono (by norm_num)
  have hRF : GV p (C ((p : ℚ) ^ (-β)) * (polyPart A Pl).comp (Gc p c) * piF (locI p Pl c) *
      farP p Pl c) 0 := (hRP.mul hfi).mono (by norm_num)
  have hsumc : GV p (∑ r ∈ plc p Pl (c : ZMod p), Tt p A Pl β c r) 0 := GV.sum _ hTc
  have hred := congrArg (redP p) hid
  rw [hL, hLr, hsplit, ← add_assoc,
    redP_add (hRF.add hsumc) (hTo.mono (by norm_num)), redP_eq_zero_of_GV_one hTo, add_zero,
    redP_add hRF hsumc, redP_mul hRP hfi, redP_mul hRi hpiFi, redP_piF, redP_farP,
    htind] at hred
  -- the remainder has degree `< #I`
  have hRemdeg : (redP p (∑ r ∈ plc p Pl (c : ZMod p), Tt p A Pl β c r)).degree <
      (piF (locI p Pl c) : (ZMod p)[X]).degree := by
    rw [degree_eq_natDegree (piF_monic (p := p) (locI p Pl c)).ne_zero, natDegree_piF, card_locI,
      degree_lt_iff_coeff_zero]
    intro n hn
    rw [redP_sum _ _ hTc, finsetSum_coeff]
    refine Finset.sum_eq_zero fun r hr => ?_
    have hcard : (plc p (Pl.erase r) (c : ZMod p)).card = (plc p Pl (c : ZMod p)).card - 1 := by
      rw [plc_erase, Finset.card_erase_of_mem hr]
    have h1 : VG p (tcoef p A Pl β c r) 0 := (VG_tcoef_plc A eF hAloc Pl hsep β c hr).mono (by linarith)
    unfold Tt
    rw [redP_mul (((GV.C h1).mul (GV_piF _)).mono (by norm_num)) (GV_farP _ _),
      redP_mul (GV.C h1) (GV_piF _), redP_piF, redP_farP, redP_C]
    refine coeff_eq_zero_of_natDegree_lt ?_
    refine lt_of_le_of_lt ((natDegree_mul_C_le _ _).trans (natDegree_C_mul_le _ _)) ?_
    rw [natDegree_piF, card_locI, hcard]
    have hℓ1 : 1 ≤ (plc p Pl (c : ZMod p)).card := Finset.card_pos.mpr ⟨r, hr⟩
    omega
  have huniq := div_modByMonic_unique
    (f := C (tind p eF Pl β c) * locN p A (eF (c : ZMod p)) c)
    (C (locU p Pl c) * redP p (C ((p : ℚ) ^ (-β)) * (polyPart A Pl).comp (Gc p c)))
    (redP p (∑ r ∈ plc p Pl (c : ZMod p), Tt p A Pl β c r)) (piF_monic (p := p) (locI p Pl c))
    ⟨by rw [locN, hred]; unfold locU; ring, hRemdeg⟩
  have hU := locU_ne_zero (p := p) Pl c
  have key : redP p (C ((p : ℚ) ^ (-β)) * (polyPart A Pl).comp (Gc p c)) =
      C ((locU p Pl c)⁻¹) * ((C (tind p eF Pl β c) * locN p A (eF (c : ZMod p)) c) /ₘ
        piF (locI p Pl c)) := by
    rw [huniq.1, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hU, C_1, one_mul]
  rw [key, ← smul_eq_C_mul (tind p eF Pl β c), smul_divByMonic, smul_eq_C_mul, ← mul_assoc,
    ← C_mul]

end lead

end Apery
