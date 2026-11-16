module

public import CatalanCore.Zeta5.Padic.TauLead

@[expose] public section

/-!
# ZC06(b), part 5: the residues `c` and `p - c`, and the local pole intervals of `±[1, K]`

* `locSymb_pc`: for an odd numerator and a symmetric pole set the local symbols at `c` and `p - c`
  agree (`ā_{p-c} = -J ā_c`, `I_{p-c} = refl I_c`, `ū_{p-c} = (-1)^{#far} ū_c`), provided the local
  pole set of a tight residue is reflection-symmetric of even size.
* `sum_range_pair`: `∑_{c < p} f c = f 0 + 2 ∑_{a=1}^{m} f a` for such `f`.
* `mem_locI_PlK`, `locI_PlK_refl`: the local pole set of `±[1, K]` at a residue `1 ≤ c < p/2` is an
  integer interval `[-B, A]`, `B - A ∈ {0, 1}`; it is reflection-symmetric exactly when its size is
  even.
-/

open Finset Polynomial

namespace Apery

section pair
variable {p : ℕ} [hp : Fact p.Prime]

lemma cast_sub_p {c : ℕ} (hc : c ≤ p) : (((p - c : ℕ)) : ZMod p) = -((c : ℕ) : ZMod p) := by
  rw [Nat.cast_sub hc, ZMod.natCast_self, zero_sub]

lemma mem_neg_of_sym {Pl : Finset ℤ} (hPl : Pl.image (fun r => -r) = Pl) {r : ℤ} (hr : r ∈ Pl) :
    -r ∈ Pl := by
  rw [← hPl]; exact Finset.mem_image_of_mem _ hr

lemma plc_neg {Pl : Finset ℤ} (hPl : Pl.image (fun r => -r) = Pl) (x : ZMod p) :
    plc p Pl (-x) = (plc p Pl x).image (fun r => -r) := by
  ext r
  simp only [plc, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hr, hx⟩
    refine ⟨-r, ⟨mem_neg_of_sym hPl hr, ?_⟩, neg_neg r⟩
    push_cast; rw [hx, neg_neg]
  · rintro ⟨s, ⟨hs, hx⟩, rfl⟩
    exact ⟨mem_neg_of_sym hPl hs, by push_cast; rw [hx]⟩

lemma plo_pc {Pl : Finset ℤ} (hPl : Pl.image (fun r => -r) = Pl) {c : ℕ} (hc : c ≤ p) :
    plo p Pl (p - c) = (plo p Pl c).image (fun r => -r) := by
  ext r
  simp only [plo, Finset.mem_filter, Finset.mem_image, cast_sub_p hc]
  constructor
  · rintro ⟨hr, hx⟩
    refine ⟨-r, ⟨mem_neg_of_sym hPl hr, fun h => hx ?_⟩, neg_neg r⟩
    push_cast at h; rw [← h, neg_neg]
  · rintro ⟨s, ⟨hs, hx⟩, rfl⟩
    refine ⟨mem_neg_of_sym hPl hs, fun h => hx ?_⟩
    push_cast at h; rw [← neg_neg (s : ZMod p), h, neg_neg]

lemma kloc_pc {Pl : Finset ℤ} {c : ℕ} (hc : c ≤ p) {r : ℤ} (hr : r ∈ plc p Pl (c : ZMod p)) :
    kloc p (p - c) (-r) = refl (kloc p c r) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h := (mem_plc_spec (p := p) hr).2.2
  unfold kloc refl
  have e : -r - ((p - c : ℕ) : ℤ) = (p : ℤ) * (-1 - (r - c) / p) := by
    have h' : r = c + p * ((r - c) / p) := h
    rw [Nat.cast_sub hc]
    linear_combination -h'
  rw [e, Int.mul_ediv_cancel_left _ hp0]

lemma locI_pc {Pl : Finset ℤ} (hPl : Pl.image (fun r => -r) = Pl) {c : ℕ} (hc : c ≤ p) :
    locI p Pl (p - c) = (locI p Pl c).image refl := by
  unfold locI
  rw [cast_sub_p hc, plc_neg hPl, Finset.image_image, Finset.image_image]
  exact Finset.image_congr fun r hr => kloc_pc hc hr

lemma locU_pc {Pl : Finset ℤ} (hPl : Pl.image (fun r => -r) = Pl) {c : ℕ} (hc : c ≤ p) :
    locU p Pl (p - c) = (-1) ^ (plo p Pl c).card * locU p Pl c := by
  unfold locU
  rw [plo_pc hPl hc, Finset.prod_image (fun a _ b _ h => neg_injective h), cast_sub_p hc,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  push_cast; ring

lemma Gc_pc {c : ℕ} (hc : c ≤ p) : Gc p (p - c) = -((Gc p c).comp (-X - 1)) := by
  simp only [Gc, add_comp, mul_comp, C_comp, X_comp]
  rw [Nat.cast_sub hc, C_sub]; ring

lemma locN_pc {A : ℚ[X]} (hA : A.comp (-X) = -A) (e : ℕ) {c : ℕ} (hc : c ≤ p)
    (hN : GV p (C ((p : ℚ) ^ (-(e : ℤ))) * A.comp (Gc p c)) 0) :
    locN p A e (p - c) = -Jr (locN p A e c) := by
  unfold locN
  have h1 : A.comp (Gc p (p - c)) = -((A.comp (Gc p c)).comp (-X - 1)) := by
    rw [Gc_pc hc, show -((Gc p c).comp (-X - 1)) = (-X : ℚ[X]).comp ((Gc p c).comp (-X - 1)) by
      simp, ← comp_assoc, hA, neg_comp, comp_assoc]
  rw [h1, mul_neg, redP_neg, ← redP_Jr hN, mul_comp, C_comp]

/-- **The residues `c` and `p - c` carry the same local symbol.** -/
theorem locSymb_pc (hp5 : 5 ≤ p) {A : ℚ[X]} (hA : A.comp (-X) = -A) (eF : ZMod p → ℕ)
    (hAloc : ∀ m : ℤ, GV p (A.comp (C (m : ℚ) + C (p : ℚ) * X)) (eF (m : ZMod p)))
    (heF : ∀ x, eF (-x) = eF x) {Pl : Finset ℤ} (hPl : Pl.image (fun r => -r) = Pl)
    (hev : Even Pl.card) (β : ℤ) {c : ℕ} (hcp : c < p)
    (hI : tind p eF Pl β c ≠ 0 →
      (locI p Pl c).image refl = locI p Pl c ∧ Even (locI p Pl c).card) :
    locSymb p A eF Pl β (p - c) = locSymb p A eF Pl β c := by
  have hc : c ≤ p := hcp.le
  have htind : tind p eF Pl β (p - c) = tind p eF Pl β c := by
    unfold tind
    rw [cast_sub_p hc, heF, plc_neg hPl, Finset.card_image_of_injective _ neg_injective]
  by_cases ht : tind p eF Pl β c = 0
  · unfold locSymb; rw [htind, ht]; simp
  obtain ⟨hsym, hevI⟩ := hI ht
  unfold locSymb
  rw [htind, locI_pc hPl hc, hsym, locU_pc hPl hc, cast_sub_p hc, heF,
    locN_pc hA _ hc (GV_locNum (hAloc_nat hAloc c))]
  have hneg : locSym p (locI p Pl c) (-Jr (locN p A (eF (c : ZMod p)) c)) =
      -locSym p (locI p Pl c) (Jr (locN p A (eF (c : ZMod p)) c)) :=
    (locL p (locI p Pl c)).map_neg _
  rw [hneg, locSym_Jr hp5 hsym hevI, neg_neg]
  have hcard : (plo p Pl c).card + (locI p Pl c).card = Pl.card := by
    rw [card_locI]; unfold plo plc
    rw [add_comm]; exact Finset.card_filter_add_card_filter_not _
  have hevo : Even (plo p Pl c).card := by
    have := (Nat.even_add.mp (hcard ▸ hev))
    exact this.mpr hevI
  rw [hevo.neg_one_pow, one_mul]

/-- Pairing of the residues `c ↔ p - c`. -/
lemma sum_range_pair {M : Type*} [AddCommMonoid M] {m : ℕ} (hm : 2 * m + 1 = p) (f : ℕ → M)
    (hf : ∀ c, 1 ≤ c → c ≤ m → f (p - c) = f c) :
    ∑ c ∈ range p, f c = f 0 + 2 • ∑ a ∈ Icc 1 m, f a := by
  have hshift : ∀ n, ∑ i ∈ range n, f (i + 1) = ∑ j ∈ Icc 1 n, f j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
  subst hm
  rw [Finset.sum_range_succ', show 2 * m = m + m by ring, Finset.sum_range_add, add_comm,
    ← hshift m, two_nsmul]
  congr 1
  congr 1
  rw [← Finset.sum_range_reflect (fun i => f (i + 1)) m]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have := hf (m - i) (by omega) (by omega)
  rw [show 2 * m + 1 - (m - i) = m + i + 1 by omega] at this
  rw [show m + i + 1 = m + i + 1 from rfl, this, show m - 1 - i + 1 = m - i by omega]

/-! ### The local pole intervals of `±[1, K]` -/

lemma mem_PlK_Icc (K : ℕ) (r : ℤ) :
    r ∈ PlK K ↔ (1 ≤ r ∧ r ≤ K) ∨ (-(K : ℤ) ≤ r ∧ r ≤ -1) := by
  unfold PlK
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro (⟨j, ⟨h1, h2⟩, rfl⟩ | ⟨j, ⟨h1, h2⟩, rfl⟩)
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; exact ⟨r.toNat, ⟨by omega, by omega⟩, by omega⟩
    · right; exact ⟨(-r).toNat, ⟨by omega, by omega⟩, by omega⟩

lemma mem_locI_iff {Pl : Finset ℤ} {c : ℕ} (k : ℤ) :
    k ∈ locI p Pl c ↔ (c : ℤ) + p * k ∈ Pl := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold locI
  rw [Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have h := mem_plc_spec (p := p) hr
    rw [← h.2.2]; exact h.1
  · intro h
    refine ⟨(c : ℤ) + p * k, ?_, ?_⟩
    · unfold plc; rw [Finset.mem_filter]; refine ⟨h, ?_⟩; simp
    · unfold kloc; rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hp0]

/-- The local pole set of `±[1, K]` at `1 ≤ c`, `2c < p` is `[-B, A]`. -/
lemma mem_locI_PlK {K c : ℕ} (hc1 : 1 ≤ c) (hcp : 2 * c < p) (k : ℤ) :
    k ∈ locI p (PlK K) c ↔ -(((K : ℤ) + c) / p) ≤ k ∧ k ≤ ((K : ℤ) - c) / p := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hcp' : 2 * (c : ℤ) < p := by exact_mod_cast hcp
  have hc1' : (1 : ℤ) ≤ c := by exact_mod_cast hc1
  have e1 : k ≤ ((K : ℤ) - c) / p ↔ k * p ≤ (K : ℤ) - c := Int.le_ediv_iff_mul_le hp0
  have e2 : -(((K : ℤ) + c) / p) ≤ k ↔ (-k) * p ≤ (K : ℤ) + c := by
    rw [neg_le, Int.le_ediv_iff_mul_le hp0]
  rw [mem_locI_iff, mem_PlK_Icc, e1, e2]
  rcases le_or_gt 0 k with hk | hk
  · have h1 : 0 ≤ (p : ℤ) * k := mul_nonneg hp0.le hk
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · constructor <;> nlinarith
      · omega
    · rintro ⟨_, h⟩; left; constructor <;> nlinarith
  · have h1 : (p : ℤ) * k ≤ -p := by nlinarith
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · omega
      · constructor <;> nlinarith
    · rintro ⟨h, _⟩; right; constructor <;> nlinarith

/-- **Even local pole intervals are centred.** -/
lemma locI_PlK_refl {K c : ℕ} (hc1 : 1 ≤ c) (hcp : 2 * c < p)
    (hev : Even (locI p (PlK K) c).card) : (locI p (PlK K) c).image refl = locI p (PlK K) c := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  set A := ((K : ℤ) - c) / p with hA
  set B := ((K : ℤ) + c) / p with hB
  have hI : locI p (PlK K) c = Finset.Icc (-B) A := by
    ext k; rw [mem_locI_PlK hc1 hcp, Finset.mem_Icc]
  -- `B - A ∈ {0, 1}`
  have hcp' : 2 * (c : ℤ) < p := by exact_mod_cast hcp
  have hBA : A ≤ B ∧ B ≤ A + 1 := by
    have h1 := Int.ediv_mul_le ((K : ℤ) - c) hp0.ne'
    have h2 := Int.lt_ediv_add_one_mul_self ((K : ℤ) - c) hp0
    have h3 := Int.ediv_mul_le ((K : ℤ) + c) hp0.ne'
    have h4 := Int.lt_ediv_add_one_mul_self ((K : ℤ) + c) hp0
    rw [← hA] at h1 h2; rw [← hB] at h3 h4
    constructor
    · by_contra h
      have h' : B + 1 ≤ A := by omega
      have : (B + 1) * p ≤ A * p := by nlinarith
      nlinarith
    · by_contra h
      have h' : A + 2 ≤ B := by omega
      have : (A + 2) * p ≤ B * p := by nlinarith
      nlinarith
  rw [hI, Int.card_Icc] at hev
  rw [hI]
  rcases (show B = A ∨ B = A + 1 by omega) with h | h
  · -- `B = A`: the interval is empty
    have hA0 : A < 0 := by
      by_contra hpos
      have hpos' : 0 ≤ 2 * A + 1 := by omega
      rw [h, show A + 1 - -A = 2 * A + 1 by ring] at hev
      rcases hev with ⟨t, ht⟩
      have h1 := congrArg (fun x : ℕ => (x : ℤ)) ht
      have h2 := Int.toNat_of_nonneg hpos'
      push_cast at h1
      omega
    have hemp : Finset.Icc (-B) A = ∅ := by
      ext k; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [hemp, Finset.image_empty]
  · ext k
    simp only [Finset.mem_image, Finset.mem_Icc, refl]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩; constructor <;> omega
    · rintro ⟨h1, h2⟩; exact ⟨-1 - k, ⟨by omega, by omega⟩, by ring⟩

end pair

end Apery
