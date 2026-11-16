module

public import CatalanCore.Zeta5.Padic.Entry
public import CatalanCore.Zeta5.Content.Parity

@[expose] public section

/-!
# ZC06(b), part 7: the tight residues of a centred entry (step E2)

In the inner range (`InnerHyp`), fix an even group `S = {a ≠ 0 : ℓ_K(a) even}` (`parS`) and two
rows `s, t` with classes in `S`; put `β = w_s + w_t + 4` (an integer).

* `gap_nz`: at a class `a ≠ 0`, `2 ν_u(a) + B(a) - 4 - 2 w_u` is a nonnegative integer, zero exactly
  when `ℓ_K(a)` is even and `tcond a u` (`u.1 = a`, or `a ∉ ε`, `u.1 ∈ ε` and `u` is the top row).
* `gap_zero`: at the zero class the same quantity is positive.
* `tind_zero`, `tind_class`: the residue `0` is never tight; a class `a ≠ 0` is tight iff
  `ℓ_K(a)` even `∧ tcond a s ∧ tcond a t`.
* `sum_locSymb_entry`: `∑_{c < p} locSymb(c) = 2 ∑_{a ∈ S, tight} ū_K(a)⁻¹ locSym(I^K_a, ā_a)`.
-/

open Finset Polynomial

namespace Apery

/-- the tightness condition of a row `u` at the class `a`. -/
def tcond (p n L0 : ℕ) (a : Fin (p / 2 + 1)) (u : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b)) :
    Prop :=
  u.1 = a ∨ (a ∉ epsSet p n L0 ∧ u.1 ∈ epsSet p n L0 ∧ (u.2 : ℕ) + 1 = innerL p n L0 u.1)

noncomputable instance (p n L0 : ℕ) (a : Fin (p / 2 + 1)) (u : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b)) :
    Decidable (tcond p n L0 a u) := by
  unfold tcond; infer_instance

lemma PlK_neg (K : ℕ) : (PlK K).image (fun r => -r) = PlK K := by
  ext r
  simp only [Finset.mem_image, mem_PlK_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩; omega
  · intro h; exact ⟨-r, by omega, by ring⟩

namespace InnerHyp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0)
include H

lemma p5 : 5 ≤ p := by have := H.p200; have := H.hM; omega

lemma Bse_nz (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    Bse p (40 * n) (3 * n) a = 2 * (innerT p n L0 : ℚ) + 2 * (if a ∈ epsSet p n L0 then 1 else 0)
      - 2 * (innerL p n L0 a : ℚ) - (lK p n a : ℚ) := by
  have hna : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
  have h := H.innerL_spec a ha
  have h' : ((innerL p n L0 a : ℕ) : ℚ) + 3 * (lN p n a : ℚ) =
      (innerT p n L0 : ℚ) + (if a ∈ epsSet p n L0 then 1 else 0) := by
    have h2 := h
    split_ifs at h2 ⊢ <;> exact_mod_cast h2
  unfold Bse
  rw [if_neg hna]
  unfold lN at h'
  unfold lK
  push_cast at h' ⊢
  linarith

lemma winner_nz (u : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b)) (hu : u.1 ≠ 0) :
    winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) u =
      (u.2 : ℕ) + (Bse p (40 * n) (3 * n) u.1 - 4) / 2 := by
  unfold winner; rw [if_neg hu]

/-- **E2 at a class `a ≠ 0`.** -/
lemma gap_nz (a : Fin (p / 2 + 1)) (ha : a ≠ 0)
    (u : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b)) (hu : u.1 ∈ parS p n) :
    ∃ X : ℤ, 2 * (nu (innerL p n L0) u a : ℚ) + Bse p (40 * n) (3 * n) a - 4 -
        2 * winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) u = X ∧ 0 ≤ X ∧
      (X = 0 ↔ lK p n a % 2 = 0 ∧ tcond p n L0 a u) := by
  have hu' := (Finset.mem_filter.mp hu).2
  have hu0 : u.1 ≠ 0 := hu'.1
  have hℓ : lK p n u.1 % 2 = 0 := hu'.2
  have hw := H.winner_nz u hu0
  have hlt : (u.2 : ℕ) < innerL p n L0 u.1 := u.2.isLt
  by_cases hau : u.1 = a
  · subst hau
    refine ⟨0, ?_, le_refl _, ?_⟩
    · rw [hw]; unfold nu; rw [if_pos rfl]; push_cast; ring
    · simp [tcond, hℓ]
  · have hnu : nu (innerL p n L0) u a = innerL p n L0 a := by
      unfold nu; rw [if_neg (fun h => hau h.symm)]
    have hBa := H.Bse_nz a ha
    have hBu := H.Bse_nz u.1 hu0
    have c1 := H.lK_consec a u.1 ha hu0
    have c2 := H.lK_consec u.1 a hu0 ha
    obtain ⟨_, _, htop⟩ := H.epsSet_spec
    have hmem : a ∈ (Finset.univ : Finset (Fin (p / 2 + 1))).erase 0 :=
      Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
    by_cases hA : a ∈ epsSet p n L0 <;> by_cases hU : u.1 ∈ epsSet p n L0
    · refine ⟨2 - lK p n a - 2 * (u.2 : ℕ) - 2 + 2 * innerL p n L0 u.1 + lK p n u.1, ?_, ?_, ?_⟩
      · rw [hw, hnu, hBa, hBu, if_pos hA, if_pos hU]; push_cast; ring
      · omega
      · simp only [tcond, hau, hA, hU, false_or, not_true_eq_false, false_and, and_false,
          iff_false]
        omega
    · refine ⟨2 - lK p n a - 2 * (u.2 : ℕ) - 0 + 2 * innerL p n L0 u.1 + lK p n u.1, ?_, ?_, ?_⟩
      · rw [hw, hnu, hBa, hBu, if_pos hA, if_neg hU]; push_cast; ring
      · omega
      · simp only [tcond, hau, hA, hU, false_or, not_true_eq_false, false_and, and_false,
          iff_false]
        omega
    · have htop' := htop u.1 hU a hmem hA
      refine ⟨0 - lK p n a - 2 * (u.2 : ℕ) - 2 + 2 * innerL p n L0 u.1 + lK p n u.1, ?_, ?_, ?_⟩
      · rw [hw, hnu, hBa, hBu, if_neg hA, if_pos hU]; push_cast; ring
      · omega
      · simp only [tcond, hau, hA, hU, false_or, not_false_eq_true, true_and]
        omega
    · refine ⟨0 - lK p n a - 2 * (u.2 : ℕ) - 0 + 2 * innerL p n L0 u.1 + lK p n u.1, ?_, ?_, ?_⟩
      · rw [hw, hnu, hBa, hBu, if_neg hA, if_neg hU]; push_cast; ring
      · omega
      · simp only [tcond, hau, hA, hU, false_or, false_and, and_false, iff_false]
        omega

/-- **E2 at the zero class** (strict form of `inner_Z`). -/
lemma gap_zero (u : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b)) (hu0 : u.1 ≠ 0) :
    0 < 4 * (nu (innerL p n L0) u 0 : ℚ) + Bse p (40 * n) (3 * n) 0 - 4 -
        2 * winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) u := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have hnu : nu (innerL p n L0) u 0 = L0 := by
    unfold nu; rw [if_neg (fun h => hu0 h.symm), H.innerL_zero]
  have hw := H.winner_nz u hu0
  have hBu := H.Bse_nz u.1 hu0
  have hB : Bse p (40 * n) (3 * n) 0 =
      5 + 6 * ((3 * n / p : ℕ) * 2 : ℕ) - ((40 * n / p : ℕ) * 2 : ℕ) := by
    unfold Bse
    simp only [if_true, Nat.cast_zero, Int.cast_zero, SX_zero]
    push_cast; ring
  have hlt : ((u.2 : ℕ) : ℚ) + 1 ≤ innerL p n L0 u.1 := by
    have := u.2.isLt; exact_mod_cast this
  have hT : (innerT p n L0 : ℚ) ≤ 3 * M := by exact_mod_cast H.innerT_le
  have hmK : ((40 * n / p : ℕ) : ℚ) + 1 ≤ M := by exact_mod_cast H.mK_lt
  have hL : (2 * M : ℚ) ≤ L0 := by exact_mod_cast H.hL0a
  have hmN : (0 : ℚ) ≤ ((3 * n / p : ℕ) : ℚ) := Nat.cast_nonneg _
  have hlK : (0 : ℚ) ≤ lK p n u.1 := Nat.cast_nonneg _
  have hε : (0 : ℚ) ≤ (if u.1 ∈ epsSet p n L0 then (1 : ℚ) else 0) ∧
      (if u.1 ∈ epsSet p n L0 then (1 : ℚ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [hnu, hw, hBu, hB]
  push_cast
  nlinarith [hε.1, hε.2]

/-- the weights of rows in an even group are integers. -/
lemma winner_int (u : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b))
    (hu : u.1 ∈ parS p n) :
    ∃ z : ℤ, winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) u = z := by
  have hu' := (Finset.mem_filter.mp hu).2
  obtain ⟨j, hj⟩ : ∃ j, lK p n u.1 = 2 * j := ⟨lK p n u.1 / 2, by omega⟩
  have hBu := H.Bse_nz u.1 hu'.1
  rw [hj] at hBu
  refine ⟨(u.2 : ℕ) + innerT p n L0 + (if u.1 ∈ epsSet p n L0 then 1 else 0) -
    innerL p n L0 u.1 - j - 2, ?_⟩
  rw [H.winner_nz u hu'.1, hBu]
  split_ifs <;> push_cast <;> ring

lemma ccls_fin (a : Fin (p / 2 + 1)) :
    haveI : Fact p.Prime := ⟨H.prime⟩
    ccls H.p_odd (((a : ℕ) : ZMod p)) = a := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  exact (ccls_unique H.p_odd _ a (Or.inl (by push_cast; rfl))).symm

/-- the tightness test in rational form. -/
lemma tind_iff (s t : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b)) (β : ℤ)
    (hβ : (β : ℚ) = winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s +
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) t + 4) (c : ZMod p) :
    haveI : Fact p.Prime := ⟨H.prime⟩
    ((entF p (3 * n) (innerL p n L0) s t c : ℤ) - (plc p (PlK (40 * n)) c).card = β ↔
      classCount p (40 * n) (entryRoots (3 * n) (innerL p n L0) s t) c =
        winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s +
        winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) t + 4) := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  rw [← entF_sub (40 * n), ← hβ]
  constructor
  · intro h
    have := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at this; linarith
  · intro h
    have : (((entF p (3 * n) (innerL p n L0) s t c : ℤ) - (plc p (PlK (40 * n)) c).card : ℤ) : ℚ)
        = (β : ℚ) := by push_cast; linarith
    exact_mod_cast this

/-- **The residue `0` is never tight.** -/
lemma tind_zero (s t : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b))
    (hs : s.1 ∈ parS p n) (ht : t.1 ∈ parS p n) (β : ℤ)
    (hβ : (β : ℚ) = winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s +
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) t + 4) :
    haveI : Fact p.Prime := ⟨H.prime⟩
    tind p (entF p (3 * n) (innerL p n L0) s t) (PlK (40 * n)) β 0 = 0 := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  unfold tind
  rw [if_neg]
  rw [show (((0 : ℕ)) : ZMod p) = 0 by simp, H.tind_iff s t β hβ 0, classCount_eq H.p_odd]
  have hc : ccls H.p_odd (0 : ZMod p) = 0 := (ccls_eq_zero_iff H.p_odd 0).mpr rfl
  rw [hc, if_pos rfl]
  have g1 := H.gap_zero s (Finset.mem_filter.mp hs).2.1
  have g2 := H.gap_zero t (Finset.mem_filter.mp ht).2.1
  intro h
  rw [Fin.val_zero] at h
  push_cast at h
  linarith

/-- **The tight classes.** -/
lemma tind_class (s t : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b))
    (hs : s.1 ∈ parS p n) (ht : t.1 ∈ parS p n) (β : ℤ)
    (hβ : (β : ℚ) = winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s +
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) t + 4)
    (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    haveI : Fact p.Prime := ⟨H.prime⟩
    tind p (entF p (3 * n) (innerL p n L0) s t) (PlK (40 * n)) β (a : ℕ) =
      if lK p n a % 2 = 0 ∧ tcond p n L0 a s ∧ tcond p n L0 a t then 1 else 0 := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  obtain ⟨Xs, hXs, hXs0, hXsi⟩ := H.gap_nz a ha s hs
  obtain ⟨Xt, hXt, hXt0, hXti⟩ := H.gap_nz a ha t ht
  have hiff : ((entF p (3 * n) (innerL p n L0) s t (((a : ℕ) : ZMod p)) : ℤ) -
      (plc p (PlK (40 * n)) (((a : ℕ) : ZMod p))).card = β) ↔
      (lK p n a % 2 = 0 ∧ tcond p n L0 a s ∧ tcond p n L0 a t) := by
    rw [H.tind_iff s t β hβ, classCount_eq H.p_odd, H.ccls_fin, if_neg ha]
    have key : (Bse p (40 * n) (3 * n) a + 1 * ((nu (innerL p n L0) s a : ℚ) +
        nu (innerL p n L0) t a) = winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s +
          winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) t + 4) ↔ Xs + Xt = 0 := by
      constructor
      · intro h
        have : ((Xs + Xt : ℤ) : ℚ) = 0 := by push_cast; linarith
        exact_mod_cast this
      · intro h
        have : ((Xs + Xt : ℤ) : ℚ) = 0 := by exact_mod_cast h
        push_cast at this; linarith
    rw [key, show Xs + Xt = 0 ↔ Xs = 0 ∧ Xt = 0 by omega, hXsi, hXti]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨_, h3⟩⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, ⟨h1, h3⟩⟩
  unfold tind
  by_cases hc : lK p n a % 2 = 0 ∧ tcond p n L0 a s ∧ tcond p n L0 a t
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]

/-- **The pairing hypothesis**: a tight class has a symmetric local pole set of even size. -/
lemma tight_sym (s t : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b))
    (hs : s.1 ∈ parS p n) (ht : t.1 ∈ parS p n) (β : ℤ)
    (hβ : (β : ℚ) = winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s +
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) t + 4)
    (c : ℕ) (hc1 : 1 ≤ c) (hcm : c ≤ p / 2) :
    haveI : Fact p.Prime := ⟨H.prime⟩
    tind p (entF p (3 * n) (innerL p n L0) s t) (PlK (40 * n)) β c ≠ 0 →
      (locI p (PlK (40 * n)) c).image refl = locI p (PlK (40 * n)) c ∧
        Even (locI p (PlK (40 * n)) c).card := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  intro hne
  set a : Fin (p / 2 + 1) := ⟨c, by omega⟩ with ha
  have ha0 : a ≠ 0 := fun h => by
    have := congrArg Fin.val h; simp [ha] at this; omega
  have h := H.tind_class s t hs ht β hβ a ha0
  have hlK : lK p n a % 2 = 0 := by
    by_contra hne'
    have hn : ¬ (lK p n a % 2 = 0 ∧ tcond p n L0 a s ∧ tcond p n L0 a t) := fun h => hne' h.1
    rw [if_neg hn] at h
    exact hne h
  have hcard : (locI p (PlK (40 * n)) c).card = lK p n a := by
    rw [card_locI, card_plc_PlK]
    unfold lK; simp [ha]
  have hev : Even (locI p (PlK (40 * n)) c).card := by
    rw [hcard]; exact Nat.even_iff.mpr hlK
  have hp := H.p_odd
  exact ⟨locI_PlK_refl hc1 (by omega) hev, hev⟩

/-- **E2: the sum over residues.** -/
theorem sum_locSymb_entry (s t : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b))
    (hs : s.1 ∈ parS p n) (ht : t.1 ∈ parS p n) (β : ℤ)
    (hβ : (β : ℚ) = winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s +
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) t + 4) :
    haveI : Fact p.Prime := ⟨H.prime⟩
    ∑ c ∈ range p, locSymb p (entA p (40 * n) (3 * n) (innerL p n L0) s t)
        (entF p (3 * n) (innerL p n L0) s t) (PlK (40 * n)) β c =
      2 * ∑ a ∈ parS p n, if tcond p n L0 a s ∧ tcond p n L0 a t then
        (locU p (PlK (40 * n)) a)⁻¹ * locSym p (locI p (PlK (40 * n)) a)
          (locN p (entA p (40 * n) (3 * n) (innerL p n L0) s t)
            (entF p (3 * n) (innerL p n L0) s t (((a : ℕ) : ZMod p))) a) else 0 := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have hp5 := H.p5
  set f : ℕ → ZMod p := fun c => locSymb p (entA p (40 * n) (3 * n) (innerL p n L0) s t)
    (entF p (3 * n) (innerL p n L0) s t) (PlK (40 * n)) β c with hf
  have hpair : ∀ c, 1 ≤ c → c ≤ p / 2 → f (p - c) = f c := by
    intro c hc1 hcm
    simp only [hf]
    exact locSymb_pc hp5 (entA_odd _ _ _ _ _) _ (entF_hAloc (by omega) _ _ _ _ _)
      (entF_neg _ _ _ _) (PlK_neg _) (by rw [card_PlK]; exact even_two_mul _) β
      (by have := H.p_odd; omega) (H.tight_sym s t hs ht β hβ c hc1 hcm)
  rw [sum_range_pair H.p_odd f hpair]
  have h0 : f 0 = 0 := by
    simp only [hf, locSymb]
    rw [H.tind_zero s t hs ht β hβ]; ring
  rw [h0, zero_add, two_nsmul, ← two_mul]
  congr 1
  -- reindex `Icc 1 m` by the nonzero classes
  have himg : (Finset.univ.erase (0 : Fin (p / 2 + 1))).image (fun a : Fin (p / 2 + 1) => (a : ℕ)) = Icc 1 (p / 2) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
      have := a.isLt
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨⟨c, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega, rfl⟩
  rw [← himg, Finset.sum_image (fun a _ b _ h => Fin.ext h)]
  have hsub : parS p n ⊆ Finset.univ.erase 0 := fun a ha =>
    Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp ha).2.1, Finset.mem_univ _⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := (Finset.mem_filter.mp ha).2
    simp only [hf, locSymb]
    rw [H.tind_class s t hs ht β hβ a ha'.1]
    by_cases hc : tcond p n L0 a s ∧ tcond p n L0 a t
    · rw [if_pos ⟨ha'.2, hc⟩, if_pos hc]; ring
    · have hn : ¬ (lK p n a % 2 = 0 ∧ tcond p n L0 a s ∧ tcond p n L0 a t) := fun h => hc h.2
      rw [if_neg hn, if_neg hc]; ring
  · intro a ha hna
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have hlK : ¬ lK p n a % 2 = 0 := fun h => hna (by
      unfold parS; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha0, h⟩)
    simp only [hf, locSymb]
    have hn : ¬ (lK p n a % 2 = 0 ∧ tcond p n L0 a s ∧ tcond p n L0 a t) := fun h => hlK h.1
    rw [H.tind_class s t hs ht β hβ a ha0, if_neg hn]
    ring

end InnerHyp

end Apery
