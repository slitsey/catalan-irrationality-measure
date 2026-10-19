module

public import CatalanFrames.HybCommon.Pieces
public import CatalanCore.Arith.Hybrid.D1Exact
public import CatalanCore.Arith.Hybrid.Values

@[expose] public section

/-!
# Hybrid tropical content, generic in the offset `o` (class dictionary)

Everything that was `lamInst`-specific in `CatalanFrames/Lambda/HybBounds, HybPieces, HybD1Pieces` is
stated for an instance `I : HybInst Fr` satisfying `TropFacts I o`:
the class `j = 1` is `p ≡ 4 - o (mod 4)` with `kq p = (p + o)/4`, the class `j = 3` is `p ≡ o (mod 4)`
with `kq p = (3p + o)/4`.  The piece tables (`l3`, `l1`, `ld1` of `HybContent8`) are frame-free; their
covers hold for both offsets with the same constants.  For `o = 1` the class `j = 1` is `3 mod 4`, for
`o = 3` it is `1 mod 4`: the residue classes are swapped.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- The facts about a hybrid instance used by the tropical piece tables. -/
structure TropFacts (I : HybInst Fr) (o : ℕ) : Prop where
  ho : o = 1 ∨ o = 3
  kq3 : ∀ p, p.Prime → 5 ≤ p → p % 4 = o → I.cd.kq p = (3 * p + o) / 4
  kq1 : ∀ p, p.Prime → 5 ≤ p → p % 4 = 4 - o → I.cd.kq p = (p + o) / 4
  good : ∀ p, p.Prime → 5 ≤ p → IsPrimePow p ∧ ∀ q ∈ I.cd.bad, ¬ q ∣ p
  zero_iff : ∀ q c, IsPrimePow q → (∀ p ∈ I.cd.bad, ¬ p ∣ q) → (I.lev q c = 0 ↔ c < I.cd.kq q)
  high : ∀ q c, 1 ≤ q → q ≤ c → 0 < I.lev q c

/-- The level-1 tropical value of the hybrid at `(r, ⌊r/8⌋)` and the prime `p`. -/
noncomputable def XG (I : HybInst Fr) (r p : ℕ) : ℕ := tropVal (HW I.lev p r (r / 8))

/-- The weight function of the summation. -/
noncomputable def WG (I : HybInst Fr) (r p : ℕ) : ℝ := (XG I r p : ℝ)

/-- The residue class of the primes with `j = 1`. -/
def cJ1 (o : ℕ) : ZMod 4 := ((4 - o : ℕ) : ZMod 4)
/-- The residue class of the primes with `j = 3`. -/
def cJ3 (o : ℕ) : ZMod 4 := (o : ZMod 4)

section Dual

variable {I : HybInst Fr} {o : ℕ} (T : TropFacts I o)
include T

lemma XG_D1 (r p : ℕ) : XG I r p ≤ 2 * (r + r / 8) := by
  have h := trop_D1 (lev := I.lev) p r (r / 8)
  have : (XG I r p : ℚ) ≤ ((2 * (r + r / 8) : ℕ) : ℚ) := by push_cast; exact h
  exact_mod_cast this

lemma XG_D3 (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hl : r / 4 < p) (hu : p ≤ r) :
    XG I r p ≤ 2 * r + r / 8 :=
  val_D3 p r (r / 8) (lev := I.lev) hp.one_lt.le
    (fun c hc => T.high p c hp.one_lt.le hc) (by omega) hu

lemma XG_kq_le (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : I.cd.kq p ≤ p := by
  have hodd := hp.eq_two_or_odd
  rcases T.ho with rfl | rfl
  · by_cases h : p % 4 = 1
    · rw [T.kq3 p hp h5 h]; omega
    · rw [T.kq1 p hp h5 (by omega)]; omega
  · by_cases h : p % 4 = 3
    · rw [T.kq3 p hp h5 h]; omega
    · rw [T.kq1 p hp h5 (by omega)]; omega

lemma XG_D2 (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hl : r / 4 < p) (hu : p ≤ r) :
    ∃ u L : ℕ, I.cd.kq p + p ≤ u + r ∧ u ≤ r ∧ L ≤ u ∧ L ≤ 2 * (r / 8) ∧
      XG I r p ≤ 2 * (r - u) + 2 * (r / 8) + L := by
  obtain ⟨hq, hb⟩ := T.good p hp h5
  have hk : I.cd.kq p ≤ r := (XG_kq_le T p hp h5).trans hu
  exact val_D2 p r (r / 8) (I.cd.kq p) (lev := I.lev) hp.one_lt.le
    (fun c hc => T.high p c hp.one_lt.le hc) (by omega) hu hk
    (fun c => T.zero_iff p c hq hb)

lemma XG_D45 (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hr : r < p) :
    XG I r p ≤ 2 * (r - I.cd.kq p) + 2 * (r / 8) + (2 * (r / 8) - (p - r)) := by
  obtain ⟨hq, hb⟩ := T.good p hp h5
  exact val_D45 p r (r / 8) (I.cd.kq p) (lev := I.lev) hr (by omega)
    (fun c => T.zero_iff p c hq hb)

lemma XG_D6 (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hN : r + 2 * (r / 8) ≤ p)
    (hk : r ≤ I.cd.kq p) : XG I r p ≤ 2 * (r / 8) - (I.cd.kq p - r) := by
  obtain ⟨hq, hb⟩ := T.good p hp h5
  exact val_D6 p r (r / 8) (I.cd.kq p) (lev := I.lev) hN hk
    (fun c => T.zero_iff p c hq hb)

lemma XG_D1x (r p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    XG I r p ≤ 2 * r + 2 * (r / 8) - min ((r / 8) % p) (p - (r / 8) % p) := by
  have hodd : p % 2 = 1 := by have := hp.eq_two_or_odd; omega
  exact val_D1x p r (lev := I.lev) hodd hp.pos (r / 8)

lemma mod_j1 {p : ℕ} (hc : (p : ZMod 4) = cJ1 o) : p % 4 = 4 - o := by
  rcases T.ho with rfl | rfl
  · exact cls4_mod3 (by simpa [cJ1] using hc)
  · exact cls4_mod1 (by simpa [cJ1] using hc)

lemma mod_j3 {p : ℕ} (hc : (p : ZMod 4) = cJ3 o) : p % 4 = o := by
  rcases T.ho with rfl | rfl
  · exact cls4_mod1 (by simpa [cJ3] using hc)
  · exact cls4_mod3 (by simpa [cJ3] using hc)

end Dual

section Covers

variable {I : HybInst Fr} {o : ℕ}

theorem cj1_1 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WG I r) r (mkPiece 1 4 9 10 17 (0) 64 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq1 p hp h5 hm
  have hb := XG_D3 T r p hp h5 (by omega) (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 8 17 (0) 64 (by norm_num) (by omega)

theorem cj1_2 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WG I r) r (mkPiece 9 10 1 1 13 (-5) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq1 p hp h5 hm
  obtain ⟨u, L, h1', h4, h5', h6, hb⟩ := XG_D2 T r p hp h5 (by omega) (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 4 13 (-5) 32 (by norm_num) (by omega)

theorem cj1_3 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WG I r) r (mkPiece 1 1 5 4 7 (-3) 32 2) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq1 p hp h5 hm
  have hb := XG_D45 T r p hp h5 (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 2 7 (-3) 32 (by norm_num) (by omega)

theorem cj1_4 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WG I r) r (mkPiece 5 4 4 1 9 (-2) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq1 p hp h5 hm
  have hb := XG_D45 T r p hp h5 (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 4 9 (-2) 32 (by norm_num) (by omega)

theorem cj1_5 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WG I r) r (mkPiece 4 1 5 1 5 (-1) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq1 p hp h5 hm
  have hb := XG_D6 T r p hp h5 (by omega) (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 4 5 (-1) 32 (by norm_num) (by omega)

theorem cj3_1 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WG I r) r (mkPiece 1 4 9 14 17 (0) 64 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq3 p hp h5 hm
  have hb := XG_D3 T r p hp h5 (by omega) (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 8 17 (0) 64 (by norm_num) (by omega)

theorem cj3_2 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WG I r) r (mkPiece 9 14 5 7 13 (-7) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq3 p hp h5 hm
  obtain ⟨u, L, h1', h4, h5', h6, hb⟩ := XG_D2 T r p hp h5 (by omega) (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 4 13 (-7) 32 (by norm_num) (by omega)

theorem cj3_3 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WG I r) r (mkPiece 5 7 1 1 9 (-7) 16 2) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq3 p hp h5 hm
  obtain ⟨u, L, h1', h4, h5', h6, hb⟩ := XG_D2 T r p hp h5 (by omega) (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 2 9 (-7) 16 (by norm_num) (by omega)

theorem cj3_4 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WG I r) r (mkPiece 1 1 5 4 7 (-5) 16 2) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq3 p hp h5 hm
  have hb := XG_D45 T r p hp h5 (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 2 7 (-5) 16 (by norm_num) (by omega)

theorem cj3_5 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WG I r) r (mkPiece 5 4 4 3 9 (-6) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq3 p hp h5 hm
  have hb := XG_D45 T r p hp h5 (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 4 9 (-6) 32 (by norm_num) (by omega)

theorem cj3_6 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WG I r) r (mkPiece 4 3 5 3 5 (-3) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have h5 : 5 ≤ p := by omega
  have hk := T.kq3 p hp h5 hm
  have hb := XG_D6 T r p hp h5 (by omega) (by omega)
  show (XG I r p : ℝ) ≤ _
  rcases T.ho with rfl | rfl <;>
    exact real_of_int_bound 4 5 (-3) 32 (by norm_num) (by omega)

theorem d1g_0 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 68 1 64 17 (64) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 8 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (64) 320 (by norm_num) (by omega)

theorem d1g_1 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 64 1 60 19 (-64) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 7 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-64) 320 (by norm_num) (by omega)

theorem d1g_2 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 60 1 56 17 (56) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 7 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (56) 320 (by norm_num) (by omega)

theorem d1g_3 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 56 1 52 19 (-56) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 6 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-56) 320 (by norm_num) (by omega)

theorem d1g_4 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 52 1 48 17 (48) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 6 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (48) 320 (by norm_num) (by omega)

theorem d1g_5 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 48 1 44 19 (-48) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 5 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-48) 320 (by norm_num) (by omega)

theorem d1g_6 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 44 1 40 17 (40) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 5 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (40) 320 (by norm_num) (by omega)

theorem d1g_7 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 40 1 36 19 (-40) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 4 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-40) 320 (by norm_num) (by omega)

theorem d1g_8 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 36 1 32 17 (32) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 4 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (32) 320 (by norm_num) (by omega)

theorem d1g_9 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 32 1 28 19 (-32) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 3 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-32) 320 (by norm_num) (by omega)

theorem d1g_10 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 28 1 24 17 (24) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 3 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (24) 320 (by norm_num) (by omega)

theorem d1g_11 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 24 1 20 19 (-24) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 2 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-24) 320 (by norm_num) (by omega)

theorem d1g_12 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 20 1 16 17 (16) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 2 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (16) 320 (by norm_num) (by omega)

theorem d1g_13 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 16 1 12 19 (-16) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 1 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-16) 320 (by norm_num) (by omega)

theorem d1g_14 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 12 1 8 17 (8) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 1 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (8) 320 (by norm_num) (by omega)

theorem d1g_15 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (WG I r) r (mkPiece 1 8 1 4 19 (-8) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := XG_D1x T r p hp h2
  have hd := dist_ge p (r / 8) 0 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (XG I r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-8) 320 (by norm_num) (by omega)

end Covers

end CatalanFrames.HybCommon
