module

public import CatalanFrames.Lambda.HybPieces
public import CatalanCore.Arith.Hybrid.D1Exact

@[expose] public section

/-!
# λ: the exact D1 pieces on `(1/68, 1/4]` (truncation `K = 8`)

For an odd prime `p`, `lamX r p ≤ 2r + 2m - dist (m, pℤ)` (`val_D1x`) with `m = ⌊r/8⌋`; on
`(a/(n+1/2), a/n]` (`a = 1/8`) `dist ≥ m - n p - c` and on `(a/(n+1), a/(n+1/2)]`
`dist ≥ (n+1) p - m - c`, giving the 16 linear pieces below.  They hold for both classes mod 4.
-/

open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma lamX_D1x (r p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    lamX r p ≤ 2 * r + 2 * (r / 8) - min ((r / 8) % p) (p - (r / 8) % p) := by
  have hodd : p % 2 = 1 := by have := hp.eq_two_or_odd; omega
  exact val_D1x p r (lev := lamInst.lev) hodd hp.pos (r / 8)


lemma d1p_0 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 68 1 64 17 (64) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 8 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (64) 320 (by norm_num) (by omega)

lemma d1p_1 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 64 1 60 19 (-64) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 7 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-64) 320 (by norm_num) (by omega)

lemma d1p_2 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 60 1 56 17 (56) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 7 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (56) 320 (by norm_num) (by omega)

lemma d1p_3 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 56 1 52 19 (-56) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 6 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-56) 320 (by norm_num) (by omega)

lemma d1p_4 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 52 1 48 17 (48) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 6 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (48) 320 (by norm_num) (by omega)

lemma d1p_5 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 48 1 44 19 (-48) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 5 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-48) 320 (by norm_num) (by omega)

lemma d1p_6 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 44 1 40 17 (40) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 5 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (40) 320 (by norm_num) (by omega)

lemma d1p_7 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 40 1 36 19 (-40) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 4 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-40) 320 (by norm_num) (by omega)

lemma d1p_8 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 36 1 32 17 (32) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 4 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (32) 320 (by norm_num) (by omega)

lemma d1p_9 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 32 1 28 19 (-32) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 3 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-32) 320 (by norm_num) (by omega)

lemma d1p_10 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 28 1 24 17 (24) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 3 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (24) 320 (by norm_num) (by omega)

lemma d1p_11 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 24 1 20 19 (-24) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 2 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-24) 320 (by norm_num) (by omega)

lemma d1p_12 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 20 1 16 17 (16) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 2 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (16) 320 (by norm_num) (by omega)

lemma d1p_13 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 16 1 12 19 (-16) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 1 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-16) 320 (by norm_num) (by omega)

lemma d1p_14 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 12 1 8 17 (8) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 1 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 (8) 320 (by norm_num) (by omega)

lemma d1p_15 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) :
    Covers c (lamW r) r (mkPiece 1 8 1 4 19 (-8) 320 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h2 : p ≠ 2 := by
    rintro rfl; exact hc2 (by simpa using hc)
  have hb := lamX_D1x r p hp h2
  have hd := dist_ge p (r / 8) 0 hp.pos
  generalize (r / 8) % p = s0 at hb hd
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 19 (-8) 320 (by norm_num) (by omega)

noncomputable def ld1 : List Piece :=
  [mkPiece 1 68 1 64 17 (64) 320 8,
   mkPiece 1 64 1 60 19 (-64) 320 8,
   mkPiece 1 60 1 56 17 (56) 320 8,
   mkPiece 1 56 1 52 19 (-56) 320 8,
   mkPiece 1 52 1 48 17 (48) 320 8,
   mkPiece 1 48 1 44 19 (-48) 320 8,
   mkPiece 1 44 1 40 17 (40) 320 8,
   mkPiece 1 40 1 36 19 (-40) 320 8,
   mkPiece 1 36 1 32 17 (32) 320 8,
   mkPiece 1 32 1 28 19 (-32) 320 8,
   mkPiece 1 28 1 24 17 (24) 320 8,
   mkPiece 1 24 1 20 19 (-24) 320 8,
   mkPiece 1 20 1 16 17 (16) 320 8,
   mkPiece 1 16 1 12 19 (-16) 320 8,
   mkPiece 1 12 1 8 17 (8) 320 8,
   mkPiece 1 8 1 4 19 (-8) 320 8]


lemma ld1_covers (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) : ∀ P ∈ ld1, Covers c (lamW r) r P := by
  intro P hP
  simp only [ld1, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [d1p_0 c hc2 r, d1p_1 c hc2 r, d1p_2 c hc2 r, d1p_3 c hc2 r, d1p_4 c hc2 r, d1p_5 c hc2 r, d1p_6 c hc2 r, d1p_7 c hc2 r, d1p_8 c hc2 r, d1p_9 c hc2 r, d1p_10 c hc2 r, d1p_11 c hc2 r, d1p_12 c hc2 r, d1p_13 c hc2 r, d1p_14 c hc2 r, d1p_15 c hc2 r]

end CatalanFrames.Lambda
