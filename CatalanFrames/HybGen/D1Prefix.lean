module

public import CatalanFrames.HybGen.ClassBand
public import CatalanFrames.HybCommon.Pieces

@[expose] public section

/-!
# The `ld1` prefix covers (exact `D1`), generic in the modulus and the class

`ld1` (frame free, `HybCommon.Pieces`) covers the primes `r/68 < p ≤ r/4` of a class `c` (modulo any `M`)
that avoids the prime `2`, for every hybrid size `m` with `r ≤ 8m ≤ r + 9`.  Linear facts for omega:
the window, `sd*..`-floors of the piece, `hb : X ≤ 2r + 2m - min s0 (p - s0)` and
`hd : min (m - n p) ((n+1) p - m) ≤ min s0 (p - s0)` with `s0 = m % p` generalised, `n p ≤ m`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen

namespace CatalanFrames.HybGen

variable {Fr : Frame} (I : HybInst Fr) {M : ℕ} {c : ZMod M}
  (hc2 : ∀ p : ℕ, p.Prime → (p : ZMod M) = c → p ≠ 2)
  {r m : ℕ} (hm1 : r ≤ 8 * m) (hm2 : 8 * m ≤ r + 9)

include hc2 hm1 hm2

lemma d1m_0 : Covers c (WGm I r m) r (mkPiece 1 68 1 64 17 64 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 8 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_1 : Covers c (WGm I r m) r (mkPiece 1 64 1 60 19 (-64) 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 7 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_2 : Covers c (WGm I r m) r (mkPiece 1 60 1 56 17 56 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 7 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_3 : Covers c (WGm I r m) r (mkPiece 1 56 1 52 19 (-56) 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 6 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_4 : Covers c (WGm I r m) r (mkPiece 1 52 1 48 17 48 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 6 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_5 : Covers c (WGm I r m) r (mkPiece 1 48 1 44 19 (-48) 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 5 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_6 : Covers c (WGm I r m) r (mkPiece 1 44 1 40 17 40 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 5 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_7 : Covers c (WGm I r m) r (mkPiece 1 40 1 36 19 (-40) 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 4 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_8 : Covers c (WGm I r m) r (mkPiece 1 36 1 32 17 32 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 4 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_9 : Covers c (WGm I r m) r (mkPiece 1 32 1 28 19 (-32) 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 3 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_10 : Covers c (WGm I r m) r (mkPiece 1 28 1 24 17 24 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 3 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_11 : Covers c (WGm I r m) r (mkPiece 1 24 1 20 19 (-24) 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 2 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_12 : Covers c (WGm I r m) r (mkPiece 1 20 1 16 17 16 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 2 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_13 : Covers c (WGm I r m) r (mkPiece 1 16 1 12 19 (-16) 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 1 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_14 : Covers c (WGm I r m) r (mkPiece 1 12 1 8 17 8 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 1 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

lemma d1m_15 : Covers c (WGm I r m) r (mkPiece 1 8 1 4 19 (-8) 320 8) :=
  covers_mkM c (fun p => p ≠ 2) hc2 (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp h2
    have hb := XGm_D1x I r m p hp h2
    have hd := dist_ge p m 0 hp.pos (by omega)
    generalize m % p = s0 at hb hd
    omega)

theorem ld1_covers : ∀ P ∈ ld1, Covers c (WGm I r m) r P := by
  intro P hP
  simp only [ld1, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [d1m_0 I hc2 hm1 hm2, d1m_1 I hc2 hm1 hm2, d1m_2 I hc2 hm1 hm2, d1m_3 I hc2 hm1 hm2, d1m_4 I hc2 hm1 hm2, d1m_5 I hc2 hm1 hm2, d1m_6 I hc2 hm1 hm2, d1m_7 I hc2 hm1 hm2, d1m_8 I hc2 hm1 hm2, d1m_9 I hc2 hm1 hm2, d1m_10 I hc2 hm1 hm2, d1m_11 I hc2 hm1 hm2, d1m_12 I hc2 hm1 hm2, d1m_13 I hc2 hm1 hm2, d1m_14 I hc2 hm1 hm2, d1m_15 I hc2 hm1 hm2]

end CatalanFrames.HybGen

#print axioms CatalanFrames.HybGen.ld1_covers
