module

public import CatalanFrames.HybGen.ClassBand

@[expose] public section

/-!
# Covers of the "high" class table (`3 kq ≈ 2p`)

Stated for an arbitrary hybrid instance `I` with `LevelFacts` and the class dictionary
`Band I 6 c 3 2 1 2` (`2p + 1 ≤ 3 kq p ≤ 2p + 2`).  Window `r ≤ 8m ≤ r + 9`.
Linear facts handed to omega in each piece: the window, the two floors `sn*r/sd < p ≤ tn*r/td`,
the band, `5 ≤ p`, and the bound of the dual lemma (named in the proof).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen

namespace CatalanFrames.Thirds

variable {Fr : Frame} {I : HybInst Fr}
  (T : LevelFacts I (fun p => 5 ≤ p) (fun q c => c < I.cd.kq q))
  {c : ZMod 6} (hband : Band I 6 c 3 2 1 2)
  {r m : ℕ} (hm1 : r ≤ 8 * m) (hm2 : 8 * m ≤ r + 9) (hr : 400 ≤ r)

include hband hm1 hm2 hr

/-- piece 1: `D1x`. -/
lemma thigh_1 : Covers c (WGm I r m) r (mkPiece 1 4 27 40 17 0 48 8) :=
  covers_mkM c (BandP I 3 2 1 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h5, hk1, hk2⟩ := hb
    have hb1 := XGm_D1x I r m p hp (by omega)
    have hd := dist_ge p m 0 hp.pos (by omega)
    generalize m % p = s0 at hb1 hd
    omega)

include T in
/-- piece 2: `D2`. -/
lemma thigh_2 : Covers c (WGm I r m) r (mkPiece 27 40 3 4 39 (-20) 72 12) :=
  covers_mkM c (BandP I 3 2 1 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h5, hk1, hk2⟩ := hb
    have hkr : I.cd.kq p ≤ r := by omega
    obtain ⟨u, L, h1, h2, h3, h4, h6⟩ :=
      XGm_D2 T r m p hp h5 (by omega) (by omega) hkr
    omega)

include T in
/-- piece 3: `D2`. -/
lemma thigh_3 : Covers c (WGm I r m) r (mkPiece 3 4 1 1 27 (-20) 36 6) :=
  covers_mkM c (BandP I 3 2 1 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h5, hk1, hk2⟩ := hb
    have hkr : I.cd.kq p ≤ r := by omega
    obtain ⟨u, L, h1, h2, h3, h4, h6⟩ :=
      XGm_D2 T r m p hp h5 (by omega) (by omega) hkr
    omega)

include T in
/-- piece 4: `D45`. -/
lemma thigh_4 : Covers c (WGm I r m) r (mkPiece 1 1 5 4 21 (-14) 36 6) :=
  covers_mkM c (BandP I 3 2 1 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h5, hk1, hk2⟩ := hb
    have h6 := XGm_D45 T r m p hp h5 (by omega) (by omega)
    omega)

include T in
/-- piece 5: `D45`. -/
lemma thigh_5 : Covers c (WGm I r m) r (mkPiece 5 4 3 2 27 (-16) 72 12) :=
  covers_mkM c (BandP I 3 2 1 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h5, hk1, hk2⟩ := hb
    have h6 := XGm_D45 T r m p hp h5 (by omega) (by omega)
    omega)

include T in
/-- piece 6: `D6`. -/
lemma thigh_6 : Covers c (WGm I r m) r (mkPiece 3 2 15 8 15 (-8) 72 12) :=
  covers_mkM c (BandP I 3 2 1 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h5, hk1, hk2⟩ := hb
    have h6 := XGm_D6 T r m p hp h5 (by omega) (by omega)
    omega)

include T in
/-- piece 7: `D6`. -/
lemma thigh_7 : Covers c (WGm I r m) r (mkPiece 15 8 2 1 0 0 6 1) :=
  covers_mkM c (BandP I 3 2 1 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h5, hk1, hk2⟩ := hb
    have h6 := XGm_D6 T r m p hp h5 (by omega) (by omega)
    omega)

end CatalanFrames.Thirds
