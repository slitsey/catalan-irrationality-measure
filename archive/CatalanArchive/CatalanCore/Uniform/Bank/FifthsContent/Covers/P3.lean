import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P3
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths

theorem pP3_0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 909 1 450 (19) (450) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 49 j 2 909 1 450 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 450 2 891 (7) (-150) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 48 j 1 450 2 891 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 891 1 441 (19) (441) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 48 j 2 891 1 441 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 441 2 873 (7) (-147) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 47 j 1 441 2 873 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 873 1 432 (19) (432) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 47 j 2 873 1 432 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 432 2 855 (7) (-144) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 46 j 1 432 2 855 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_6 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 855 1 423 (19) (423) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 46 j 2 855 1 423 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_7 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 423 2 837 (7) (-141) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 45 j 1 423 2 837 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_8 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 837 1 414 (19) (414) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 45 j 2 837 1 414 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_9 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 414 2 819 (7) (-138) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 44 j 1 414 2 819 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_10 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 819 1 405 (19) (405) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 44 j 2 819 1 405 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_11 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 405 2 801 (7) (-135) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 43 j 1 405 2 801 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_12 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 801 1 396 (19) (396) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 43 j 2 801 1 396 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_13 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 396 2 783 (7) (-132) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 42 j 1 396 2 783 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_14 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 783 1 387 (19) (387) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 42 j 2 783 1 387 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_15 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 387 2 765 (7) (-129) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 41 j 1 387 2 765 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_16 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 765 1 378 (19) (378) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 41 j 2 765 1 378 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_17 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 378 2 747 (7) (-126) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 40 j 1 378 2 747 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_18 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 747 1 369 (19) (369) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 40 j 2 747 1 369 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_19 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 369 2 729 (7) (-123) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 39 j 1 369 2 729 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_20 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 729 1 360 (19) (360) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 39 j 2 729 1 360 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_21 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 360 2 711 (7) (-120) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 38 j 1 360 2 711 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_22 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 711 1 351 (19) (351) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 38 j 2 711 1 351 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_23 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 351 2 693 (7) (-117) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 37 j 1 351 2 693 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_24 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 693 1 342 (19) (342) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 37 j 2 693 1 342 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_25 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 342 2 675 (7) (-114) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 36 j 1 342 2 675 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_26 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 675 1 333 (19) (333) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 36 j 2 675 1 333 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_27 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 333 2 657 (7) (-111) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 35 j 1 333 2 657 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_28 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 657 1 324 (19) (324) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 35 j 2 657 1 324 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_29 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 324 2 639 (7) (-108) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 34 j 1 324 2 639 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_30 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 639 1 315 (19) (315) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 34 j 2 639 1 315 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_31 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 315 2 621 (7) (-105) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 33 j 1 315 2 621 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP3_32 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 621 1 306 (19) (306) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 33 j 2 621 1 306 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem covPrefix3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    ∀ P ∈ prefix3, CovP T depth j P := by
  intro P hP
  simp only [prefix3, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_0 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_1 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_2 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_3 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_4 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_5 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_6 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_7 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_8 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_9 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_10 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_11 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_12 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_13 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_14 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_15 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_16 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_17 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_18 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_19 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_20 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_21 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_22 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_23 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_24 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_25 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_26 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_27 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_28 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_29 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_30 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_31 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP3_32 T depth hcF j)

#print axioms covPrefix3
end CatalanCore.Uniform.Bank.FifthsContent
