import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P1
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths

theorem pP1_0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1503 1 747 (19) (747) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 82 j 2 1503 1 747 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 747 2 1485 (7) (-249) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 81 j 1 747 2 1485 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1485 1 738 (19) (738) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 81 j 2 1485 1 738 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 738 2 1467 (7) (-246) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 80 j 1 738 2 1467 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1467 1 729 (19) (729) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 80 j 2 1467 1 729 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 729 2 1449 (7) (-243) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 79 j 1 729 2 1449 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_6 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1449 1 720 (19) (720) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 79 j 2 1449 1 720 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_7 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 720 2 1431 (7) (-240) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 78 j 1 720 2 1431 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_8 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1431 1 711 (19) (711) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 78 j 2 1431 1 711 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_9 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 711 2 1413 (7) (-237) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 77 j 1 711 2 1413 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_10 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1413 1 702 (19) (702) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 77 j 2 1413 1 702 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_11 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 702 2 1395 (7) (-234) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 76 j 1 702 2 1395 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_12 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1395 1 693 (19) (693) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 76 j 2 1395 1 693 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_13 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 693 2 1377 (7) (-231) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 75 j 1 693 2 1377 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_14 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1377 1 684 (19) (684) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 75 j 2 1377 1 684 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_15 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 684 2 1359 (7) (-228) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 74 j 1 684 2 1359 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_16 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1359 1 675 (19) (675) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 74 j 2 1359 1 675 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_17 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 675 2 1341 (7) (-225) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 73 j 1 675 2 1341 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_18 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1341 1 666 (19) (666) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 73 j 2 1341 1 666 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_19 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 666 2 1323 (7) (-222) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 72 j 1 666 2 1323 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_20 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1323 1 657 (19) (657) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 72 j 2 1323 1 657 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_21 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 657 2 1305 (7) (-219) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 71 j 1 657 2 1305 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_22 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1305 1 648 (19) (648) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 71 j 2 1305 1 648 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_23 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 648 2 1287 (7) (-216) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 70 j 1 648 2 1287 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_24 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1287 1 639 (19) (639) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 70 j 2 1287 1 639 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_25 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 639 2 1269 (7) (-213) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 69 j 1 639 2 1269 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_26 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1269 1 630 (19) (630) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 69 j 2 1269 1 630 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_27 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 630 2 1251 (7) (-210) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 68 j 1 630 2 1251 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_28 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1251 1 621 (19) (621) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 68 j 2 1251 1 621 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_29 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 621 2 1233 (7) (-207) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 67 j 1 621 2 1233 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_30 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1233 1 612 (19) (612) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 67 j 2 1233 1 612 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_31 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 612 2 1215 (7) (-204) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 66 j 1 612 2 1215 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP1_32 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1215 1 603 (19) (603) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 66 j 2 1215 1 603 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem covPrefix1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    ∀ P ∈ prefix1, CovP T depth j P := by
  intro P hP
  simp only [prefix1, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_0 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_1 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_2 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_3 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_4 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_5 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_6 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_7 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_8 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_9 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_10 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_11 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_12 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_13 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_14 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_15 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_16 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_17 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_18 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_19 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_20 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_21 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_22 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_23 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_24 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_25 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_26 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_27 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_28 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_29 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_30 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_31 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP1_32 T depth hcF j)

#print axioms covPrefix1
end CatalanCore.Uniform.Bank.FifthsContent
