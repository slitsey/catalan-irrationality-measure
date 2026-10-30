import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P5
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths

theorem pP5_0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 315 1 153 (19) (153) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 16 j 2 315 1 153 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 153 2 297 (7) (-51) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 15 j 1 153 2 297 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 297 1 144 (19) (144) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 15 j 2 297 1 144 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 144 2 279 (7) (-48) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 14 j 1 144 2 279 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 279 1 135 (19) (135) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 14 j 2 279 1 135 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 135 2 261 (7) (-45) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 13 j 1 135 2 261 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_6 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 261 1 126 (19) (126) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 13 j 2 261 1 126 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_7 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 126 2 243 (7) (-42) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 12 j 1 126 2 243 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_8 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 243 1 117 (19) (117) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 12 j 2 243 1 117 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_9 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 117 2 225 (7) (-39) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 11 j 1 117 2 225 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_10 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 225 1 108 (19) (108) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 11 j 2 225 1 108 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_11 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 108 2 207 (7) (-36) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 10 j 1 108 2 207 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_12 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 207 1 99 (19) (99) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 10 j 2 207 1 99 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_13 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 99 2 189 (7) (-33) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 9 j 1 99 2 189 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_14 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 189 1 90 (19) (90) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 9 j 2 189 1 90 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_15 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 90 2 171 (7) (-30) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 8 j 1 90 2 171 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_16 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 171 1 81 (19) (81) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 8 j 2 171 1 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_17 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 81 2 153 (7) (-27) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 7 j 1 81 2 153 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_18 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 153 1 72 (19) (72) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 7 j 2 153 1 72 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_19 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 72 2 135 (7) (-24) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 6 j 1 72 2 135 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_20 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 135 1 63 (19) (63) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 6 j 2 135 1 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_21 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 63 2 117 (7) (-21) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 5 j 1 63 2 117 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_22 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 117 1 54 (19) (54) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 5 j 2 117 1 54 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_23 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 54 2 99 (7) (-18) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 4 j 1 54 2 99 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_24 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 99 1 45 (19) (45) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 4 j 2 99 1 45 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_25 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 45 2 81 (7) (-15) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 3 j 1 45 2 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_26 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 81 1 36 (19) (36) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 3 j 2 81 1 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_27 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 36 2 63 (7) (-12) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 2 j 1 36 2 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_28 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 63 1 27 (19) (27) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 2 j 2 63 1 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_29 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 27 2 45 (7) (-9) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 1 j 1 27 2 45 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_30 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 45 1 18 (19) (18) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 1 j 2 45 1 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_31 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 18 2 27 (7) (-6) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 0 j 1 18 2 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP5_32 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 27 1 9 (19) (9) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 0 j 2 27 1 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem covPrefix5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    ∀ P ∈ prefix5, CovP T depth j P := by
  intro P hP
  simp only [prefix5, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_0 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_1 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_2 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_3 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_4 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_5 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_6 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_7 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_8 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_9 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_10 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_11 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_12 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_13 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_14 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_15 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_16 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_17 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_18 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_19 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_20 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_21 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_22 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_23 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_24 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_25 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_26 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_27 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_28 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_29 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_30 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_31 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP5_32 T depth hcF j)

#print axioms covPrefix5
end CatalanCore.Uniform.Bank.FifthsContent
