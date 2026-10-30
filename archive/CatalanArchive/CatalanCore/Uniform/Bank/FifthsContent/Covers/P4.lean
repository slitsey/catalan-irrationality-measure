import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P4
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths

theorem pP4_0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 306 2 603 (7) (-102) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 32 j 1 306 2 603 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 603 1 297 (19) (297) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 32 j 2 603 1 297 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 297 2 585 (7) (-99) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 31 j 1 297 2 585 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 585 1 288 (19) (288) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 31 j 2 585 1 288 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 288 2 567 (7) (-96) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 30 j 1 288 2 567 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 567 1 279 (19) (279) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 30 j 2 567 1 279 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_6 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 279 2 549 (7) (-93) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 29 j 1 279 2 549 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_7 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 549 1 270 (19) (270) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 29 j 2 549 1 270 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_8 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 270 2 531 (7) (-90) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 28 j 1 270 2 531 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_9 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 531 1 261 (19) (261) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 28 j 2 531 1 261 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_10 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 261 2 513 (7) (-87) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 27 j 1 261 2 513 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_11 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 513 1 252 (19) (252) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 27 j 2 513 1 252 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_12 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 252 2 495 (7) (-84) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 26 j 1 252 2 495 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_13 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 495 1 243 (19) (243) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 26 j 2 495 1 243 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_14 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 243 2 477 (7) (-81) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 25 j 1 243 2 477 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_15 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 477 1 234 (19) (234) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 25 j 2 477 1 234 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_16 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 234 2 459 (7) (-78) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 24 j 1 234 2 459 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_17 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 459 1 225 (19) (225) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 24 j 2 459 1 225 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_18 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 225 2 441 (7) (-75) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 23 j 1 225 2 441 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_19 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 441 1 216 (19) (216) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 23 j 2 441 1 216 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_20 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 216 2 423 (7) (-72) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 22 j 1 216 2 423 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_21 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 423 1 207 (19) (207) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 22 j 2 423 1 207 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_22 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 207 2 405 (7) (-69) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 21 j 1 207 2 405 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_23 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 405 1 198 (19) (198) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 21 j 2 405 1 198 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_24 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 198 2 387 (7) (-66) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 20 j 1 198 2 387 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_25 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 387 1 189 (19) (189) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 20 j 2 387 1 189 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_26 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 189 2 369 (7) (-63) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 19 j 1 189 2 369 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_27 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 369 1 180 (19) (180) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 19 j 2 369 1 180 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_28 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 180 2 351 (7) (-60) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 18 j 1 180 2 351 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_29 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 351 1 171 (19) (171) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 18 j 2 351 1 171 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_30 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 171 2 333 (7) (-57) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 17 j 1 171 2 333 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_31 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 333 1 162 (19) (162) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 17 j 2 333 1 162 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP4_32 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 162 2 315 (7) (-54) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 16 j 1 162 2 315 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem covPrefix4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    ∀ P ∈ prefix4, CovP T depth j P := by
  intro P hP
  simp only [prefix4, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_0 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_1 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_2 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_3 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_4 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_5 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_6 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_7 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_8 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_9 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_10 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_11 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_12 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_13 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_14 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_15 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_16 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_17 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_18 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_19 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_20 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_21 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_22 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_23 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_24 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_25 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_26 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_27 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_28 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_29 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_30 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_31 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP4_32 T depth hcF j)

#print axioms covPrefix4
end CatalanCore.Uniform.Bank.FifthsContent
