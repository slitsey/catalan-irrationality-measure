import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.Profile.J3
import CatalanCore.Uniform.Bank.FifthsContent.LP
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths

theorem pJ3_0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 1 9 55 477 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 9 0 3 1 9 55 477 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 55 477 25 216 (55) (387) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 9 9 0 3 55 477 25 216 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 25 216 5 43 (155) (-477) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 9 8 0 3 25 216 5 43 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 43 11 90 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 8 0 3 5 43 11 90 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 11 90 10 81 (11) (72) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 8 0 3 11 90 10 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 10 81 1 8 (31) (-90) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 8 0 3 10 81 1 8 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_6 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 1 8 55 432 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 8 0 3 1 8 55 432 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_7 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 55 432 50 387 (55) (342) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 8 0 3 55 432 50 387 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_8 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 50 387 5 38 (155) (-432) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 7 0 3 50 387 5 38 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_9 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 38 11 81 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 7 0 3 5 38 11 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_10 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 11 81 5 36 (11) (63) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 7 0 3 11 81 5 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_11 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 36 55 387 (31) (-81) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 7 0 3 5 36 55 387 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_12 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 55 387 1 7 (100) (-18) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 7 7 0 3 55 387 1 7 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_13 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 1 7 25 171 (55) (297) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 7 7 0 3 1 7 25 171 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_14 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 25 171 5 33 (155) (-387) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 7 6 0 3 25 171 5 33 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_15 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 33 11 72 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 6 0 3 5 33 11 72 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_16 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 11 72 10 63 (11) (54) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 6 0 3 11 72 10 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_17 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 10 63 55 342 (31) (-72) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 6 6 0 3 10 63 55 342 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_18 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 55 342 1 6 (100) (-18) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 6 0 3 55 342 1 6 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_19 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 1 6 50 297 (55) (252) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 6 0 3 1 6 50 297 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_20 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 50 297 11 63 (155) (-342) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 5 0 3 50 297 11 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_21 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 11 63 5 28 (100) (-27) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 5 0 3 11 63 5 28 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_22 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 28 5 27 (11) (45) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 6 5 0 3 5 28 5 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_23 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 27 25 126 (7) (-3) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 0 3 5 27 25 126 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pJ3_24 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 25 126 11 54 (155) (-297) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 5 4 0 3 25 126 11 54 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_25 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 11 54 5 23 (100) (-27) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 5 4 0 3 11 54 5 23 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_26 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 23 2 9 (11) (36) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 5 4 0 3 5 23 2 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_27 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 2 9 50 207 (19) (0) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 0 3 2 9 50 207 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pJ3_28 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 50 207 1 4 (145) (-207) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 4 3 0 3 50 207 1 4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_29 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 1 4 55 207 (100) (-27) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 4 3 0 3 1 4 55 207 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_30 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 55 207 5 18 (1) (4) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 4 3 0 3 55 207 5 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_31 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 18 11 36 (100) (-18) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 3 3 0 3 5 18 11 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_32 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 11 36 25 81 (5) (18) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 3 3 0 3 11 36 25 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_33 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 25 81 1 3 (145) (-162) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 3 2 0 3 25 81 1 3 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_34 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 1 3 55 162 (100) (-27) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 3 2 0 3 1 3 55 162 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_35 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 55 162 10 27 (1) (3) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 3 2 0 3 55 162 10 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_36 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 10 27 5 13 (29) (-27) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 2 2 0 3 10 27 5 13 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_37 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 13 11 27 (100) (-18) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 2 2 0 3 5 13 11 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_38 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 11 27 50 117 (5) (13) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 2 2 0 3 11 27 50 117 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_39 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 50 117 55 117 (145) (-117) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 2 1 0 3 50 117 55 117 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_40 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 55 117 1 2 (2) (0) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 2 1 0 3 55 117 1 2 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_41 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 1 2 5 9 (1) (2) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 2 1 0 3 1 2 5 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_42 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 9 11 18 (29) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 1 1 0 3 5 9 11 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_43 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 11 18 5 8 (2) (0) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 1 1 0 3 11 18 5 8 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_44 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 8 25 36 (5) (8) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 1 1 0 3 5 8 25 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ3_45 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 3 25 36 1 1 (65) (-48) (39000000000) (15) := by
  refine pieceOK_lp1 T depth hcF hdepth 3 25 36 1 1 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega

theorem pJ3_46 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 3 1 1 10 9 (35) (-18) (39000000000) (15) := by
  refine pieceOK_lp2 T depth hcF hdepth 3 1 1 10 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  refine ⟨fun hlt => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, fun hge => ⟨⟨?_, ?_⟩, ?_⟩⟩ <;> omega

theorem pJ3_47 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 10 9 11 9 (155) (-99) (117000000000) (45) := by
  refine pieceOK_D45 T depth hcF 3 10 9 11 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pJ3_48 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 11 9 5 3 (100) (-54) (117000000000) (45) := by
  refine pieceOK_D45 T depth hcF 3 11 9 5 3 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pJ3_49 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 5 3 55 27 (55) (-27) (117000000000) (45) := by
  refine pieceOK_D6 T depth hcF 3 5 3 55 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pJ3_50 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 55 27 55 9 (0) (0) (2600000000) (1) := by
  refine pieceOK_D6 T depth hcF 3 55 27 55 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pJ3_51 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 3 55 9 63 10 (0) (0) (2600000000) (1) := by
  refine pieceOK_D6 T depth hcF 3 55 9 63 10 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem covProfile3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    ∀ P ∈ profile3, CovP T depth 3 P := by
  intro P hP
  simp only [profile3, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_0 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_1 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_2 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_3 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_4 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_5 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_6 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_7 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_8 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_9 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_10 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_11 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_12 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_13 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_14 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_15 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_16 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_17 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_18 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_19 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_20 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_21 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_22 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_23 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_24 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_25 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_26 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_27 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_28 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_29 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_30 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_31 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_32 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_33 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_34 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_35 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_36 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_37 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_38 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_39 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_40 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_41 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_42 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_43 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_44 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_45 T depth hcF hdepth)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_46 T depth hcF hdepth)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_47 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_48 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_49 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_50 T depth hcF)
  · exact covP_mk T depth 3 _ _ _ _ _ _ _ _ (by norm_num) (pJ3_51 T depth hcF)

#print axioms covProfile3
end CatalanCore.Uniform.Bank.FifthsContent
