import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.Profile.J1
import CatalanCore.Uniform.Bank.FifthsContent.LP
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths

theorem pJ1_0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 1 9 55 459 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 9 0 1 1 9 55 459 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 55 459 25 207 (55) (369) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 9 9 0 1 55 459 25 207 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 25 207 5 41 (155) (-459) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 9 8 0 1 25 207 5 41 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 41 11 90 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 8 0 1 5 41 11 90 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 11 90 10 81 (11) (72) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 8 0 1 11 90 10 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 10 81 1 8 (31) (-90) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 8 0 1 10 81 1 8 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_6 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 1 8 55 414 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 8 0 1 1 8 55 414 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_7 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 55 414 50 369 (55) (324) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 8 0 1 55 414 50 369 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_8 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 50 369 11 81 (155) (-414) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 7 0 1 50 369 11 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_9 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 11 81 5 36 (100) (-9) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 7 0 1 11 81 5 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_10 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 36 1 7 (31) (-81) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 7 0 1 5 36 1 7 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_11 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 1 7 55 369 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 7 0 1 1 7 55 369 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_12 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 55 369 25 162 (55) (279) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 7 7 0 1 55 369 25 162 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_13 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 25 162 10 63 (7) (-3) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 0 1 25 162 10 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pJ1_14 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 10 63 1 6 (31) (-72) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 6 6 0 1 10 63 1 6 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_15 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 1 6 55 324 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 6 6 0 1 1 6 55 324 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_16 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 55 324 50 279 (55) (234) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 6 0 1 55 324 50 279 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_17 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 50 279 5 27 (7) (-3) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 0 1 50 279 5 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pJ1_18 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 27 55 279 (31) (-63) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 5 5 0 1 5 27 55 279 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_19 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 55 279 1 5 (100) (-36) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 5 5 0 1 55 279 1 5 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_20 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 1 5 25 117 (55) (189) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 5 5 0 1 1 5 25 117 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_21 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 25 117 2 9 (7) (-3) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 0 1 25 117 2 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pJ1_22 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 2 9 5 21 (29) (-45) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 4 4 0 1 2 9 5 21 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_23 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 21 11 45 (100) (-36) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 4 4 0 1 5 21 11 45 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_24 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 11 45 50 189 (5) (21) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 4 4 0 1 11 45 50 189 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_25 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 50 189 5 18 (19) (0) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 0 1 50 189 5 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pJ1_26 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 18 11 36 (29) (-36) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 3 3 0 1 5 18 11 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_27 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 11 36 5 16 (2) (0) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 3 3 0 1 11 36 5 16 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_28 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 16 25 72 (5) (16) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 3 3 0 1 5 16 25 72 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_29 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 25 72 10 27 (19) (0) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 0 1 25 72 10 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pJ1_30 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 10 27 11 27 (29) (-27) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 2 2 0 1 10 27 11 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_31 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 11 27 5 11 (2) (0) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 2 2 0 1 11 27 5 11 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_32 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 11 50 99 (5) (11) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 2 2 0 1 5 11 50 99 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_33 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 50 99 5 9 (19) (0) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 0 1 50 99 5 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pJ1_34 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 9 11 18 (29) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 1 1 0 1 5 9 11 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_35 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 11 18 5 6 (2) (0) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 1 1 0 1 11 18 5 6 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_36 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 6 25 27 (5) (6) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 1 1 0 1 5 6 25 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_37 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 1 25 27 1 1 (65) (-36) (39000000000) (15) := by
  refine pieceOK_lp1 T depth hcF hdepth 1 25 27 1 1 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega

theorem pJ1_38 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 1 1 55 54 (100) (-9) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 1 0 0 1 1 1 55 54 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pJ1_39 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 1 55 54 10 9 (35) (-6) (39000000000) (15) := by
  refine pieceOK_lp2 T depth hcF hdepth 1 55 54 10 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  refine ⟨fun hlt => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, fun hge => ⟨⟨?_, ?_⟩, ?_⟩⟩ <;> omega

theorem pJ1_40 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 10 9 11 9 (155) (-63) (117000000000) (45) := by
  refine pieceOK_D45 T depth hcF 1 10 9 11 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pJ1_41 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 11 9 5 1 (100) (-18) (117000000000) (45) := by
  refine pieceOK_D45 T depth hcF 1 11 9 5 1 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pJ1_42 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 5 1 55 9 (55) (-9) (117000000000) (45) := by
  refine pieceOK_D6 T depth hcF 1 5 1 55 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pJ1_43 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 1 55 9 63 10 (0) (0) (2600000000) (1) := by
  refine pieceOK_D6 T depth hcF 1 55 9 63 10 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem covProfile1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    ∀ P ∈ profile1, CovP T depth 1 P := by
  intro P hP
  simp only [profile1, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_0 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_1 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_2 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_3 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_4 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_5 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_6 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_7 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_8 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_9 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_10 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_11 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_12 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_13 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_14 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_15 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_16 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_17 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_18 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_19 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_20 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_21 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_22 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_23 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_24 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_25 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_26 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_27 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_28 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_29 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_30 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_31 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_32 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_33 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_34 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_35 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_36 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_37 T depth hcF hdepth)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_38 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_39 T depth hcF hdepth)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_40 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_41 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_42 T depth hcF)
  · exact covP_mk T depth 1 _ _ _ _ _ _ _ _ (by norm_num) (pJ1_43 T depth hcF)

#print axioms covProfile1
end CatalanCore.Uniform.Bank.FifthsContent
