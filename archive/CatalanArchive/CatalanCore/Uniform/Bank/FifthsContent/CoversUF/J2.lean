import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.ProfileUF.J2
import CatalanCore.Uniform.Bank.FifthsContent.LP
import CatalanCore.Uniform.Bank.FifthsContent.UF
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths

theorem pU2_0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 1 9 55 468 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 9 0 2 1 9 55 468 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 55 468 50 423 (55) (378) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 9 9 0 2 55 468 50 423 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 50 423 5 42 (155) (-468) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 9 8 0 2 50 423 5 42 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 42 11 90 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 8 0 2 5 42 11 90 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 11 90 10 81 (11) (72) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 8 0 2 11 90 10 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 10 81 1 8 (31) (-90) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 8 0 2 10 81 1 8 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_6 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 1 8 55 423 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 8 0 2 1 8 55 423 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_7 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 55 423 25 189 (55) (333) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 8 0 2 55 423 25 189 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_8 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 25 189 5 37 (155) (-423) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 7 0 2 25 189 5 37 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_9 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 37 11 81 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 7 0 2 5 37 11 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_10 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 11 81 5 36 (11) (63) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 7 0 2 11 81 5 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_11 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 36 1 7 (31) (-81) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 7 0 2 5 36 1 7 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_12 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 1 7 55 378 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 7 0 2 1 7 55 378 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_13 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 55 378 50 333 (55) (288) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 7 7 0 2 55 378 50 333 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_14 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 50 333 11 72 (155) (-378) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 7 6 0 2 50 333 11 72 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_15 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 11 72 5 32 (100) (-18) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 7 6 0 2 11 72 5 32 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_16 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 32 10 63 (11) (54) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 6 0 2 5 32 10 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_17 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 10 63 55 333 (31) (-72) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 6 6 0 2 10 63 55 333 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_18 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 55 333 1 6 (100) (-27) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 6 0 2 55 333 1 6 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_19 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 1 6 25 144 (55) (243) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 6 0 2 1 6 25 144 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_20 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 25 144 11 63 (155) (-333) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 5 0 2 25 144 11 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_21 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 11 63 5 27 (100) (-18) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 5 0 2 11 63 5 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_22 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 27 55 288 (31) (-63) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 5 5 0 2 5 27 55 288 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_23 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 55 288 1 5 (100) (-27) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 5 5 0 2 55 288 1 5 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_24 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 1 5 50 243 (55) (198) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 5 5 0 2 1 5 50 243 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_25 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 50 243 2 9 (7) (-3) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 0 2 50 243 2 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pU2_26 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 2 2 9 55 243 (13) (-30) (7800000000) (3) := by
  refine pieceOK_S T depth hcF hdepth false true 2 2 9 55 243 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 4 * p ≤ r := by omega
  have hqb : r < (4 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 4 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false true := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU2_27 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 2 55 243 5 22 (140) (-207) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth false true 2 55 243 5 22 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 4 * p ≤ r := by omega
  have hqb : r < (4 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 4 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false true := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU2_28 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 2 5 22 11 45 (95) (-9) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth false true 2 5 22 11 45 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 4 * p ≤ r := by omega
  have hqb : r < (4 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 4 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false true := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU2_29 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 2 11 45 1 4 (40) (216) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth false true 2 11 45 1 4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 4 * p ≤ r := by omega
  have hqb : r < (4 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 4 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false true := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU2_30 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 2 1 4 25 99 (-5) (396) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth true true 2 1 4 25 99 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 3 * p ≤ r := by omega
  have hqb : r < (3 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 3 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k true true := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU2_31 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 25 99 5 18 (19) (0) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 0 2 25 99 5 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pU2_32 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 18 5 17 (29) (-36) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 3 3 0 2 5 18 5 17 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_33 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 17 11 36 (100) (-27) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 3 3 0 2 5 17 11 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_34 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 11 36 50 153 (5) (17) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 3 3 0 2 11 36 50 153 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_35 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 50 153 1 3 (145) (-153) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 3 2 0 2 50 153 1 3 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_36 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 1 3 55 153 (100) (-18) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 3 2 0 2 1 3 55 153 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_37 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 55 153 10 27 (1) (3) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 3 2 0 2 55 153 10 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_38 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 10 27 11 27 (29) (-27) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 2 2 0 2 10 27 11 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_39 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 11 27 5 12 (2) (0) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 2 2 0 2 11 27 5 12 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_40 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 12 25 54 (5) (12) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 2 2 0 2 5 12 25 54 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_41 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 25 54 1 2 (145) (-108) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 2 1 0 2 25 54 1 2 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_42 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 1 2 55 108 (100) (-18) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 2 1 0 2 1 2 55 108 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_43 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 55 108 5 9 (1) (2) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 2 1 0 2 55 108 5 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_44 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 9 11 18 (29) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 1 1 0 2 5 9 11 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_45 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 11 18 5 7 (2) (0) (2600000000) (1) := by
  refine pieceOK_m3 T depth hcF 1 1 0 2 11 18 5 7 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_46 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 7 50 63 (5) (7) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 1 1 0 2 5 7 50 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU2_47 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 2 50 63 1 1 (65) (-42) (39000000000) (15) := by
  refine pieceOK_lp1 T depth hcF hdepth 2 50 63 1 1 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega

theorem pU2_48 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 2 1 1 10 9 (35) (-12) (39000000000) (15) := by
  refine pieceOK_lp2 T depth hcF hdepth 2 1 1 10 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  refine ⟨fun hlt => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, fun hge => ⟨⟨?_, ?_⟩, ?_⟩⟩ <;> omega

theorem pU2_49 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 10 9 11 9 (155) (-81) (117000000000) (45) := by
  refine pieceOK_D45 T depth hcF 2 10 9 11 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pU2_50 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 11 9 5 2 (100) (-36) (117000000000) (45) := by
  refine pieceOK_D45 T depth hcF 2 11 9 5 2 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pU2_51 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 5 2 55 18 (55) (-18) (117000000000) (45) := by
  refine pieceOK_D6 T depth hcF 2 5 2 55 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pU2_52 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 55 18 55 9 (0) (0) (2600000000) (1) := by
  refine pieceOK_D6 T depth hcF 2 55 18 55 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pU2_53 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 2 55 9 63 10 (0) (0) (2600000000) (1) := by
  refine pieceOK_D6 T depth hcF 2 55 9 63 10 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem covProfileU2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    ∀ P ∈ profileU2, CovP T depth 2 P := by
  intro P hP
  simp only [profileU2, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_0 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_1 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_2 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_3 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_4 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_5 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_6 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_7 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_8 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_9 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_10 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_11 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_12 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_13 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_14 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_15 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_16 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_17 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_18 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_19 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_20 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_21 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_22 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_23 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_24 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_25 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_26 T depth hcF hdepth)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_27 T depth hcF hdepth)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_28 T depth hcF hdepth)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_29 T depth hcF hdepth)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_30 T depth hcF hdepth)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_31 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_32 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_33 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_34 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_35 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_36 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_37 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_38 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_39 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_40 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_41 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_42 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_43 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_44 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_45 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_46 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_47 T depth hcF hdepth)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_48 T depth hcF hdepth)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_49 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_50 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_51 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_52 T depth hcF)
  · exact covP_mk T depth 2 _ _ _ _ _ _ _ _ (by norm_num) (pU2_53 T depth hcF)

#print axioms covProfileU2
end CatalanCore.Uniform.Bank.FifthsContent
