import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.ProfileUF.J4
import CatalanCore.Uniform.Bank.FifthsContent.LP
import CatalanCore.Uniform.Bank.FifthsContent.UF
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths

theorem pU4_0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 1 9 55 486 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 9 0 4 1 9 55 486 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 55 486 50 441 (55) (396) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 9 9 0 4 55 486 50 441 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 50 441 5 44 (155) (-486) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 9 8 0 4 50 441 5 44 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 44 11 90 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 8 0 4 5 44 11 90 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 11 90 10 81 (11) (72) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 9 8 0 4 11 90 10 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 10 81 55 441 (31) (-90) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 8 0 4 10 81 55 441 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_6 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 55 441 1 8 (100) (-9) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 8 0 4 55 441 1 8 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_7 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 1 8 25 198 (55) (351) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 8 0 4 1 8 25 198 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_8 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 25 198 5 39 (155) (-441) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 8 7 0 4 25 198 5 39 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_9 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 39 11 81 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 7 0 4 5 39 11 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_10 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 11 81 5 36 (11) (63) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 8 7 0 4 11 81 5 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_11 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 36 50 351 (7) (-3) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 0 4 5 36 50 351 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pU4_12 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 50 351 5 34 (155) (-396) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 7 6 0 4 50 351 5 34 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_13 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 34 11 72 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 6 0 4 5 34 11 72 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_14 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 11 72 10 63 (11) (54) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 7 6 0 4 11 72 10 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_15 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 10 63 25 153 (7) (-3) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 0 4 10 63 25 153 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pU4_16 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 25 153 5 29 (155) (-351) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 6 5 0 4 25 153 5 29 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_17 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 29 11 63 (22) (-18) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 6 5 0 4 5 29 11 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_18 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 11 63 5 27 (11) (45) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 6 5 0 4 11 63 5 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_19 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 27 50 261 (7) (-3) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 0 4 5 27 50 261 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pU4_20 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 50 261 11 54 (155) (-306) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 5 4 0 4 50 261 11 54 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_21 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 11 54 5 24 (100) (-36) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 5 4 0 4 11 54 5 24 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_22 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 24 2 9 (11) (36) (23400000000) (9) := by
  refine pieceOK_m3 T depth hcF 5 4 0 4 5 24 2 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_23 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 2 9 25 108 (19) (0) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 0 4 2 9 25 108 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pU4_24 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 25 108 11 45 (65) (-144) (39000000000) (15) := by
  refine pieceOK_S T depth hcF hdepth false false 4 25 108 11 45 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 4 * p ≤ r := by omega
  have hqb : r < (4 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 4 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_25 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 11 45 1 4 (140) (-207) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth false false 4 11 45 1 4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 4 * p ≤ r := by omega
  have hqb : r < (4 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 4 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_26 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 1 4 55 216 (95) (-27) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth true false 4 1 4 55 216 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 3 * p ≤ r := by omega
  have hqb : r < (3 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 3 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k true false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_27 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 55 216 5 19 (40) (189) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth true false 4 55 216 5 19 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 3 * p ≤ r := by omega
  have hqb : r < (3 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 3 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k true false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_28 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 5 19 5 18 (-1) (72) (23400000000) (9) := by
  refine pieceOK_S T depth hcF hdepth true false 4 5 19 5 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 3 * p ≤ r := by omega
  have hqb : r < (3 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 3 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k true false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_29 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 18 50 171 (19) (0) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 0 4 5 18 50 171 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pU4_30 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 50 171 11 36 (65) (-114) (39000000000) (15) := by
  refine pieceOK_S T depth hcF hdepth false false 4 50 171 11 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 3 * p ≤ r := by omega
  have hqb : r < (3 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 3 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_31 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 11 36 55 171 (140) (-162) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth false false 4 11 36 55 171 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 3 * p ≤ r := by omega
  have hqb : r < (3 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 3 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_32 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 55 171 1 3 (85) (9) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth false false 4 55 171 1 3 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 3 * p ≤ r := by omega
  have hqb : r < (3 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 3 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_33 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 1 3 5 14 (40) (144) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth true false 4 1 3 5 14 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 2 * p ≤ r := by omega
  have hqb : r < (2 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 2 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k true false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_34 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 5 14 10 27 (-1) (54) (23400000000) (9) := by
  refine pieceOK_S T depth hcF hdepth true false 4 5 14 10 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 2 * p ≤ r := by omega
  have hqb : r < (2 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 2 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k true false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_35 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 10 27 25 63 (19) (0) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 0 4 10 27 25 63 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pU4_36 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 25 63 11 27 (65) (-84) (39000000000) (15) := by
  refine pieceOK_S T depth hcF hdepth false false 4 25 63 11 27 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 2 * p ≤ r := by omega
  have hqb : r < (2 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 2 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_37 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 11 27 55 126 (140) (-117) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth false false 4 11 27 55 126 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 2 * p ≤ r := by omega
  have hqb : r < (2 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 2 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_38 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 55 126 1 2 (85) (9) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth false false 4 55 126 1 2 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 2 * p ≤ r := by omega
  have hqb : r < (2 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 2 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k false false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_39 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 1 2 5 9 (40) (99) (117000000000) (45) := by
  refine pieceOK_S T depth hcF hdepth true false 4 1 2 5 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  have hqa : 1 * p ≤ r := by omega
  have hqb : r < (1 + 1) * p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hdq, hms⟩ := div_mod_of r p 1 hqa hqb
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  have hok : CandOK m r p k true false := by
    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega
  rw [candPrice, if_pos hok]
  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega

theorem pU4_40 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 9 11 18 (100) (-9) (117000000000) (45) := by
  refine pieceOK_m3 T depth hcF 1 1 0 4 5 9 11 18 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_41 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 11 18 50 81 (5) (9) (13000000000) (5) := by
  refine pieceOK_m3 T depth hcF 1 1 0 4 11 18 50 81 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨by omega, by omega⟩

theorem pU4_42 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 50 81 1 1 (65) (-54) (39000000000) (15) := by
  refine pieceOK_lp1 T depth hcF hdepth 4 50 81 1 1 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega

theorem pU4_43 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    PieceOK T depth 4 1 1 10 9 (35) (-24) (39000000000) (15) := by
  refine pieceOK_lp2 T depth hcF hdepth 4 1 1 10 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  refine ⟨fun hlt => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, fun hge => ⟨⟨?_, ?_⟩, ?_⟩⟩ <;> omega

theorem pU4_44 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 10 9 11 9 (155) (-117) (117000000000) (45) := by
  refine pieceOK_D45 T depth hcF 4 10 9 11 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pU4_45 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 11 9 5 4 (100) (-72) (117000000000) (45) := by
  refine pieceOK_D45 T depth hcF 4 11 9 5 4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pU4_46 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 5 4 55 36 (55) (-36) (117000000000) (45) := by
  refine pieceOK_D6 T depth hcF 4 5 4 55 36 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pU4_47 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 55 36 55 9 (0) (0) (2600000000) (1) := by
  refine pieceOK_D6 T depth hcF 4 55 36 55 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem pU4_48 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PieceOK T depth 4 55 9 63 10 (0) (0) (2600000000) (1) := by
  refine pieceOK_D6 T depth hcF 4 55 9 63 10 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2
  unfold R0 at hR
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem covProfileU4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    ∀ P ∈ profileU4, CovP T depth 4 P := by
  intro P hP
  simp only [profileU4, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_0 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_1 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_2 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_3 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_4 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_5 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_6 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_7 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_8 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_9 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_10 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_11 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_12 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_13 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_14 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_15 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_16 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_17 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_18 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_19 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_20 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_21 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_22 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_23 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_24 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_25 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_26 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_27 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_28 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_29 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_30 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_31 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_32 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_33 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_34 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_35 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_36 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_37 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_38 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_39 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_40 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_41 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_42 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_43 T depth hcF hdepth)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_44 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_45 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_46 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_47 T depth hcF)
  · exact covP_mk T depth 4 _ _ _ _ _ _ _ _ (by norm_num) (pU4_48 T depth hcF)

#print axioms covProfileU4
end CatalanCore.Uniform.Bank.FifthsContent
