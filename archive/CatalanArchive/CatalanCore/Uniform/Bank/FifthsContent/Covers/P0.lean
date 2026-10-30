import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P0
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths

theorem pP0_0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 900 2 1791 (7) (-300) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 98 j 1 900 2 1791 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_1 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1791 1 891 (19) (891) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 98 j 2 1791 1 891 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_2 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 891 2 1773 (7) (-297) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 97 j 1 891 2 1773 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_3 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1773 1 882 (19) (882) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 97 j 2 1773 1 882 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_4 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 882 2 1755 (7) (-294) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 96 j 1 882 2 1755 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1755 1 873 (19) (873) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 96 j 2 1755 1 873 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_6 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 873 2 1737 (7) (-291) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 95 j 1 873 2 1737 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_7 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1737 1 864 (19) (864) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 95 j 2 1737 1 864 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_8 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 864 2 1719 (7) (-288) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 94 j 1 864 2 1719 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_9 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1719 1 855 (19) (855) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 94 j 2 1719 1 855 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_10 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 855 2 1701 (7) (-285) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 93 j 1 855 2 1701 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_11 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1701 1 846 (19) (846) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 93 j 2 1701 1 846 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_12 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 846 2 1683 (7) (-282) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 92 j 1 846 2 1683 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_13 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1683 1 837 (19) (837) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 92 j 2 1683 1 837 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_14 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 837 2 1665 (7) (-279) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 91 j 1 837 2 1665 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_15 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1665 1 828 (19) (828) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 91 j 2 1665 1 828 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_16 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 828 2 1647 (7) (-276) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 90 j 1 828 2 1647 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_17 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1647 1 819 (19) (819) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 90 j 2 1647 1 819 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_18 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 819 2 1629 (7) (-273) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 89 j 1 819 2 1629 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_19 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1629 1 810 (19) (810) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 89 j 2 1629 1 810 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_20 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 810 2 1611 (7) (-270) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 88 j 1 810 2 1611 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_21 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1611 1 801 (19) (801) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 88 j 2 1611 1 801 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_22 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 801 2 1593 (7) (-267) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 87 j 1 801 2 1593 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_23 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1593 1 792 (19) (792) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 87 j 2 1593 1 792 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_24 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 792 2 1575 (7) (-264) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 86 j 1 792 2 1575 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_25 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1575 1 783 (19) (783) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 86 j 2 1575 1 783 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_26 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 783 2 1557 (7) (-261) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 85 j 1 783 2 1557 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_27 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1557 1 774 (19) (774) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 85 j 2 1557 1 774 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_28 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 774 2 1539 (7) (-258) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 84 j 1 774 2 1539 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_29 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1539 1 765 (19) (765) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 84 j 2 1539 1 765 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_30 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 765 2 1521 (7) (-255) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 83 j 1 765 2 1521 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_31 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 2 1521 1 756 (19) (756) (23400000000) (9) := by
  refine pieceOK_saw T depth hcF 83 j 2 1521 1 756 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem pP0_32 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    PieceOK T depth j 1 756 2 1503 (7) (-252) (7800000000) (3) := by
  refine pieceOK_saw T depth hcF 82 j 1 756 2 1503 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro r p h1 h2; omega) ?_
  intro r p m hR hb1 hb2 h1 h2
  unfold R0 at hR
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s0 hs0 hd
  omega

theorem covPrefix0 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :
    ∀ P ∈ prefix0, CovP T depth j P := by
  intro P hP
  simp only [prefix0, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_0 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_1 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_2 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_3 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_4 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_5 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_6 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_7 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_8 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_9 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_10 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_11 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_12 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_13 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_14 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_15 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_16 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_17 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_18 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_19 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_20 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_21 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_22 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_23 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_24 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_25 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_26 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_27 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_28 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_29 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_30 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_31 T depth hcF j)
  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (pP0_32 T depth hcF j)

#print axioms covPrefix0
end CatalanCore.Uniform.Bank.FifthsContent
