module
public import CatalanFrames.P6Hybrid.Pieces
@[expose] public section
open CatalanFrames.P6Hybrid
open CatalanFrames CatalanFrames.HybCommon
open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon CatalanFrames.P6
namespace CatalanArchive.CatalanFrames.P6Hybrid.Quarter.QuarterPieces
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

/-- H/Z envelope, using Z only in its proved finite-size domain. -/
def W (r m p : ℕ) : ℕ :=
  if p % 6 = 1 ∨ p % 6 = 5 then
    if r + 2*m ≤ 2*p then min (Hb r m p) (2*r+2*m-Sv r m p)
    else Hb r m p
  else 2*r+2*m

theorem trop_le {r m p : ℕ} (hp : p.Prime) (hr : 16 ≤ r) :
    tropVal (HW (p6Inst r m).lev p r m) ≤ W r m p := by
  unfold W
  split_ifs with hc hn
  · have hH := p6_trop_H (r := r) (m := m) (p := p) (by omega) hp.pos
    have hZ := p6_trop_Z (r := r) (m := m) hp (by omega) hc hn
    omega
  · exact p6_trop_H (by omega) hp.pos
  · have h := trop_D1 (lev := (p6Inst r m).lev) p r m
    have : (tropVal (HW (p6Inst r m).lev p r m) : ℚ) ≤ ((2*r+2*m : ℕ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast this

macro "quarter_omega" : tactic =>
  `(tactic| (intro p hs ht hc; have hk := kq6_cases p; unfold W Sv Hb; split_ifs <;> omega))

section
variable {r m : ℕ} (hm1 : r ≤ 4*m) (hm2 : 4*m ≤ r+3) (hr : 100 ≤ r)
include hm1 hm2 hr

lemma c1_1 : Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 1 4 1 2 11 (-4) 100 4) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c1_2 : Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 1 2 3 4 9 (0) 100 4) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c1_3 : Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 3 4 15 16 9 (0) 100 4) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c1_4 : Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 15 16 9 8 21 (-8) 100 6) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c1_5 : Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 9 8 3 2 15 (-8) 100 3) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c1_6 : Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 3 2 2 1 6 (-2) 100 3) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c1_7 : Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 2 1 3 1 6 (-1) 100 6) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c1_8 : Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 3 1 9 2 9 (-2) 100 6) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c1_9 : Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 9 2 9 1 0 (0) 100 1) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c5_1 : Covers (5 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 1 4 1 2 11 (-4) 100 4) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c5_2 : Covers (5 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 1 2 3 4 9 (0) 100 4) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c5_3 : Covers (5 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 3 4 5 6 9 (0) 100 4) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c5_4 : Covers (5 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 5 6 1 1 7 (-3) 100 2) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c5_5 : Covers (5 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 1 1 3 2 4 (-2) 100 1) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c5_6 : Covers (5 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 3 2 2 1 5 (-2) 100 2) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c5_7 : Covers (5 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 2 1 3 1 3 (-1) 100 2) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

lemma c5_8 : Covers (5 : ZMod 6) (fun p => (W r m p : ℝ)) r (mkPiece 3 1 9 1 0 (0) 100 1) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by quarter_omega)

end
end CatalanArchive.CatalanFrames.P6Hybrid.Quarter.QuarterPieces
#print axioms CatalanArchive.CatalanFrames.P6Hybrid.Quarter.QuarterPieces.trop_le
