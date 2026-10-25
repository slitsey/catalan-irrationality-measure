module
public import CatalanFrames.HybGen.TropM
@[expose] public section
open CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
namespace CatalanFrames.HybGen
variable {Fr : Frame} {I : HybInst Fr} {Good : ℕ → Prop}
variable (T : LevelFacts I Good (fun q c => c < I.cd.kq q))
include T
theorem XGm_D2_good (r m p : ℕ) (hp : p.Prime) (hG : Good p) (hm : 2*m < p)
    (hu : p ≤ r) (hk : I.cd.kq p ≤ r) :
    ∃ u L : ℕ, I.cd.kq p+p ≤ u+r ∧ u ≤ r ∧ L ≤ u ∧ L ≤ 2*m ∧
      XGm I r m p ≤ 2*(r-u)+2*m+L := by
  obtain ⟨hq,hb⟩ := T.good p hp hG
  exact val_D2 p r m (I.cd.kq p) (lev := I.lev) hp.one_lt.le
    (fun c hc => T.high p c hp.one_lt.le hc) hm hu hk (fun c => T.zero_iff p c hq hb)
theorem XGm_D45_good (r m p : ℕ) (hp : p.Prime) (hG : Good p)
    (hr : r < p) (hmr : 2*m ≤ r) :
    XGm I r m p ≤ 2*(r-I.cd.kq p)+2*m+(2*m-(p-r)) := by
  obtain ⟨hq,hb⟩ := T.good p hp hG
  exact val_D45 p r m (I.cd.kq p) (lev := I.lev) hr hmr (fun c => T.zero_iff p c hq hb)
theorem XGm_D6_good (r m p : ℕ) (hp : p.Prime) (hG : Good p)
    (hN : r+2*m ≤ p) (hk : r ≤ I.cd.kq p) :
    XGm I r m p ≤ 2*m-(I.cd.kq p-r) := by
  obtain ⟨hq,hb⟩ := T.good p hp hG
  exact val_D6 p r m (I.cd.kq p) (lev := I.lev) hN hk (fun c => T.zero_iff p c hq hb)
end CatalanFrames.HybGen
#print axioms CatalanFrames.HybGen.XGm_D2_good
#print axioms CatalanFrames.HybGen.XGm_D45_good
#print axioms CatalanFrames.HybGen.XGm_D6_good
