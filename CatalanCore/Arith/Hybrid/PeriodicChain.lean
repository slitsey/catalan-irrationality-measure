module
public import CatalanCore.Arith.Hybrid.PeriodicEntries
public import CatalanCore.Arith.Hybrid.ChainAlgebra

@[expose] public section
open Finset Polynomial Matrix CatalanCore
namespace CatalanCore.Arith.Hybrid.Periodic
open ChainClasses LemmaE
variable {Fr : Frame} {p N : ℕ} [Fact p.Prime]

lemma prefix_nocut {K : Type*} [AddCommGroup K] (v : ℕ→K) (sing : ℤ→Prop)
    {a b : ℕ} (hab : a≤b) (hb : b<N)
    (hv : ∀k,1≤k→k<N→¬sing k→v k=0) (hc : NoCut sing a b) :
    (∑k∈Icc 1 a,v k)=∑k∈Icc 1 b,v k := by
  have he (n : ℕ) : Icc 1 n=Ioc 0 n := by ext k;simp only [mem_Icc,mem_Ioc];omega
  rw [he,he,←Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  have hz : (∑k∈Ioc a b,v k)=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk':=mem_Ioc.mp hk
    exact hv k (by omega) (by omega) (hc k (by exact_mod_cast hk'.1) (by exact_mod_cast hk'.2))
  rw [hz,add_zero]

namespace PoleData
lemma prefix_chain (D : PoleData Fr p N) {K : Type*} [AddCommGroup K]
    (v : ℕ→K) (hv : ∀k,1≤k→k<N→¬D.singular k→v k=0)
    {r z w : ℕ} (hr : r≤N) (hzw : z≤w)
    (hc : NoCut (Cut p r D.singular) z w) (i : ChainIndex p r z) :
    (∑k∈Icc 1 (chainNode i).val,v k)=
      ∑k∈Icc 1 (chainNode (chainTransport hzw hc i)).val,v k := by
  let e:=chainTransport hzw hc
  have ht := chainNode_transport hzw hc i
  have hab : (chainNode i).val≤(chainNode (e i)).val := by dsimp [e] at *;omega
  apply prefix_nocut v D.singular hab ((chainNode (e i)).isLt.trans_le hr) hv
  have H:=noCut_translate (i:=i.val) D.periodic hc
  have he : (e i).val=i.val := rfl
  rw [chainNode_cast,chainNode_cast,he]
  exact H

lemma V_chain (D : PoleData Fr p N) {r z w : ℕ} (hr : r≤N) (hzw : z≤w)
    (hc : NoCut (Cut p r D.singular) z w) (i : ChainIndex p r z) :
    D.V (chainNode i).val=D.V (chainNode (chainTransport hzw hc i)).val :=
  D.prefix_chain D.dv (fun k hk hkN hs=>D.dv_zero hk hkN hs) hr hzw hc i
lemma W_chain (D : PoleData Fr p N) {r z w : ℕ} (hr : r≤N) (hzw : z≤w)
    (hc : NoCut (Cut p r D.singular) z w) (i : ChainIndex p r z) :
    D.W (chainNode i).val=D.W (chainNode (chainTransport hzw hc i)).val :=
  D.prefix_chain D.sv (fun k hk hkN hs=>D.sv_zero hk hkN hs) hr hzw hc i
lemma V_zone (D : PoleData Fr p N) {r z w : ℕ} (hzw : z≤w) (hw : w<N)
    (hc : NoCut (Cut p r D.singular) z w) : D.V z=D.V w :=
  prefix_nocut D.dv D.singular hzw hw (fun k hk hkN hs=>D.dv_zero hk hkN hs)
    (fun t h1 h2 hs=>hc t h1 h2 (Or.inl hs))

lemma square_cng (D : PoleData Fr p N) (hN : N<p*p) {a b a' b' : ℕ}
    (ha : a<N) (hb : b<N) (ha' : a'<N) (hb' : b'<N)
    (hd : (b:ℤ)-a=(b':ℤ)-a') (hVa : D.V a=D.V a') (hVb : D.V b=D.V b')
    (hWa : D.W a=D.W a') :
    Cng p (C ((p:ℚ)^2*Fr.Mn a b)) (C ((p:ℚ)^2*Fr.Mn a' b')) := by
  rcases lt_trichotomy a b with h|h|h
  · have h' : a'<b' := by omega
    have he : b-a=b'-a' := by omega
    apply good_constants_cng (D.good_square hN h hb)
    simpa only [he,hVa,hVb] using D.good_square hN h' hb'
  · subst b
    have he : b'=a' := by omega
    subst b'
    apply good_constants_cng (D.good_diagonal ha)
    simpa only [hWa] using D.good_diagonal ha'
  · have h' : b'<a' := by omega
    have he : a-b=a'-b' := by omega
    rw [Mn_symm (A:=a) (B:=b),Mn_symm (A:=a') (B:=b')]
    apply good_constants_cng (D.good_square hN h ha)
    simpa only [he,hVa,hVb] using D.good_square hN h' ha'

lemma chain_cng (D : PoleData Fr p N) (hN : N<p*p) {r z w : ℕ}
    (hr : r≤N) (hzw : z≤w) (hc : NoCut (Cut p r D.singular) z w)
    (i j : ChainIndex p r z) :
    Cng p (C ((p:ℚ)^2*Fr.Mn (chainNode i).val (chainNode j).val))
      (C ((p:ℚ)^2*Fr.Mn (chainNode (chainTransport hzw hc i)).val
        (chainNode (chainTransport hzw hc j)).val)) := by
  apply D.square_cng hN ((chainNode i).isLt.trans_le hr) ((chainNode j).isLt.trans_le hr)
    ((chainNode (chainTransport hzw hc i)).isLt.trans_le hr)
    ((chainNode (chainTransport hzw hc j)).isLt.trans_le hr)
  · rw [chainNode_transport hzw hc i,chainNode_transport hzw hc j];ring
  · exact D.V_chain hr hzw hc i
  · exact D.V_chain hr hzw hc j
  · exact D.W_chain hr hzw hc i

lemma zone_chain_cng (D : PoleData Fr p N) (hN : N<p*p) {r z w : ℕ}
    (hr : r≤N) (hz : z<N) (hw : w<N) (hzw : z≤w)
    (hc : NoCut (Cut p r D.singular) z w) (i : ChainIndex p r z) :
    Cng p (C ((p:ℚ)^2*Fr.Mn (chainNode i).val z))
      (C ((p:ℚ)^2*Fr.Mn (chainNode (chainTransport hzw hc i)).val w)) := by
  apply D.square_cng hN ((chainNode i).isLt.trans_le hr) hz
    ((chainNode (chainTransport hzw hc i)).isLt.trans_le hr) hw
  · rw [chainNode_transport hzw hc i];ring
  · exact D.V_chain hr hzw hc i
  · exact D.V_zone hzw hw hc
  · exact D.W_chain hr hzw hc i

end PoleData
end CatalanCore.Arith.Hybrid.Periodic
