module
public import CatalanCore.Arith.Hybrid.ChainSums
public import CatalanCore.Arith.Hybrid.ChainTransport
public import CatalanCore.Arith.Hybrid.LemmaE.Bridge
@[expose] public section
open Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainClasses
variable {p : ℕ} [Fact p.Prime]

lemma good_constants_cng {a b : ℚ} {v : ZMod p}
    (ha : Good p a v) (hb : Good p b v) : LemmaE.Cng p (C a) (C b) := by
  apply (LemmaE.cng_C_iff ha.mem hb.mem).mpr
  exact ha.eq.trans hb.eq.symm

/-- Every leading squared entry transports with its two cumulative data and displacement. -/
theorem square_entry_cng {Fr : Frame} {o N A B A' B' : ℕ}
    (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hA : A<N) (hB : B<N) (hA' : A'<N) (hB' : B'<N)
    (hd : (B : ℤ)-A = (B' : ℤ)-A')
    (hLA : ∀ v : ℕ→ZMod p, Lv (singularNodes p o N) v A = Lv (singularNodes p o N) v A')
    (hLB : ∀ v : ℕ→ZMod p, Lv (singularNodes p o N) v B = Lv (singularNodes p o N) v B') :
    LemmaE.Cng p (C ((p : ℚ)^2*Fr.Mn A B)) (C ((p : ℚ)^2*Fr.Mn A' B')) := by
  rcases lt_trichotomy A B with hab | hab | hab
  · have hab' : A'<B' := by omega
    have he : B-A=B'-A' := by omega
    have ga := good_Mn_square_uniform hL hp5 hN hab hB
    have gb := good_Mn_square_uniform hL hp5 hN hab' hB'
    rw [delta_interval_eq_Lv hab.le hB] at ga
    rw [delta_interval_eq_Lv hab'.le hB', ←hLA _, ←hLB _, ←he] at gb
    exact good_constants_cng ga gb
  · subst B
    have he : B'=A' := by omega
    subst B'
    have ga := good_Mn_diag_uniform hL hp5 hN hA
    have gb := good_Mn_diag_uniform hL hp5 hN hA'
    rw [dsq_prefix_eq_Lv hA] at ga
    rw [dsq_prefix_eq_Lv hA', ←hLA _] at gb
    exact good_constants_cng ga gb
  · have hba' : B'<A' := by omega
    have he : A-B=A'-B' := by omega
    have ga := good_Mn_square_uniform hL hp5 hN hab hA
    have gb := good_Mn_square_uniform hL hp5 hN hba' hA'
    rw [delta_interval_eq_Lv hab.le hA] at ga
    rw [delta_interval_eq_Lv hba'.le hA', ←hLA _, ←hLB _, ←he] at gb
    simpa only [Mn_symm] using good_constants_cng ga gb

/-- Concrete core-chain leading blocks, with no bound on their length. -/
theorem square_chain_cng {Fr : Frame} {o N r z w : ℕ}
    (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hzw : z≤w) (h : NoCut (Cut p r (Singular p o)) z w)
    (i j : ChainIndex p r z) :
    LemmaE.Cng p (C ((p : ℚ)^2*Fr.Mn (chainNode i).val (chainNode j).val))
      (C ((p : ℚ)^2*Fr.Mn (chainNode (chainTransport hzw h i)).val
        (chainNode (chainTransport hzw h j)).val)) := by
  apply square_entry_cng hL hp5 hN
    (lt_of_lt_of_le (chainNode i).isLt hr) (lt_of_lt_of_le (chainNode j).isLt hr)
    (lt_of_lt_of_le (chainNode (chainTransport hzw h i)).isLt hr)
    (lt_of_lt_of_le (chainNode (chainTransport hzw h j)).isLt hr)
  · rw [chainNode_transport hzw h i, chainNode_transport hzw h j]
    ring
  · exact fun v => uniform_Lv_chain_eq hL.o_le hzw h v i
  · exact fun v => uniform_Lv_chain_eq hL.o_le hzw h v j

/-- The source column transports alongside its corresponding core node. -/
theorem square_zone_chain_cng {Fr : Frame} {o N r z w : ℕ}
    (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hz : z<N) (hw : w<N) (hzw : z≤w)
    (h : NoCut (Cut p r (Singular p o)) z w) (i : ChainIndex p r z) :
    LemmaE.Cng p (C ((p : ℚ)^2*Fr.Mn (chainNode i).val z))
      (C ((p : ℚ)^2*Fr.Mn (chainNode (chainTransport hzw h i)).val w)) := by
  apply square_entry_cng hL hp5 hN
    (lt_of_lt_of_le (chainNode i).isLt hr) hz
    (lt_of_lt_of_le (chainNode (chainTransport hzw h i)).isLt hr) hw
  · rw [chainNode_transport hzw h i]
    ring
  · exact fun v => uniform_Lv_chain_eq hL.o_le hzw h v i
  · exact fun v => uniform_Lv_zone_eq hL.o_le hzw h v
end CatalanCore.Arith.Hybrid.ChainClasses
#print axioms CatalanCore.Arith.Hybrid.ChainClasses.square_chain_cng
