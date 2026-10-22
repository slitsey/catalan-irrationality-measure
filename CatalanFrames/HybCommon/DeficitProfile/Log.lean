module
public import CatalanFrames.HybCommon.DeficitProfile.Weight
@[expose] public section
open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon
variable {Fr : Frame} {I : HybInst Fr} {o : ℕ}

theorem profileT_le_weight {L : List DeficitRow} (hD : RowData L) {Lc cm : ℕ} (T : TropFacts I o) (B : BadInfo I Lc cm)
    (r p : ℕ) (hr : 400≤r) (hp : p.Prime) :
    (profileTL L o I r p : ℝ)≤(if p∈I.cd.bad then exBad cm r (r/8) else 0)+
      ((2*(r+r/8)*cntG I r (r/8) p : ℕ) : ℝ)+
      (if p∈I.cd.bad then 0 else profileWeight I o r p) := by
  have hold := TfunG_leG T B r p (by omega) hp
  have hW := WTG_le_profileWeight I o r p
  by_cases hb : p∈I.cd.bad
  · have hn : ¬profileSupportL L o r p := by
      intro hs
      have hh := profileSupport_lower hD hs
      have hp3 := B.bad_le p hb
      omega
    simpa only [profileTL,if_neg hn,hb,if_true] using hold
  · simp only [hb,if_false,zero_add] at hold ⊢
    by_cases hs : profileSupportL L o r p
    · simp only [profileTL,if_pos hs,Nat.cast_max]
      apply max_le
      · linarith
      · have hbase := profileBaseline_le_weight hD (I := I) hs
        have hn : (0 : ℝ)≤((2*(r+r/8)*cntG I r (r/8) p : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
    · simp only [profileTL,if_neg hs]
      linarith

/-- The uplift uses only existing affine pieces, so its leading content budget
is exactly the old budget.  All new arithmetic savings enter separately. -/
theorem profile_logDhybT_le {L : List DeficitRow} (hD : RowData L) {Lc cm : ℕ} (T : TropFacts I o) (B : BadInfo I Lc cm)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠr : ℕ in atTop, ∀δ : ℕ→ℕ, DefHypT I r (r/8) (profileTL L o I r) δ →
      Real.log (DhybT I r (r/8) (profileTL L o I r) δ)≤
        (24994314577/6665218560+ε)*(r : ℝ)^2-
          ∑p∈(Finset.range (Bnd I r (r/8))).filter Nat.Prime, (δ p : ℝ)*Real.log p := by
  apply logDhybT_le_weight T B (profileTL L o I) (profileWeight I o)
    (profileWeight_nonneg I o) (fun r hr p hp => profileT_le_weight hD T B r p hr hp)
    ?_ ?_ (fun ε hε => profileWeight_class1 T hε) (fun ε hε => profileWeight_class3 T hε) hε
  · intro r hr p hp h5 hm ht
    rw [profileWeight_tail I o r p (by omega)]
    have hz := XG_tail1 T r p hp h5 hm ht
    have he := eNG_tail T.ho (by omega : 16≤r) (r := r) (p := p) (by omega)
    simp [WTG,WG,hz,he]
  · intro r hr p hp h5 hm ht
    rw [profileWeight_tail I o r p (by omega)]
    have hz := XG_tail3 T r p hp h5 hm ht
    have he := eNG_tail T.ho (by omega : 16≤r) (r := r) (p := p) ht
    simp [WTG,WG,hz,he]

end CatalanFrames.HybCommon
