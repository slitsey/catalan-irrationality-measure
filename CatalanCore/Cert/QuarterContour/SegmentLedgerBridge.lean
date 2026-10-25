module
public import CatalanCore.Cert.QuarterCompute.SegmentLedger
public import CatalanCore.Cert.QuarterContour.SegmentFold
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.SegmentLedgerBridge
open CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.QuarterCompute

lemma svalues_eq (p q : ℤ) (bs : List QBox) : SegmentFold.svalues p q bs = SegmentLedger.svalues p q bs := by rfl
lemma shape_eq (b : QBox) : SegmentLedger.shape b = QuarterContour.segShape b := by rfl

/-- The coordinate-only integer cover proves exact real-axis coverage. -/
theorem chainCovers_sound (bs : List QBox) (lo hi : ℤ)
    (hc : SegmentLedger.chainCovers bs lo hi = true) (x : ℝ)
    (hxlo : (lo : ℝ)/2^40 ≤ x) (hxhi : x ≤ (hi : ℝ)/2^40) :
    ∃ b ∈ bs, (b.1.1 : ℝ)/2^40 ≤ x ∧ x ≤ (b.1.2.1 : ℝ)/2^40 := by
  induction bs generalizing lo with
  | nil => simp [SegmentLedger.chainCovers] at hc
  | cons b bs ih =>
    simp only [SegmentLedger.chainCovers,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true] at hc
    have ha : (b.1.1 : ℝ)/2^40 ≤ x := by
      have hh : (b.1.1 : ℝ) ≤ lo := by exact_mod_cast hc.1
      exact (div_le_div_of_nonneg_right hh (by positivity)).trans hxlo
    by_cases hb : x ≤ (b.1.2.1 : ℝ)/2^40
    · exact ⟨b,by simp,ha,hb⟩
    · have ht : SegmentLedger.chainCovers bs b.1.2.1 hi = true := by
        rcases hc.2 with h | h
        · have hh : (hi : ℝ) ≤ b.1.2.1 := by exact_mod_cast h
          exact False.elim (hb (hxhi.trans (div_le_div_of_nonneg_right hh (by positivity))))
        · exact h
      obtain ⟨c,hc,h1,h2⟩ := ih b.1.2.1 ht (le_of_not_ge hb)
      exact ⟨c,by simp [hc],h1,h2⟩

theorem intervalCovers (bs : List QBox) (lo hi : ℤ)
    (hc : SegmentLedger.chainCovers bs lo hi = true) :
    IntervalCovers (bs.map QuarterContour.axisInterval) ((lo : ℚ)/2^40) ((hi : ℚ)/2^40) := by
  intro x hx hy
  push_cast at hx hy
  obtain ⟨b,hb,h1,h2⟩ := chainCovers_sound bs lo hi hc x hx hy
  refine ⟨QuarterContour.axisInterval b,List.mem_map.mpr ⟨b,hb,rfl⟩,?_,?_⟩
  · simpa only [QuarterContour.axisInterval,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat] using h1
  · simpa only [QuarterContour.axisInterval,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat] using h2
end CatalanCore.Cert.QuarterContour.SegmentLedgerBridge
#print axioms CatalanCore.Cert.QuarterContour.SegmentLedgerBridge.intervalCovers
