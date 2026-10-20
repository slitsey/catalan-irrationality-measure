module
public import CatalanCore.Arith.Hybrid.Pieces
@[expose] public section
open Finset Filter Topology CatalanCore.NT
namespace CatalanCore.Arith.Hybrid

/-- Lower affine prime sums, reusing the upper affine theorem on a complement. -/
theorem piece_sum_lower {M : ℕ} [NeZero M] {c : ZMod M} (hc : IsUnit c)
    {s t a b C K : ℝ} (hs : 0<s) (hst : s≤t) (hC : 0≤C)
    (hK : 0≤K) (hKs : a+b*s≤K) (hKt : a+b*t≤K)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r : ℕ in atTop, ∀ w : ℕ→ℝ,
      (∀ p, ⌊s*r⌋₊<p → p≤⌊t*r⌋₊ → p.Prime → (p : ZMod M)=c →
        a*r+b*p-C≤w p) →
      (r : ℝ)^2*((a*(t-s)+b*(t^2-s^2)/2)/(M.totient : ℝ)-ε) ≤
        clsSum M c w ⌊s*r⌋₊ ⌊t*r⌋₊ := by
  have he2 : 0<ε/2 := by positivity
  have hd : 0<ε/(2*(K+1)) := by positivity
  have hup := piece_sum hc hs hst hC (show 0≤K-a+(-b)*s by linarith)
    (show 0≤K-a+(-b)*t by linarith) he2
  have htheta := (tendsto_natCast_atTop_atTop.eventually
    (theta_interval_abs_le hc hs hst hd))
  filter_upwards [hup, htheta] with r hr ht w hw
  have hcomp := hr (fun p => K*r-w p) (by
    intro p hp hpt hpr hpc
    have := hw p hp hpt hpr hpc
    linarith)
  have hAB : ⌊s*(r : ℝ)⌋₊≤⌊t*(r : ℝ)⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right hst (Nat.cast_nonneg r))
  have hsum : clsSum M c (fun p => K*r-w p) ⌊s*r⌋₊ ⌊t*r⌋₊ =
      K*r*(thetaClass M c (t*r)-thetaClass M c (s*r)) -
        clsSum M c w ⌊s*r⌋₊ ⌊t*r⌋₊ := by
    unfold thetaClass
    rw [thetaClassN_sub M c hAB]
    unfold clsSum
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum] at hcomp
  have hlower := (abs_le.mp ht).1
  have hr0 : (0 : ℝ)≤r := Nat.cast_nonneg r
  have hbase := mul_le_mul_of_nonneg_left hlower (mul_nonneg hK hr0)
  have herr : K*(ε/(2*(K+1)))≤ε/2 := by
    have heq : K*(ε/(2*(K+1)))=ε/2*(K/(K+1)) := by field_simp <;> ring
    rw [heq]
    have hfrac : K/(K+1)≤1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have hφ : (M.totient : ℝ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))).ne'
  have hid : K*(t-s)/(M.totient : ℝ) -
      ((K-a)*(t-s)+(-b)*(t^2-s^2)/2)/(M.totient : ℝ) =
      (a*(t-s)+b*(t^2-s^2)/2)/(M.totient : ℝ) := by ring
  have hbound : (r : ℝ)^2 * ((a*(t-s)+b*(t^2-s^2)/2)/(M.totient : ℝ)-ε/2-K*(ε/(2*(K+1)))) ≤
      clsSum M c w ⌊s*r⌋₊ ⌊t*r⌋₊ := by
    rw [← hid]
    simp only [div_eq_mul_inv] at hcomp hbase ⊢
    nlinarith [hcomp, hbase]
  exact le_trans (by nlinarith [sq_nonneg (r : ℝ)]) hbound

def LowerCovers {M : ℕ} (c : ZMod M) (w : ℕ→ℝ) (r : ℕ) (P : Piece) : Prop :=
  ∀ p, ⌊P.s*r⌋₊<p → p≤⌊P.t*r⌋₊ → p.Prime → (p : ZMod M)=c →
    P.α*r+P.β*p-P.C≤w p

theorem piece_sum_lower_auto {M : ℕ} [NeZero M] {c : ZMod M} (hc : IsUnit c)
    (P : Piece) (hs : 0<P.s) (hst : P.s≤P.t) (hC : 0≤P.C)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r : ℕ in atTop, ∀w : ℕ→ℝ, LowerCovers c w r P →
      (r : ℝ)^2*(P.int/(M.totient : ℝ)-ε)≤clsSum M c w ⌊P.s*r⌋₊ ⌊P.t*r⌋₊ := by
  exact piece_sum_lower hc hs hst hC (le_max_left 0 _)
    (le_trans (le_max_left _ _) (le_max_right 0 _))
    (le_trans (le_max_right _ _) (le_max_right 0 _)) hε

theorem finite_piece_sum_lower {ι : Type*} {M : ℕ} [NeZero M]
    (s : Finset ι) (c : ι→ZMod M) (P : ι→Piece)
    (hc : ∀i∈s, IsUnit (c i))
    (hP : ∀i∈s, 0<(P i).s ∧ (P i).s≤(P i).t ∧ 0≤(P i).C)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r : ℕ in atTop, ∀w : ℕ→ℝ,
      (∀i∈s, LowerCovers (c i) w r (P i)) →
      (r : ℝ)^2*((∑i∈s,(P i).int)/(M.totient : ℝ)-ε)≤
        ∑i∈s,clsSum M (c i) w ⌊(P i).s*r⌋₊ ⌊(P i).t*r⌋₊ := by
  have hd : 0<ε/((s.card : ℝ)+1) := by positivity
  have hall : ∀i∈s, ∀ᶠ r : ℕ in atTop, ∀w : ℕ→ℝ,
      LowerCovers (c i) w r (P i) →
      (r : ℝ)^2*((P i).int/(M.totient : ℝ)-ε/((s.card : ℝ)+1))≤
        clsSum M (c i) w ⌊(P i).s*r⌋₊ ⌊(P i).t*r⌋₊ := by
    intro i hi
    exact piece_sum_lower_auto (hc i hi) (P i) (hP i hi).1 (hP i hi).2.1 (hP i hi).2.2 hd
  filter_upwards [(Filter.eventually_all_finset s).2 hall] with r hr w hw
  have hh := Finset.sum_le_sum (fun i hi => hr i hi w (hw i hi))
  have herr : (s.card : ℝ)*(ε/((s.card : ℝ)+1))≤ε := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<(s.card : ℝ)+1)).2
    nlinarith
  have he : (∑i∈s,(r : ℝ)^2*((P i).int/(M.totient : ℝ)-ε/((s.card : ℝ)+1))) =
      (r : ℝ)^2*((∑i∈s,(P i).int)/(M.totient : ℝ)-(s.card : ℝ)*(ε/((s.card : ℝ)+1))) := by
    rw [←Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_div]
    simp
  rw [he] at hh
  exact le_trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg (r : ℝ))) hh

#print axioms finite_piece_sum_lower
end CatalanCore.Arith.Hybrid
