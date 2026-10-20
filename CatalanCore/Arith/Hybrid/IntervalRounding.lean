module
public import Mathlib.Tactic
@[expose] public section
namespace CatalanCore.Arith.Hybrid
lemma nat_sub_cast_ge (a b : ℕ) : (a : ℝ)-b≤((a-b : ℕ) : ℝ) := by
  by_cases h : b≤a
  · rw [Nat.cast_sub h]
  · have hb : a≤b := by omega
    rw [Nat.sub_eq_zero_of_le hb, Nat.cast_zero]
    exact sub_nonpos.mpr (by exact_mod_cast hb)

lemma interval_low_rounding (r p m a b : ℕ) (A B : ℝ)
    (hp : p≤r)
    (hmL : (r : ℝ)/8-1≤m) (hmU : (m : ℝ)≤r/8)
    (ha : (a : ℝ)≤max (r : ℝ) A+1)
    (hb : min (5*(r : ℝ)/4) (min B ((r : ℝ)+p))-2≤b) :
    min ((r : ℝ)/8-p+min (5*(r : ℝ)/4) (min B ((r : ℝ)+p))-max (r : ℝ) A)
      (min (5*(r : ℝ)/4) (min B ((r : ℝ)+p))-9*(r : ℝ)/8)-8≤
      ((m+(b-max a (r+2*m-p))-(p+4) : ℕ) : ℝ) := by
  have hpN : p≤r+2*m := by omega
  have hN : ((r+2*m-p : ℕ) : ℝ)≤5*(r : ℝ)/4-p := by
    rw [Nat.cast_sub hpN]
    push_cast
    linarith
  have hmax : ((max a (r+2*m-p) : ℕ) : ℝ)≤
      max (max (r : ℝ) A) (5*(r : ℝ)/4-p)+1 := by
    rw [Nat.cast_max]
    apply max_le
    · exact ha.trans (by have := le_max_left (max (r : ℝ) A) (5*(r : ℝ)/4-p); linarith)
    · exact hN.trans (by have := le_max_right (max (r : ℝ) A) (5*(r : ℝ)/4-p); linarith)
  have hn := nat_sub_cast_ge b (max a (r+2*m-p))
  have hd := nat_sub_cast_ge (m+(b-max a (r+2*m-p))) (p+4)
  push_cast at hd
  have ht : (r : ℝ)/8-p+min (5*(r : ℝ)/4) (min B ((r : ℝ)+p))-
      max (max (r : ℝ) A) (5*(r : ℝ)/4-p)-8≤
      ((m+(b-max a (r+2*m-p))-(p+4) : ℕ) : ℝ) := by linarith
  have he : min ((r : ℝ)/8-p+min (5*(r : ℝ)/4) (min B ((r : ℝ)+p))-max (r : ℝ) A)
      (min (5*(r : ℝ)/4) (min B ((r : ℝ)+p))-9*(r : ℝ)/8) =
      (r : ℝ)/8-p+min (5*(r : ℝ)/4) (min B ((r : ℝ)+p))-
        max (max (r : ℝ) A) (5*(r : ℝ)/4-p) := by
    rcases le_total (max (r : ℝ) A) (5*(r : ℝ)/4-p) with h|h
    · rw [max_eq_right h, min_eq_right (by linarith)]
      ring
    · rw [max_eq_left h, min_eq_left (by linarith)]
  rw [he]
  exact ht

lemma interval_nc_rounding (r m a b : ℕ) (A B : ℝ)
    (hmU : (m : ℝ)≤r/8) (ha : (a : ℝ)≤max (r : ℝ) A+1)
    (hb : min (5*(r : ℝ)/4) B-2≤b) :
    min (5*(r : ℝ)/4) B-max (r : ℝ) A-(r : ℝ)/8-7≤
      ((b-a-(m+4) : ℕ) : ℝ) := by
  have hn := nat_sub_cast_ge b a
  have hd := nat_sub_cast_ge (b-a) (m+4)
  push_cast at hd
  linarith
end CatalanCore.Arith.Hybrid
