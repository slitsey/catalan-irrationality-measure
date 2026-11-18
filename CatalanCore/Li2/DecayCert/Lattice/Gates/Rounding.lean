module
public import CatalanCore.Li2.DecayCert.Rounded.Arithmetic
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeGate

def scalarFloorCheck (S : ℤ) (q : ℚ) (a : ℤ) : Bool :=
  decide (0<S ∧ a=q.num*S/(q.den:ℤ))

theorem scaled_ediv_error (S raw D : ℤ) (hS : 0<S) (hD : D≠0) :
    |(raw:ℚ)/(D:ℚ)/(S:ℚ)-((raw/D:ℤ):ℚ)/(S:ℚ)|≤1/(S:ℚ) := by
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hS
  rw [← sub_div,abs_div,abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  simpa only [abs_sub_comm] using Rounded.ediv_error_Q raw D hD

theorem scalarFloorCheck_sound (S : ℤ) (q : ℚ) (a : ℤ)
    (hc : scalarFloorCheck S q a=true) :
    |q-(a:ℚ)/(S:ℚ)|≤1/(S:ℚ) := by
  have hh : 0<S ∧ a=q.num*S/(q.den:ℤ) := of_decide_eq_true hc
  have hd : (q.den:ℤ)≠0 := by exact_mod_cast q.den_nz
  have hs : (S:ℚ)≠0 := by exact_mod_cast hh.1.ne'
  have hdQ : (q.den:ℚ)≠0 := by exact_mod_cast q.den_nz
  have he : ((q.num*S:ℤ):ℚ)/(q.den:ℚ)/(S:ℚ)=q := by
    calc
      _=(q.num:ℚ)/(q.den:ℚ) := by push_cast; field_simp
      _=q := Rat.num_div_den q
  have h := scaled_ediv_error S (q.num*S) (q.den:ℤ) hh.1 hd
  rw [hh.2]
  simpa only [Int.cast_natCast,he] using h

theorem weighted_floor_sum (S : ℤ) (n : ℕ) (q : ℕ→ℚ) (a w : ℕ→ℤ)
    (hS : 0<S) (h : ∀ i<n,scalarFloorCheck S (q i) (a i)=true) :
    |(∑ i ∈ Finset.range n,q i*(w i:ℚ))-
        ((∑ i ∈ Finset.range n,a i*w i:ℤ):ℚ)/(S:ℚ)|≤
      ((∑ i ∈ Finset.range n,|w i|:ℤ):ℚ)/(S:ℚ) := by
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hS
  have he : ((∑ i ∈ Finset.range n,a i*w i:ℤ):ℚ)/(S:ℚ)=
      ∑ i ∈ Finset.range n,(a i:ℚ)*(w i:ℚ)/(S:ℚ) := by
    push_cast
    rw [Finset.sum_div]
  rw [he,← Finset.sum_sub_distrib]
  calc
    _≤∑ i ∈ Finset.range n,|q i*(w i:ℚ)-(a i:ℚ)*(w i:ℚ)/(S:ℚ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ i ∈ Finset.range n,(|w i|:ℚ)/(S:ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := scalarFloorCheck_sound S (q i) (a i) (h i (Finset.mem_range.mp hi))
      have hterm : q i*(w i:ℚ)-(a i:ℚ)*(w i:ℚ)/(S:ℚ)=
          (q i-(a i:ℚ)/(S:ℚ))*(w i:ℚ) := by ring
      rw [hterm,abs_mul]
      calc
        _≤(1/(S:ℚ))*|(w i:ℚ)| := mul_le_mul_of_nonneg_right hh (abs_nonneg _)
        _=_ := by ring
    _=_ := by push_cast;rw [Finset.sum_div]

theorem rescale_rounded_sum (S G D acc out En E : ℤ) (q : ℚ)
    (hS : 0<S) (hD : 0<D)
    (hclose : |q-(acc:ℚ)/(S:ℚ)|≤(En:ℚ)/(S:ℚ))
    (hout : out=G*acc/D) (hbudget : |G| *En≤(E-1)*D) :
    |(G:ℚ)/(D:ℚ)*q-(out:ℚ)/(S:ℚ)|≤(E:ℚ)/(S:ℚ) := by
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hS
  have hd : (0:ℚ)<(D:ℚ) := by exact_mod_cast hD
  have hr := scaled_ediv_error S (G*acc) D hS hD.ne'
  rw [← hout] at hr
  have he : (G:ℚ)/(D:ℚ)*q-(out:ℚ)/(S:ℚ)=
      (G:ℚ)/(D:ℚ)*(q-(acc:ℚ)/(S:ℚ))+
        (((G*acc:ℤ):ℚ)/(D:ℚ)/(S:ℚ)-(out:ℚ)/(S:ℚ)) := by push_cast;ring
  rw [he]
  calc
    _≤|(G:ℚ)/(D:ℚ)*(q-(acc:ℚ)/(S:ℚ))|+
        |((G*acc:ℤ):ℚ)/(D:ℚ)/(S:ℚ)-(out:ℚ)/(S:ℚ)| := abs_add_le _ _
    _≤((|G|:ℤ):ℚ)/(D:ℚ)*((En:ℚ)/(S:ℚ))+1/(S:ℚ) := by
      apply add_le_add _ hr
      rw [abs_mul,abs_div,abs_of_pos hd,← Int.cast_abs]
      exact mul_le_mul_of_nonneg_left hclose (div_nonneg (by exact_mod_cast abs_nonneg G) hd.le)
    _=(((|G|:ℤ):ℚ)*(En:ℚ)/(D:ℚ)+1)/(S:ℚ) := by ring
    _≤(E:ℚ)/(S:ℚ) := by
      apply (div_le_div_iff_of_pos_right hs).2
      have hb : ((|G|:ℤ):ℚ)*(En:ℚ)≤((E:ℚ)-1)*(D:ℚ) := by exact_mod_cast hbudget
      have hh := (div_le_iff₀ hd).2 hb
      linarith

#print axioms scalarFloorCheck_sound
#print axioms weighted_floor_sum
#print axioms rescale_rounded_sum
/-- Bind the non-rational seed without evaluating the large exact rational sum. -/
def seedPlusCheck (S c E a e : ℤ) (seed : SE) : Bool :=
  match seed.check with
  | none => false
  | some b => decide (0<S ∧ 0≤E ∧ 0≤e ∧
      (((c-a-E+e:ℤ):ℚ)/(S:ℚ))≤b.1 ∧ b.2≤(((c-a+E-e:ℤ):ℚ)/(S:ℚ)))

theorem seedPlusCheck_sound (S c E a e : ℤ) (seed : SE) (q : ℚ)
    (hclose : |q-(a:ℚ)/(S:ℚ)|≤(e:ℚ)/(S:ℚ))
    (hc : seedPlusCheck S c E a e seed=true) :
    (match (seAdd seed (seRat q)).check with
      | none=>false | some b=>coeffEnclosed S c E b)=true := by
  unfold seedPlusCheck at hc
  cases hb : seed.check with
  | none => simp only [hb,Bool.false_eq_true] at hc
  | some b =>
    rw [hb] at hc
    have hh : 0<S ∧ 0≤E ∧ 0≤e ∧
        (((c-a-E+e:ℤ):ℚ)/(S:ℚ))≤b.1 ∧ b.2≤(((c-a+E-e:ℤ):ℚ)/(S:ℚ)) := of_decide_eq_true hc
    have he : (seAdd seed (seRat q)).check=some (boxAdd b (q,q)) := by
      simp [seAdd,seRat,ScalarExpr.check,hb]
    rw [he]
    change coeffEnclosed S c E (boxAdd b (q,q))=true
    apply decide_eq_true
    change 0≤E ∧ _ ∧ _
    refine ⟨hh.2.1,?_,?_⟩
    all_goals
      have hl := hh.2.2.2.1
      have hu := hh.2.2.2.2
      have hq := abs_le.mp hclose
      dsimp only [boxAdd] at *
      push_cast at hl hu ⊢
      simp only [add_div,sub_div] at hl hu ⊢
      linarith [hq.1,hq.2]

#print axioms seedPlusCheck_sound

end CatalanCore.Li2.DecayCert.LatticeGate
