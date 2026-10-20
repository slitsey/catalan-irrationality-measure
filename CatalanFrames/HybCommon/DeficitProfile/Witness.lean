module
public import CatalanFrames.HybCommon.DeficitProfile
public import CatalanCore.Arith.Hybrid.AffineWitness
@[expose] public section
open CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon

lemma row_lowWitness {P : DeficitRow} (hP : P.cert) (hk : P.kind=0)
    {u : ℝ} (hu0 : (P.lo : ℝ)≤u) (hu1 : u≤(P.hi : ℝ)) :
    (P.a : ℝ)+(P.b : ℝ)*u≤lowWitness ((P.A4 : ℝ)/4) ((P.B4 : ℝ)/4) u := by
  have hh := hP.2.2.2.2
  simp only [hk, if_pos] at hh
  have hs := hh.2.2.2
  have hlen (q : ℚ) (hq : q∈[P.lo,P.hi]) :
      ∀aa∈[1,(P.A4 : ℝ)/4*(q : ℝ)],∀bb∈[5/4,(P.B4 : ℝ)/4*(q : ℝ),1+(q : ℝ)],
        (P.a : ℝ)+(P.b : ℝ)*(q : ℝ)≤1/8-(q : ℝ)+bb-aa := by
    have hq' : ∀aa∈[1,(P.A4 : ℚ)*q/4],∀bb∈[5/4,(P.B4 : ℚ)*q/4,1+q],
        P.a+P.b*q≤1/8-q+bb-aa := fun aa ha bb hb => (hs q hq).1 aa ha bb hb |>.2
    simp [List.mem_cons] at hq' ⊢
    simp only [div_mul_eq_mul_div]
    rcases hq' with ⟨⟨h00,h01,h02⟩,h10,h11,h12⟩
    refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
    · have hR := (Rat.cast_le (K := ℝ)).2 h00
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h01
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h02
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h10
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h11
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h12
      push_cast at hR
      exact hR
  have hedge (q : ℚ) (hq : q∈[P.lo,P.hi]) :
      ∀bb∈[5/4,(P.B4 : ℝ)/4*(q : ℝ),1+(q : ℝ)],
        (P.a : ℝ)+(P.b : ℝ)*(q : ℝ)≤bb-9/8 := by
    have hq' : ∀bb∈[5/4,(P.B4 : ℚ)*q/4,1+q],P.a+P.b*q≤bb-9/8 := (hs q hq).2
    simp [List.mem_cons] at hq' ⊢
    simp only [div_mul_eq_mul_div]
    rcases hq' with ⟨h0,h1,h2⟩
    refine ⟨?_,?_,?_⟩
    · have hR := (Rat.cast_le (K := ℝ)).2 h0
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h1
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h2
      push_cast at hR
      exact hR
  exact lowWitness_bound hu0 hu1 (hlen _ (by simp)) (hlen _ (by simp))
    (hedge _ (by simp)) (hedge _ (by simp))

lemma row_ncWitness {P : DeficitRow} (hP : P.cert) (hk : P.kind≠0)
    {u : ℝ} (hu0 : (P.lo : ℝ)≤u) (hu1 : u≤(P.hi : ℝ)) :
    (P.a : ℝ)+(P.b : ℝ)*u≤ncWitness ((P.A4 : ℝ)/4) ((P.B4 : ℝ)/4) u := by
  have hh := hP.2.2.2.2
  simp only [hk, if_false] at hh
  have hs := hh.2.2.2.2.2.2
  have hlen (q : ℚ) (hq : q∈[P.lo,P.hi]) :
      ∀aa∈[1,(P.A4 : ℝ)/4*(q : ℝ)],∀bb∈[5/4,(P.B4 : ℝ)/4*(q : ℝ)],
        (P.a : ℝ)+(P.b : ℝ)*(q : ℝ)≤bb-aa-1/8 := by
    have hq' : ∀aa∈[1,(P.A4 : ℚ)*q/4],∀bb∈[5/4,(P.B4 : ℚ)*q/4],
        P.a+P.b*q≤bb-aa-1/8 := (hs q hq).2.2
    simp [List.mem_cons] at hq' ⊢
    simp only [div_mul_eq_mul_div]
    rcases hq' with ⟨⟨h00,h01⟩,h10,h11⟩
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · have hR := (Rat.cast_le (K := ℝ)).2 h00
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h01
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h10
      push_cast at hR
      exact hR
    · have hR := (Rat.cast_le (K := ℝ)).2 h11
      push_cast at hR
      exact hR
  exact ncWitness_bound hu0 hu1 (hlen _ (by simp)) (hlen _ (by simp))
end CatalanFrames.HybCommon
