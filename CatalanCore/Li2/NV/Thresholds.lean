module
public import CatalanCore.Li2.NV.Classes
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.NormCast

@[expose] public section
namespace CatalanCore.Li2.NV
noncomputable section

private def classLevel : ClassType→ℤ
  | .C => 0
  | .A | .D => 1
  | .B | .zero => 2

private theorem level_bounds (c : ClassType) : 0≤classLevel c ∧ classLevel c≤2 := by
  cases c <;> norm_num [classLevel]

private theorem level_zero (c : ClassType) : classLevel c=0 ↔ c=.C := by
  cases c <;> norm_num [classLevel]

private theorem level_two (c : ClassType) : classLevel c=2 ↔ c=.B ∨ c=.zero := by
  cases c <;> norm_num [classLevel]

private theorem class_zero_iff (n ℓ s : ℕ) : classType n ℓ s=.zero ↔ s=0 := by
  unfold classType
  split_ifs <;> simp_all

private theorem class_C_ne_zero (n ℓ s : ℕ) (h : classType n ℓ s=.C) : s≠0 := by
  intro hs
  simp [classType,hs] at h

private theorem C_no_B (n ℓ s t : ℕ) (hs : classType n ℓ s=.C) : classType n ℓ t≠.B := by
  intro ht
  unfold classType at hs ht
  split_ifs at hs ht <;> simp_all <;> omega

private theorem level_high_only_zero (n ℓ : ℕ) (s x : Fin ℓ)
    (hs : classLevel (classType n ℓ s)=0) : classLevel (classType n ℓ x)=2 ↔ x.val=0 := by
  rw [level_two]
  constructor
  · rintro (hb | hz)
    · exact False.elim (C_no_B n ℓ s x ((level_zero _).mp hs) hb)
    · exact (class_zero_iff n ℓ x).mp hz
  · intro hx
    exact Or.inr ((class_zero_iff n ℓ x).mpr hx)

private theorem level_at_zero (n ℓ : ℕ) (x : Fin ℓ) (hx : x.val=0) :
    classLevel (classType n ℓ x)=2 := by simp [classType,hx,classLevel]

private theorem potential_level (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) (s : Fin ℓ) :
    nu n ℓ s+2*(m n ℓ s:ℤ)=
      3*((n/ℓ:ℕ):ℤ)+(k n ℓ:ℤ)-2+classLevel (classType n ℓ s) := by
  have hp := ((class_table n ℓ hR).1 s).2.1
  have hQ : (nu n ℓ s:ℚ)+2*(m n ℓ s:ℚ)=
      3*((n/ℓ:ℕ):ℚ)+(k n ℓ:ℚ)-2+(classLevel (classType n ℓ s):ℚ) := by
    cases hc : classType n ℓ s <;>
      simp only [hc,typePot] at hp ⊢ <;>
      dsimp only [pot,classLevel] at hp ⊢ <;> norm_num at hp ⊢ <;> linarith
  exact_mod_cast hQ

private def gap (n ℓ : ℕ) (P : Ix n ℓ) : ℤ := (m n ℓ P.1:ℤ)-(P.2.val:ℤ)-1

private theorem gap_nonneg (n ℓ : ℕ) (P : Ix n ℓ) : 0≤gap n ℓ P := by
  have hp := P.2.isLt
  dsimp [gap]
  omega

private theorem gap_zero (n ℓ : ℕ) (P : Ix n ℓ) : gap n ℓ P=0 ↔ P.2.val+1=m n ℓ P.1 := by
  dsimp [gap]
  omega

private def twiceSlack (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ) : ℤ :=
  2*nu n ℓ s+2*(d n ℓ s P:ℤ)+2*(d n ℓ s Q:ℤ)-
    2*(P.2.val:ℤ)-2*(Q.2.val:ℤ)-nu n ℓ P.1-nu n ℓ Q.1

/-- Potential levels differ by at most one; equality occurs only at the
class-C/zero top-index couplings identified in the paper. -/
theorem threshold (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s : Fin ℓ) (P Q : Ix n ℓ) :
    0≤slack n ℓ s P Q ∧
    (slack n ℓ s P Q=0 ↔ (s=P.1 ∧ s=Q.1) ∨ ExceptionalSlack n ℓ s P Q) ∧
    (0<slack n ℓ s P Q →
      if nu n ℓ P.1%2=nu n ℓ Q.1%2 then 1≤slack n ℓ s P Q
      else (1:ℚ)/2≤slack n ℓ s P Q) := by
  let S := twiceSlack n ℓ s P Q
  have hS : (S:ℚ)=2*slack n ℓ s P Q := by
    dsimp only [S,twiceSlack,slack,pi]
    push_cast
    ring
  have hgp := gap_nonneg n ℓ P
  have hgq := gap_nonneg n ℓ Q
  have hls := level_bounds (classType n ℓ s)
  have hlp := level_bounds (classType n ℓ P.1)
  have hlq := level_bounds (classType n ℓ Q.1)
  have hf : S=
      if s=P.1 then (if s=Q.1 then 0 else
        2*gap n ℓ Q+2+classLevel (classType n ℓ s)-classLevel (classType n ℓ Q.1))
      else if s=Q.1 then 2*gap n ℓ P+2+classLevel (classType n ℓ s)-classLevel (classType n ℓ P.1)
      else 2*gap n ℓ P+2*gap n ℓ Q+4+2*classLevel (classType n ℓ s)-
        classLevel (classType n ℓ P.1)-classLevel (classType n ℓ Q.1) := by
    have hs := potential_level n ℓ hR s
    have hp := potential_level n ℓ hR P.1
    have hq := potential_level n ℓ hR Q.1
    by_cases hP : s=P.1
    · by_cases hQ : s=Q.1
      · dsimp only [S,twiceSlack,gap]
        simp only [d, ite_eq_left hP, ite_eq_left hQ]
        simp only [← hP, ← hQ]
        ring
      · dsimp only [S,twiceSlack,gap]
        simp only [d, ite_eq_left hP, ite_eq_right hQ]
        simp only [← hP] at hp ⊢
        omega
    · by_cases hQ : s=Q.1
      · dsimp only [S,twiceSlack,gap]
        simp only [d, ite_eq_right hP, ite_eq_left hQ]
        simp only [← hQ] at hq ⊢
        omega
      · dsimp only [S,twiceSlack,gap]
        simp only [d, ite_eq_right hP, ite_eq_right hQ]
        omega
  have hnonneg : 0≤S := by rw [hf];split_ifs <;> omega
  have hz : S=0 ↔ (s=P.1 ∧ s=Q.1) ∨ ExceptionalSlack n ℓ s P Q := by
    constructor
    · intro he
      by_cases hP : s=P.1
      · by_cases hQ : s=Q.1
        · exact Or.inl ⟨hP,hQ⟩
        · have hform := hf
          simp only [ite_eq_left hP, ite_eq_right hQ] at hform
          have hs0 : classLevel (classType n ℓ s)=0 := by omega
          have hq2 : classLevel (classType n ℓ Q.1)=2 := by omega
          have hg0 : gap n ℓ Q=0 := by omega
          have hq0 := (level_high_only_zero n ℓ s Q.1 hs0).mp hq2
          have htop : Q.2.val+1=m n ℓ 0 := by simpa [hq0] using (gap_zero n ℓ Q).mp hg0
          exact Or.inr (Or.inl ⟨hP,(by intro h;exact hQ (hP.trans h)),(level_zero _).mp hs0,hq0,htop⟩)
      · by_cases hQ : s=Q.1
        · have hform := hf
          simp only [ite_eq_right hP, ite_eq_left hQ] at hform
          have hs0 : classLevel (classType n ℓ s)=0 := by omega
          have hp2 : classLevel (classType n ℓ P.1)=2 := by omega
          have hg0 : gap n ℓ P=0 := by omega
          have hp0 := (level_high_only_zero n ℓ s P.1 hs0).mp hp2
          have htop : P.2.val+1=m n ℓ 0 := by simpa [hp0] using (gap_zero n ℓ P).mp hg0
          exact Or.inr (Or.inr (Or.inl ⟨hQ,(by intro h;exact hP (hQ.trans h.symm)),(level_zero _).mp hs0,hp0,htop⟩))
        · have hform := hf
          simp only [ite_eq_right hP, ite_eq_right hQ] at hform
          have hs0 : classLevel (classType n ℓ s)=0 := by omega
          have hp2 : classLevel (classType n ℓ P.1)=2 := by omega
          have hq2 : classLevel (classType n ℓ Q.1)=2 := by omega
          have hgp0 : gap n ℓ P=0 := by omega
          have hgq0 : gap n ℓ Q=0 := by omega
          have hp0 := (level_high_only_zero n ℓ s P.1 hs0).mp hp2
          have hq0 := (level_high_only_zero n ℓ s Q.1 hs0).mp hq2
          have htp : P.2.val+1=m n ℓ 0 := by simpa [hp0] using (gap_zero n ℓ P).mp hgp0
          have htq : Q.2.val+1=m n ℓ 0 := by simpa [hq0] using (gap_zero n ℓ Q).mp hgq0
          exact Or.inr (Or.inr (Or.inr ⟨(level_zero _).mp hs0,hp0,hq0,htp,htq⟩))
    · rintro (h | h)
      · have hform := hf
        simp only [ite_eq_left h.1, ite_eq_left h.2] at hform
        exact hform
      · rcases h with h | h | h
        · rcases h with ⟨hP,hne,hC,hq0,htq⟩
          have hQ : s≠Q.1 := by intro h;exact hne (hP.symm.trans h)
          have hs0 := (level_zero _).mpr hC
          have hq2 := level_at_zero n ℓ Q.1 hq0
          have hg0 : gap n ℓ Q=0 := (gap_zero n ℓ Q).mpr (by simpa [hq0] using htq)
          simp only [ite_eq_left hP, ite_eq_right hQ] at hf
          omega
        · rcases h with ⟨hQ,hne,hC,hp0,htp⟩
          have hP : s≠P.1 := by intro h;exact hne (h.symm.trans hQ)
          have hs0 := (level_zero _).mpr hC
          have hp2 := level_at_zero n ℓ P.1 hp0
          have hg0 : gap n ℓ P=0 := (gap_zero n ℓ P).mpr (by simpa [hp0] using htp)
          simp only [ite_eq_right hP, ite_eq_left hQ] at hf
          omega
        · rcases h with ⟨hC,hp0,hq0,htp,htq⟩
          have hP : s≠P.1 := by intro h;exact class_C_ne_zero n ℓ s hC (by simpa only [h] using hp0)
          have hQ : s≠Q.1 := by intro h;exact class_C_ne_zero n ℓ s hC (by simpa only [h] using hq0)
          have hs0 := (level_zero _).mpr hC
          have hp2 := level_at_zero n ℓ P.1 hp0
          have hq2 := level_at_zero n ℓ Q.1 hq0
          have hgp0 : gap n ℓ P=0 := (gap_zero n ℓ P).mpr (by simpa [hp0] using htp)
          have hgq0 : gap n ℓ Q=0 := (gap_zero n ℓ Q).mpr (by simpa [hq0] using htq)
          simp only [ite_eq_right hP, ite_eq_right hQ] at hf
          omega
  refine ⟨?_,?_,?_⟩
  · have hh : (0:ℚ)≤S := by exact_mod_cast hnonneg
    linarith
  · constructor
    · intro h
      have he : S=0 := by exact_mod_cast (show (S:ℚ)=0 by linarith)
      exact hz.mp he
    · intro h
      have he : (S:ℚ)=0 := by exact_mod_cast hz.mpr h
      linarith
  · intro hpos
    have hp : 0<S := by exact_mod_cast (show (0:ℚ)<S by linarith)
    split_ifs with heven
    · have hm : S%2=0 := by dsimp only [S,twiceSlack];omega
      have htwo : 2≤S := by omega
      have hh : (2:ℚ)≤S := by exact_mod_cast htwo
      linarith
    · have hone : 1≤S := by omega
      have hh : (1:ℚ)≤S := by exact_mod_cast hone
      linarith

#print axioms threshold
end
end CatalanCore.Li2.NV
