module
public import CatalanCore.Li2.NV.Definitions
public import Mathlib.Data.Int.CardIntervalMod
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.NormCast
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.IntervalCases

@[expose] public section
open scoped BigOperators
namespace CatalanCore.Li2.NV
noncomputable section

def neededAtValid (q k : ℕ) : Finset NVMod.TypeKey :=
  if k < 4 ∧ (1 ≤ q ∨ k = 3) then NVMod.neededAt q k else ∅

theorem neededAtValid_eq (q k : ℕ) (h : k < 4 ∧ (1 ≤ q ∨ k = 3)) :
    neededAtValid q k = NVMod.neededAt q k := by simp [neededAtValid,h]

private theorem countClass_formula (N ℓ s : ℕ) (hp : 0 < ℓ) (hs : s < ℓ) :
    countClass N ℓ s = N/ℓ + if s ≠ 0 ∧ s ≤ N%ℓ then 1 else 0 := by
  have hset : ((Finset.range (N+1)).filter (fun i => i%ℓ=s)) =
      if s=0 then insert 0 ((Finset.Icc 1 N).filter (fun i => i%ℓ=s))
      else ((Finset.Icc 1 N).filter (fun i => i%ℓ=s)) := by
    by_cases hz : s=0
    · simp only [hz,ite_true]
      ext i
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
      constructor
      · intro h
        by_cases hi : i=0
        · exact Or.inl hi
        · exact Or.inr ⟨⟨by omega,by omega⟩,h.2⟩
      · rintro (hi | ⟨⟨hi,hN⟩,hm⟩)
        · subst i;exact ⟨by omega,rfl⟩
        · exact ⟨by omega,hm⟩
    · simp only [hz,ite_false]
      ext i
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
      constructor
      · rintro ⟨hi,hm⟩
        have hi0 : i≠0 := by intro h;subst i;exact hz hm.symm
        exact ⟨⟨by omega,by omega⟩,hm⟩
      · rintro ⟨⟨hi,hN⟩,hm⟩;exact ⟨by omega,hm⟩
  have hc := Nat.count_modEq_card (N+1) hp s
  simp only [Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt hs] at hc
  rw [hset] at hc
  have h0 : 0 ∉ (Finset.Icc 1 N).filter (fun i => i%ℓ=s) := by simp
  have hm := Nat.mod_lt N hp
  have hnext : (N+1)%ℓ = (N%ℓ+1)%ℓ := by exact (Nat.mod_add_mod N ℓ 1).symm
  by_cases hw : N%ℓ+1=ℓ
  · have hn : (N+1)%ℓ=0 := by rw [hnext,hw,Nat.mod_self]
    have hd := Nat.succ_div_of_mod_eq_zero hn
    rw [hn,hd] at hc
    by_cases hz : s=0
    · simp only [hz, if_pos, Finset.card_insert_of_notMem h0] at hc
      simp only [hz, ne_eq, not_true_eq_false, false_and, if_false, add_zero]
      simpa [countClass] using hc
    · simp only [hz, if_false, not_lt_zero, add_zero] at hc
      have hsN : s ≤ N%ℓ := by omega
      simpa [countClass,hz,hsN] using hc
  · have hlt : N%ℓ+1<ℓ := by omega
    have hn : (N+1)%ℓ=N%ℓ+1 := by rw [hnext,Nat.mod_eq_of_lt hlt]
    have hn0 : (N+1)%ℓ≠0 := by omega
    have hd := Nat.succ_div_of_mod_ne_zero hn0
    rw [hn,hd] at hc
    by_cases hz : s=0
    · simp only [hz, if_pos, Finset.card_insert_of_notMem h0] at hc
      simp only [hz, ne_eq, not_true_eq_false, false_and, if_false, add_zero]
      simp only [Nat.zero_lt_succ, if_true] at hc
      simpa [countClass] using hc
    · simp only [hz, if_false] at hc
      have he : s < N%ℓ+1 ↔ s ≤ N%ℓ := by omega
      simpa [countClass,hz,he] using hc

private theorem sum_countClass (N ℓ : ℕ) (hp : 0 < ℓ) :
    (∑ s : Fin ℓ, countClass N ℓ s) = N := by
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.Icc 1 N)
    (t := (Finset.univ : Finset (Fin ℓ)))
    (f := fun i : ℕ => (⟨i%ℓ,Nat.mod_lt i hp⟩ : Fin ℓ)) (by simp)
  calc
    (∑ s : Fin ℓ, countClass N ℓ s) =
        ∑ s ∈ (Finset.univ : Finset (Fin ℓ)),
          ((Finset.Icc 1 N).filter (fun i => (⟨i%ℓ,Nat.mod_lt i hp⟩ : Fin ℓ)=s)).card := by
      apply Finset.sum_congr rfl
      intro s _
      unfold countClass
      congr 1
      all_goals ext i; simp only [Finset.mem_filter, Fin.ext_iff]
    _ = (Finset.Icc 1 N).card := h.symm
    _ = N := by simp

private theorem quotient4 (n ℓ : ℕ) (hp : 0 < ℓ) :
    4*n/ℓ = 4*(n/ℓ)+k n ℓ := by
  have hn := Nat.div_add_mod n ℓ
  calc
    4*n/ℓ = (4*(n/ℓ)*ℓ+4*(n%ℓ))/ℓ := by
      congr 1
      calc
        4*n=4*(ℓ*(n/ℓ)+n%ℓ) := congrArg (fun x => 4*x) hn.symm
        _ = _ := by ring
    _ = 4*(n/ℓ)+(4*(n%ℓ))/ℓ := by rw [Nat.mul_comm (4*(n/ℓ)) ℓ, Nat.mul_add_div hp]
    _ = _ := rfl

private theorem remainder4 (n ℓ : ℕ) : 4*n%ℓ=r' n ℓ := by
  simp only [r', Nat.mul_mod, Nat.mod_mod]

theorem class_counts (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) :
    (∀ s : Fin ℓ, 2*a n ℓ s ≤ c n ℓ s ∧ c n ℓ s ≤ ℓ-1) ∧
    (∑ s : Fin ℓ, m n ℓ s)=2*n ∧
    (∀ s : Fin ℓ, (a n ℓ s,c n ℓ s)=typeAC n ℓ s) := by
  have hp : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have ha (s : Fin ℓ) := countClass_formula n ℓ s hp s.isLt
  have hc (s : Fin ℓ) := countClass_formula (4*n) ℓ s hp s.isLt
  have h4 := quotient4 n ℓ hp
  have hr4 := remainder4 n ℓ
  have hk : 1 ≤ n/ℓ ∨ k n ℓ=3 := by
    rcases hR.2 with h | ⟨hsmall,hlarge⟩
    · left; exact Nat.one_le_div_iff hp |>.2 h
    · right
      have hn : n%ℓ=n := Nat.mod_eq_of_lt hsmall
      dsimp [k];rw [hn]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hupper : 4*n/ℓ < ℓ-1 := (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hR.1)
  have hbound (s : Fin ℓ) : 2*a n ℓ s ≤ c n ℓ s ∧ c n ℓ s ≤ ℓ-1 := by
    unfold a c
    rw [ha s,hc s,h4]
    have hu : 4*(n/ℓ)+k n ℓ < ℓ-1 := by omega
    split_ifs <;> omega
  refine ⟨hbound,?_,?_⟩
  · unfold m
    rw [Finset.sum_tsub_distrib Finset.univ (fun s _ => (hbound s).1)]
    simp only [a,c,← Finset.mul_sum, sum_countClass n ℓ hp, sum_countClass (4*n) ℓ hp]
    omega
  · intro s
    simp only [a,c,ha s,hc s,typeAC,r,h4,hr4]
    rfl

theorem class_table (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) :
    (∀ s : Fin ℓ, (m n ℓ s:ℤ)=typeM (n/ℓ) (k n ℓ) (classType n ℓ s) ∧
      pot n ℓ s=typePot (n/ℓ) (k n ℓ) (classType n ℓ s) ∧
      nu n ℓ s % 2 =
        ((n/ℓ:ℤ)+(k n ℓ:ℤ)+if parityGroup (classType n ℓ s) then 0 else 1)%2) ∧
    (Bset n ℓ=∅ ∨ Cset n ℓ=∅) ∧ (tied n ℓ ↔ (Cset n ℓ).Nonempty) := by
  have hcounts := class_counts n ℓ hR
  refine ⟨?_,?_,?_⟩
  · intro s
    have ha := congrArg Prod.fst (hcounts.2.2 s)
    have hc := congrArg Prod.snd (hcounts.2.2 s)
    change a n ℓ s = _ at ha
    change c n ℓ s = _ at hc
    have hmZ : (m n ℓ s:ℤ)=(c n ℓ s:ℤ)-2*(a n ℓ s:ℤ) := by
      dsimp [m];rw [Nat.cast_sub (hcounts.1 s).1];push_cast;ring
    have hmQ : (m n ℓ s:ℚ)=(c n ℓ s:ℚ)-2*(a n ℓ s:ℚ) := by
      dsimp [m];rw [Nat.cast_sub (hcounts.1 s).1];push_cast;ring
    by_cases hz : (s:ℕ)=0 <;> by_cases hr : (s:ℕ)≤r n ℓ <;>
      by_cases hrp : (s:ℕ)≤r' n ℓ
    all_goals try simp only [hz] at hmZ hmQ
    all_goals simp [typeAC,hz,hr,hrp] at ha hc
    all_goals simp [hmZ,pot,hmQ,nu,classType,hz,hr,hrp,typeM,typePot,parityGroup]
    all_goals simp only [ha,hc]
    all_goals push_cast
    all_goals simp only [← Int.natCast_ediv]
    all_goals refine ⟨by omega, ?_, by omega⟩
    all_goals ring
  · by_cases h : r n ℓ ≤ r' n ℓ
    · right;exact Finset.Ioc_eq_empty (by omega)
    · left;exact Finset.Ioc_eq_empty (by omega)
  · simp [tied,Cset,Finset.nonempty_Ioc]

theorem consecutive_tied (n ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 13≤ℓ)
    (ht : tied n ℓ) (ht1 : tied (n+1) ℓ) :
    (n+1)/ℓ=n/ℓ ∧ k (n+1) ℓ=k n ℓ ∧
      r (n+1) ℓ=r n ℓ+1 ∧ r' (n+1) ℓ=r' n ℓ+4 := by
  have hp : 0<ℓ := by omega
  have hn0 : (n+1)%ℓ≠0 := by
    intro hz
    have hh := ht1
    simp [tied,r,r',hz] at hh
  have hq := Nat.succ_div_of_mod_ne_zero hn0
  have hr : r (n+1) ℓ=r n ℓ+1 := by
    have h := Nat.mod_add_div n ℓ
    have h1 := Nat.mod_add_div (n+1) ℓ
    rw [hq] at h1
    dsimp [r];omega
  have hrb : r n ℓ<ℓ := Nat.mod_lt n hp
  have hrb1 : r (n+1) ℓ<ℓ := Nat.mod_lt (n+1) hp
  have hkb : k n ℓ<4 := (Nat.div_lt_iff_lt_mul hp).2 (by dsimp [r] at hrb;omega)
  have hkb1 : k (n+1) ℓ<4 := (Nat.div_lt_iff_lt_mul hp).2 (by dsimp [r] at hrb1;omega)
  have h0 : r' n ℓ + ℓ*k n ℓ = 4*r n ℓ := Nat.mod_add_div (4*(n%ℓ)) ℓ
  have h1 : r' (n+1) ℓ + ℓ*k (n+1) ℓ = 4*r (n+1) ℓ := Nat.mod_add_div (4*((n+1)%ℓ)) ℓ
  change r' n ℓ<r n ℓ at ht
  change r' (n+1) ℓ<r (n+1) ℓ at ht1
  refine ⟨hq,?_,hr,?_⟩
  all_goals interval_cases hk : k n ℓ <;> interval_cases hk1 : k (n+1) ℓ <;>
    simp only [hk,hk1,Nat.mul_zero,Nat.mul_one] at * <;> omega

end
end CatalanCore.Li2.NV


