module

public import CatalanCore.Arith.Hybrid.ChainClasses

@[expose] public section

/-! # Consecutive pole intervals

A pole is either an ordinary multiple of `p`, or a solution of `4t=jp+o`.
The small dictionary consists only of consecutive numerator indices `j`;
it does not enumerate core-chain matrix types.
-/

open Finset

namespace CatalanCore.Arith.Hybrid.ChainClasses

def poleOffset (o j : ℕ) : ℕ := if j%4=0 then 0 else o
def poleCut (p o j : ℕ) : ℕ := (j*p+poleOffset o j)/4

def PolePair (c A B : ℕ) : Prop :=
  A<B ∧ (A%4=0 ∨ A%4=c) ∧ (B%4=0 ∨ B%4=c) ∧
    ∀j∈Finset.Ioo A B, j%4≠0 ∧ j%4≠c

theorem poleCut_exact {p o c j : ℕ} (ho : o=1 ∨ o=3) (hc : c=1 ∨ c=3)
    (hp : p%4=if c=1 then 4-o else o) (hj : j%4=0 ∨ j%4=c) :
    4*poleCut p o j = j*p+poleOffset o j := by
  have hm : (j*p+poleOffset o j)%4=0 := by
    rcases ho with rfl | rfl <;> rcases hc with rfl | rfl <;>
      rcases hj with hj | hj <;>
      simp_all [poleOffset, Nat.add_mod, Nat.mul_mod]
  unfold poleCut
  omega

theorem singular_numerator_class {p o c j t : ℕ} (ho : o=1 ∨ o=3)
    (hc : c=1 ∨ c=3) (hp : p%4=if c=1 then 4-o else o)
    (he : 4*t=j*p+o) : j%4=c := by
  have hm := congrArg (fun n : ℕ => n%4) he
  rcases ho with rfl | rfl <;> rcases hc with rfl | rfl
  all_goals norm_num at hp
  all_goals rw [Nat.add_mod, Nat.mul_mod j p 4, hp] at hm
  all_goals norm_num at hm
  all_goals omega

theorem no_singular_between {p o c A B t : ℕ} (ho : o=1 ∨ o=3)
    (hc : c=1 ∨ c=3) (hp5 : 5≤p) (hp : p%4=if c=1 then 4-o else o)
    (hpair : PolePair c A B) (hat : poleCut p o A<t) (htb : t<poleCut p o B) :
    ¬(p∣t ∨ p∣4*t-o) := by
  have hA := poleCut_exact ho hc hp hpair.2.1
  have hB := poleCut_exact ho hc hp hpair.2.2.1
  have ho3 : o≤3 := by rcases ho with rfl | rfl <;> omega
  have heA : poleOffset o A≤3 := by unfold poleOffset; split_ifs <;> omega
  have heB : poleOffset o B≤3 := by unfold poleOffset; split_ifs <;> omega
  intro hs
  have hj : ∃j, 4*t=j*p+poleOffset o j ∧ (j%4=0 ∨ j%4=c) := by
    rcases hs with ⟨k,hk⟩ | ⟨j,hj⟩
    · refine ⟨4*k, ?_, Or.inl (by omega)⟩
      simp only [poleOffset, show (4*k)%4=0 by omega, if_pos, add_zero]
      nlinarith
    · have ht0 : 0<t := by omega
      have he : 4*t=j*p+o := by
        have hsub := Nat.sub_add_cancel (show o≤4*t by omega)
        nlinarith
      have hclass := singular_numerator_class ho hc hp he
      have hj0 : j%4≠0 := by rcases hc with rfl | rfl <;> omega
      exact ⟨j, by simpa [poleOffset, hj0] using he, Or.inr hclass⟩
  obtain ⟨j, he, hjc⟩ := hj
  have hej : poleOffset o j≤3 := by unfold poleOffset; split_ifs <;> omega
  have haj : A<j := by
    by_contra hn
    have hle : j*p≤A*p := Nat.mul_le_mul_right p (by omega)
    by_cases hEq : j=A
    · subst j; omega
    · have hle' : (j+1)*p≤A*p := Nat.mul_le_mul_right p (by omega)
      nlinarith
  have hjb : j<B := by
    by_contra hn
    have hle : B*p≤j*p := Nat.mul_le_mul_right p (by omega)
    by_cases hEq : j=B
    · subst j; omega
    · have hle' : (B+1)*p≤j*p := Nat.mul_le_mul_right p (by omega)
      nlinarith
  have hh := hpair.2.2.2 j (Finset.mem_Ioo.mpr ⟨haj,hjb⟩)
  exact hjc.elim hh.1 hh.2

/-- Any pair inside the clipped pole interval is in one generalized chain cell.
The clipping at `r+p` removes every core-exit cut in one step. -/
theorem pole_pair_noCut {p o c A B r z y : ℕ} (ho : o=1 ∨ o=3)
    (hc : c=1 ∨ c=3) (hp5 : 5≤p) (hp : p%4=if c=1 then 4-o else o)
    (hpair : PolePair c A B) (hAz : poleCut p o A≤z) (hyB : y<poleCut p o B)
    (hrz : r≤z) (hyp : y<r+p) :
    NoCut (Cut p r (Singular p o)) z y := by
  intro t hzt hty hcut
  have ht0 : 0≤t := by omega
  let n := t.toNat
  have hn : (n : ℤ)=t := Int.toNat_of_nonneg ht0
  have hzn : z<n := by exact_mod_cast (show (z : ℤ)<(n : ℤ) by omega)
  have hny : n≤y := by exact_mod_cast (show (n : ℤ)≤(y : ℤ) by omega)
  have hns := no_singular_between ho hc hp5 hp hpair (hAz.trans_lt hzn) (hny.trans_lt hyB)
  have hnsInt : ¬ Singular (p : ℤ) o t := by
    intro hs
    apply hns
    rcases hs with hd | hd
    · left
      have he : (p : ℤ)∣(n : ℤ) := by simpa only [hn] using hd
      exact_mod_cast he
    · right
      have ho3 : o≤3 := by rcases ho with rfl | rfl <;> omega
      have hcst : ((4*n-o : ℕ) : ℤ)=4*(n : ℤ)-o := by
        rw [Nat.cast_sub (by omega : o≤4*n)]; push_cast; ring
      have he : (p : ℤ)∣((4*n-o : ℕ) : ℤ) := by rw [hcst,hn]; exact hd
      exact_mod_cast he
  rcases hcut with hs | ⟨j,hj⟩ | ⟨j,hj⟩
  · exact hnsInt hs
  · exact hnsInt (Or.inl ⟨j,by nlinarith⟩)
  · have hd : (p : ℤ)∣t-r := ⟨j,by nlinarith⟩
    have hle := Int.le_of_dvd (show (0 : ℤ)<t-r by omega) hd
    omega

end CatalanCore.Arith.Hybrid.ChainClasses
