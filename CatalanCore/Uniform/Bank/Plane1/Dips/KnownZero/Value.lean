module

public import CatalanCore.Uniform.Bank.Plane1.Dips.KnownZero.Core

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! Exact clipped interval price for every r,m,p and ordered pole cuts.
No alternating geometry slope, N<=2p, even r, or upper bound on kw is used. -/
namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Uniform
open CatalanFrames.P6Hybrid (isRowP isColP sum_ind_core sum_ind_ext sum_pair)
open Classical

def knownIntervals (r m p k0 kw : ℕ) (win : Bool) : Finset ℕ :=
  Ico 0 k0 ∪ (if win then Ico (max r kw) (min p (r+2*m)) else ∅)

def zSaving (r m p k0 kw : ℕ) (win : Bool) : ℕ :=
  (min k0 r-(r-p))+(min k0 r-(r+2*m-p))+
  (min k0 (r+2*m)-max (r+2*m-p) r)+
  (if win then min p (r+2*m)-max (max kw (r+2*m-p)) r else 0)

theorem knownIntervals_mem {r m p k0 kw t : ℕ} {win : Bool} (ht : t<r+2*m) :
    t∈knownIntervals r m p k0 kw win ↔
      t<k0 ∨ (win=true ∧ kw≤t ∧ t<p ∧ r≤t) := by
  cases win <;> simp [knownIntervals, max_le_iff, lt_min_iff] <;> omega

theorem knownIntervals_lt_p {r m p k0 kw t : ℕ} {win : Bool}
    (hk0p : k0≤p) (ht : t∈knownIntervals r m p k0 kw win) : t<p := by
  unfold knownIntervals at ht
  rcases Finset.mem_union.1 ht with h | h
  · have := (Finset.mem_Ico.1 h).2
    omega
  · cases win
    · simp at h
    · have := (Finset.mem_Ico.1 h).2
      omega

theorem zinterval_core_pt {r m p k0 kw c : ℕ} {win : Bool}
    (hc : c<r) (hpodd : p%2=1) :
    (znU r m p (knownIntervals r m p k0 kw win) c : ℚ)+
      (znV r m p (knownIntervals r m p k0 kw win) c : ℚ) =
      2-(if r-p≤c ∧ c<k0 then 1 else 0)-
        (if r+2*m-p≤c ∧ c<k0 then 1 else 0) := by
  have hk : c∈knownIntervals r m p k0 kw win ↔ c<k0 := by
    rw [knownIntervals_mem (by omega : c<r+2*m)]
    constructor
    · rintro (h | h)
      · exact h
      · omega
    · exact Or.inl
  simp only [znU,znV,hk]
  unfold isColP isRowP
  split_ifs <;> first | (norm_num;done) | (exfalso;omega)

theorem zinterval_core_sum {r m p k0 kw : ℕ} {win : Bool} (hpodd : p%2=1) :
    (∑ c∈range r,((znU r m p (knownIntervals r m p k0 kw win) c : ℚ)+
      (znV r m p (knownIntervals r m p k0 kw win) c : ℚ))) =
      2*(r:ℚ)-((min k0 r-(r-p):ℕ):ℚ)-((min k0 r-(r+2*m-p):ℕ):ℚ) := by
  rw [Finset.sum_congr rfl (fun c hc => zinterval_core_pt (Finset.mem_range.1 hc) hpodd)]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,sum_ind_core,sum_ind_core]
  simp
  ring

def zinterval_hx (r m p k0 kw : ℕ) (win : Bool) (x : ℕ) : ℚ :=
  1-(if r+2*m-p≤x ∧ x<k0 then 1 else 0)-
    (if win=true ∧ max kw (r+2*m-p)≤x ∧ x<p then 1 else 0)

private theorem zinterval_indicator {r m p k0 kw x : ℕ} {win : Bool}
    (hx : x<r+2*m) (hxr : r≤x) (hk0w : k0≤kw) (hk0p : k0≤p)
    (P : Prop) [Decidable P] (hP : P ↔ x+p<r+2*m) :
    (((if x∈knownIntervals r m p k0 kw win then 0 else 1)+
      (if x∈knownIntervals r m p k0 kw win ∧ P then 1 else 0) : ℕ) : ℚ)=
      zinterval_hx r m p k0 kw win x := by
  have hk := knownIntervals_mem (r:=r) (m:=m) (p:=p) (k0:=k0) (kw:=kw) (win:=win) hx
  have hc : x+p<r+2*m ↔ ¬(r+2*m-p≤x) := by omega
  have hvalue : (((if x∈knownIntervals r m p k0 kw win then 0 else 1)+
      (if x∈knownIntervals r m p k0 kw win ∧ P then 1 else 0) : ℕ) : ℚ)=
      if x∈knownIntervals r m p k0 kw win ∧ ¬P then 0 else 1 := by
    by_cases h : x∈knownIntervals r m p k0 kw win <;> by_cases hp : P <;> simp [h,hp]
  rw [hvalue]
  unfold zinterval_hx
  by_cases hlo : r+2*m-p≤x ∧ x<k0
  · have hK : x∈knownIntervals r m p k0 kw win := hk.mpr (Or.inl hlo.2)
    have hp : ¬P := by rw [hP,hc];omega
    have hw : ¬(win=true ∧ max kw (r+2*m-p)≤x ∧ x<p) := by omega
    rw [if_pos ⟨hK,hp⟩,if_pos hlo,if_neg hw]
    norm_num
  · by_cases hw : win=true ∧ max kw (r+2*m-p)≤x ∧ x<p
    · have hK : x∈knownIntervals r m p k0 kw win := hk.mpr (Or.inr ⟨hw.1,by omega,hw.2.2,hxr⟩)
      have hp : ¬P := by rw [hP,hc];omega
      rw [if_pos ⟨hK,hp⟩,if_neg hlo,if_pos hw]
      norm_num
    · have hn : ¬(x∈knownIntervals r m p k0 kw win ∧ ¬P) := by
        rintro ⟨hK,hp⟩
        have hh : ¬(x+p<r+2*m) := fun ht => hp (hP.mpr ht)
        have hNx : r+2*m-p≤x := by omega
        rcases hk.mp hK with hlow | hwin
        · exact hlo ⟨hNx,hlow⟩
        · exact hw ⟨hwin.1,max_le hwin.2.1 hNx,hwin.2.2.1⟩
      rw [if_neg hn,if_neg hlo,if_neg hw]
      norm_num

theorem zinterval_ext_pt_u {r m p k0 kw i : ℕ} {win : Bool}
    (hi : i<m) (hpodd : p%2=1) (hk0w : k0≤kw) (hk0p : k0≤p) :
    (znU r m p (knownIntervals r m p k0 kw win) (r+2*i) : ℚ)=
      zinterval_hx r m p k0 kw win (r+2*i) := by
  have hk := knownIntervals_mem (r:=r) (m:=m) (p:=p) (k0:=k0) (kw:=kw) (win:=win)
    (t:=r+2*i) (by omega)
  have hpar : (r+2*i+p-r)%2=1 := by omega
  have hc : isColP r m (r+2*i+p) ↔ r+2*i+p<r+2*m := by
    simp only [isColP,hpar,and_true]
    omega
  unfold znU
  exact zinterval_indicator (by omega) (by omega) hk0w hk0p _ hc

theorem zinterval_ext_pt_v {r m p k0 kw i : ℕ} {win : Bool}
    (hi : i<m) (hpodd : p%2=1) (hk0w : k0≤kw) (hk0p : k0≤p) :
    (znV r m p (knownIntervals r m p k0 kw win) (r+2*i+1) : ℚ)=
      zinterval_hx r m p k0 kw win (r+2*i+1) := by
  have hk := knownIntervals_mem (r:=r) (m:=m) (p:=p) (k0:=k0) (kw:=kw) (win:=win)
    (t:=r+2*i+1) (by omega)
  have hpar : (r+2*i+1+p-r)%2=0 := by omega
  have hc : isRowP r m (r+2*i+1+p) ↔ r+2*i+1+p<r+2*m := by
    simp only [isRowP,hpar,and_true]
    omega
  unfold znV
  exact zinterval_indicator (by omega) (by omega) hk0w hk0p _ hc

theorem zinterval_ext_sum {r m p k0 kw : ℕ} {win : Bool}
    (hpodd : p%2=1) (hk0w : k0≤kw) (hk0p : k0≤p) :
    (∑ i∈range m,((znU r m p (knownIntervals r m p k0 kw win) (r+2*i) : ℚ)+
      (znV r m p (knownIntervals r m p k0 kw win) (r+2*i+1) : ℚ))) =
      2*(m:ℚ)-((min k0 (r+2*m)-max (r+2*m-p) r:ℕ):ℚ)-
        (if win then ((min p (r+2*m)-max (max kw (r+2*m-p)) r:ℕ):ℚ) else 0) := by
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [zinterval_ext_pt_u (Finset.mem_range.1 hi) hpodd hk0w hk0p,
      zinterval_ext_pt_v (Finset.mem_range.1 hi) hpodd hk0w hk0p])]
  simp_rw [Nat.add_assoc]
  rw [sum_pair (fun j => zinterval_hx r m p k0 kw win (r+j)) m]
  unfold zinterval_hx
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,sum_ind_ext]
  by_cases hw : win=true
  · simp only [hw,true_and,if_true]
    rw [sum_ind_ext]
    simp
  · simp [hw]

theorem zPrice_intervals (r m p k0 kw : ℕ) (win : Bool)
    (hpodd : p%2=1) (hk0w : k0≤kw) (hk0p : k0≤p) :
    ((zPrice r m p (knownIntervals r m p k0 kw win) : ℕ) : ℚ) =
      2*(r:ℚ)+2*(m:ℚ)-(zSaving r m p k0 kw win : ℕ) := by
  unfold zPrice
  push_cast
  rw [zinterval_core_sum hpodd,zinterval_ext_sum hpodd hk0w hk0p]
  unfold zSaving
  push_cast
  split_ifs <;> ring

end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.knownIntervals_mem
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.zPrice_intervals
