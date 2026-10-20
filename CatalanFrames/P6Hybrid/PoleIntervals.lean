module
public import CatalanFrames.P6Hybrid.PoleData
public import CatalanCore.Rect.PeriodicMinor
public import CatalanCore.Arith.Hybrid.WitnessWeight
@[expose] public section
open Finset Polynomial Matrix CatalanCore CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid
open ChainClasses

def p6PoleMask (c : ℕ) (j : ℤ) : Prop :=
  j%6=0 ∨ j%6=3 ∨ j%6=(if c=1 then 2 else 4)

lemma p6_singular_index {p c : ℕ} (hc : c=1 ∨ c=5) (hpc : p%6=c)
    {t : ℤ} (ht : p6Singular p t) :
    ∃j : ℤ,∃e : ℤ,0≤e ∧ e≤4 ∧ 6*t=j*p+e ∧ p6PoleMask c j := by
  have hpc' : (p:ℤ)%6=c := by exact_mod_cast hpc
  rcases ht with ⟨q,hq⟩|⟨q,hq⟩|⟨q,hq⟩
  · refine ⟨6*q,0,by omega,by omega,?_,Or.inl ?_⟩
    · linear_combination 6*hq
    · omega
  · refine ⟨2*q,4,by omega,by omega,?_,Or.inr (Or.inr ?_)⟩
    · linear_combination 2*hq
    · have H:=congrArg (fun x:ℤ=>x%3) hq
      have hp3 : (p:ℤ)%3=(c:ℤ)%3 := by omega
      have ht3 : (3*t-2)%3=1 := by omega
      rw [ht3,Int.mul_emod,hp3] at H
      rcases hc with rfl|rfl <;> norm_num at H ⊢ <;> omega
  · refine ⟨3*q,3,by omega,by omega,?_,Or.inr (Or.inl ?_)⟩
    · linear_combination 3*hq
    · have H:=congrArg (fun x:ℤ=>x%2) hq
      have hp2 : (p:ℤ)%2=1 := by rcases hc with rfl|rfl <;> omega
      have ht2 : (2*t-1)%2=1 := by omega
      rw [ht2,Int.mul_emod,hp2] at H
      norm_num at H
      omega

lemma p6_no_pole_between {p c : ℕ} (hp : 0<p) (hc : c=1 ∨ c=5) (hpc : p%6=c)
    {j k t : ℤ} (hgap : ∀a,j<a→a<k→¬p6PoleMask c a)
    (hl : j*p+4<6*t) (hu : 6*t<k*p) : ¬p6Singular p t := by
  intro ht
  obtain ⟨a,e,he0,he4,ha,hm⟩:=p6_singular_index hc hpc ht
  have hp' : (0:ℤ)<p := by exact_mod_cast hp
  have hja : j<a := by nlinarith
  have hak : a<k := by nlinarith
  exact hgap a hja hak hm

/-- A pole-free interval inside one zone period has no chain-entry or exit cut. -/
lemma p6_cut_between {p r : ℕ} (hp : 0<p) {a b : ℤ}
    (hra : (r:ℤ)≤a) (hbp : b<r+p)
    (hs : ∀t,a<t→t≤b→¬p6Singular p t) :
    NoCut (Cut p r (p6Singular p)) a b := by
  intro t hat htb ht
  rcases ht with ht|⟨q,hq⟩|⟨q,hq⟩
  · exact hs t hat htb ht
  · exact hs t hat htb (Or.inl ⟨q,by linear_combination hq⟩)
  · have hp' : (0:ℤ)<p := by exact_mod_cast hp
    have hq0 : 0<q := by nlinarith
    have hq1 : q<1 := by nlinarith
    omega
end CatalanFrames.P6Hybrid
