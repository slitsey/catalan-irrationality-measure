module

public import CatalanCore.Uniform.Bank.Plane1.Dips.PlanePiv
public import CatalanCore.Uniform.Bank.Plane1.Dips.KnownZero.Member

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! First-period known zeros of every plane frame, at arbitrary geometry.
The optional upper window requires V=0; U=0 is used only on common nodes. -/
namespace CatalanCore.Uniform.Bank.Plane1.Dips
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Plane1
open CatalanCore.Uniform.Content.Shape CatalanCore.Arith.Hybrid Finset

@[reducible] def planeKA (σ : Support) (n p : ℕ) : ℕ := (n*p+σ.rho)/3
@[reducible] def planeKB (p : ℕ) : ℕ := (p+1)/2

theorem plane_first_levels (σ : Support) (a b c : ℤ) (h0 : a+b+c=0)
    {p : ℕ} [Fact p.Prime] (hp7 : 7≤p) {n : ℕ} (hn : n=1 ∨ n=2)
    (h3 : 3∣n*p+σ.rho) (t : ℕ) (ht : t<p) :
    Vp p (planeFrame σ a b c h0) t =
      (if planeKA σ n p≤t then 3*(a:ℚ)/(n:ℚ) else 0)+
        (if planeKB p≤t then 2*(b:ℚ) else 0) ∧
    Up p (planeFrame σ a b c h0) t =
      -(if planeKA σ n p≤t then 9*(a:ℚ)/(n:ℚ)^2 else 0)-
        (if planeKB p≤t then 4*(b:ℚ) else 0) := by
  constructor
  · rw [planeV_eq hp7 hn h3 t,Nat.div_eq_of_lt ht,Nat.mod_eq_of_lt ht]
    by_cases hA : planeKA σ n p≤t <;> by_cases hB : planeKB p≤t <;>
      simp only [planeKA,planeKB] at hA hB <;>
      simp [Vtab,FA,FB,FC,hA,hB]
  · rw [planeU_eq hp7 hn h3 t,Nat.div_eq_of_lt ht,Nat.mod_eq_of_lt ht]
    by_cases hA : planeKA σ n p≤t <;> by_cases hB : planeKB p≤t <;>
      simp only [planeKA,planeKB] at hA hB <;>
      simp [Utab,GA,GB,GC,hA,hB] <;> ring

theorem plane_cut_bounds (σ : Support) {p n : ℕ} (hp7 : 7≤p) (hn : n=1 ∨ n=2) :
    planeKA σ n p<p ∧ planeKB p<p := by
  have hρ : σ.rho≤2 := by cases σ <;> decide
  have hA := Nat.mod_add_div (n*p+σ.rho) 3
  have hB := Nat.mod_add_div (p+1) 2
  unfold planeKA planeKB
  rcases hn with rfl | rfl <;> omega

theorem plane_knownZero_levels (σ : Support) (a b c : ℤ) (h0 : a+b+c=0)
    {p n : ℕ} [Fact p.Prime] (hp7 : 7≤p) (hn : n=1 ∨ n=2) (h3 : 3∣n*p+σ.rho)
    (r m : ℕ) (win : Bool) (hret : win=true → 3*(a:ℚ)/(n:ℚ)+2*(b:ℚ)=0) :
    let K := knownIntervals r m p (min (planeKA σ n p) (planeKB p))
      (max (planeKA σ n p) (planeKB p)) win
    (∀ t,t<r+2*m → t∈K → Vp p (planeFrame σ a b c h0) t=0) ∧
      (∀ t,t<r → t∈K → Up p (planeFrame σ a b c h0) t=0) := by
  dsimp only
  have hcuts := plane_cut_bounds σ hp7 hn
  have hkp : min (planeKA σ n p) (planeKB p)≤p :=
    (min_le_left _ _).trans hcuts.1.le
  constructor
  · intro t ht hK
    have htp := knownIntervals_lt_p hkp hK
    rw [(plane_first_levels σ a b c h0 hp7 hn h3 t htp).1]
    rcases (knownIntervals_mem ht).mp hK with hl | hw
    · have hA : ¬planeKA σ n p≤t := by omega
      have hB : ¬planeKB p≤t := by omega
      simp [hA,hB]
    · have hA : planeKA σ n p≤t := (le_max_left _ _).trans hw.2.1
      have hB : planeKB p≤t := (le_max_right _ _).trans hw.2.1
      rw [if_pos hA,if_pos hB]
      exact hret hw.1
  · intro t ht hK
    have htp := knownIntervals_lt_p hkp hK
    have htN : t<r+2*m := by omega
    have hl : t<min (planeKA σ n p) (planeKB p) := by
      rcases (knownIntervals_mem htN).mp hK with h | h
      · exact h
      · omega
    have hA : ¬planeKA σ n p≤t := by omega
    have hB : ¬planeKB p≤t := by omega
    rw [(plane_first_levels σ a b c h0 hp7 hn h3 t htp).2]
    simp [hA,hB]

theorem plane_knownZero_alt_gle (g : ℚ) (hg : 0<g) (σ : Support)
    (a b c : ℤ) (h0 : a+b+c=0) (depth r m p n : ℕ) [Fact p.Prime]
    (hp7 : 7≤p) (hn : n=1 ∨ n=2) (h3 : 3∣n*p+σ.rho)
    (hm : m=(altGeom g hg).borderSize r) (hr : r%2=0)
    (hsq : 3*(r+2*m)<p*p) (hmp : 2*m<p) (hN : r+2*m≤2*p)
    (win : Bool) (hret : win=true → 3*(a:ℚ)/(n:ℚ)+2*(b:ℚ)=0)
    (S : Finset ((altGeom g hg).geometry r).C) :
    GLE p (zPrice r m p (knownIntervals r m p
      (min (planeKA σ n p) (planeKB p)) (max (planeKA σ n p) (planeKB p)) win)+2*(r-S.card))
      (((altGeom g hg).family (planeFrame σ a b c h0) depth).Q ⟨r,S⟩) := by
  let fl : ℕ → Bool → Bool → Bool := fun _ _ _ => false
  have hfl : FlagOK a b c n fl := by
    constructor
    intro q eA eB h
    simp [fl] at h
  have hP0 := hybPiv_plane (σ:=σ) (a:=a) (b:=b) (c:=c) (h0:=h0)
    (n:=n) (p:=p) (fl:=fl) (r:=r) (m:=m) hp7 hn h3 hfl hsq hmp
  have hR : pRd σ n p fl r m hmp=(fun _=>none) := by
    funext i
    unfold pRd
    simp [fl,isPiv]
  have hC : pCd σ n p fl r m hmp=(fun _=>none) := by
    funext i
    unfold pCd
    simp [fl,isPiv]
  rw [hR,hC] at hP0
  have hP : HybPiv r m p (planeFrame σ a b c h0) (fun _=>none) (fun _=>none)
      (fun _=>0) (fun _=>0) (fun i=>Vp p (planeFrame σ a b c h0) (r+2*i.val))
      (fun i=>Vp p (planeFrame σ a b c h0) (r+2*i.val+1)) := by
    simpa [fl,pRd,pCd,lamNode,vsNode,isPiv] using hP0
  have hc := plane_cut_bounds σ hp7 hn
  have hk : min (planeKA σ n p) (planeKB p)≤p := (min_le_left _ _).trans hc.1.le
  obtain ⟨hV,hU⟩ := plane_knownZero_levels σ a b c h0 hp7 hn h3 r m win hret
  exact knownZero_alt_member_gle g hg (planeFrame σ a b c h0) depth r m p hm hr hP hN _
    (fun t ht => knownIntervals_lt_p hk ht) hV hU S

end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.plane_first_levels
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.plane_knownZero_alt_gle
