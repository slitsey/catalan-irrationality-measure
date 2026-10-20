module
public import CatalanCore.Arith.Hybrid.PeriodicEntries
@[expose] public section
open CatalanCore
namespace CatalanCore.Arith.Hybrid.Periodic
open ChainClasses
variable {p o N : ℕ} [Fact p.Prime] {Fr : Frame}

lemma lam_regular_delta_dsq (hL : LamData Fr o) {t : ℕ} (ht : 1≤t)
    (hs : ¬Singular p o t) : Fr.Delta t∈S p ∧ Fr.Dsq t∈S p := by
  have hn : ((t:ℤ):ZMod p)≠0 := by
    rw [Ne,ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h=>hs (Or.inl h)
  have hm : ((4*(t:ℤ)-o:ℤ):ZMod p)≠0 := by
    rw [Ne,ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h=>hs (Or.inr h)
  have gt:=((Good.intCast (ℓ:=p) (t:ℤ)).inv hn)
  have gm:=((Good.intCast (ℓ:=p) (4*(t:ℤ)-o)).inv hm)
  constructor
  · rw [hL.delta_eq t ht]
    simpa [div_eq_mul_inv] using (gt.sub ((Good.ofNat (ℓ:=p) 4).mul gm)).mem
  · rw [hL.dsq_eq t ht]
    simpa [div_eq_mul_inv,inv_pow] using
      ((gt.pow' 2).sub ((Good.ofNat (ℓ:=p) 16).mul (gm.pow' 2))).mem

/-- The former lambda-specific chain hypotheses instantiate the periodic interface. -/
noncomputable def lamPoleData (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) :
    PoleData Fr p N where
  singular := Singular p o
  periodic := singular_periodic p o
  norm_mem := by rw [hL.norm_eq];exact (Good.ofNat (ℓ:=p) 16).mem
  norm_ne := by
    rw [hL.norm_eq]
    have h : (16:ZMod p)≠0 := by
      have H:=four_ne_zmod p hp
      convert mul_ne_zero H H using 1 <;> norm_num
    simpa [red] using h
  delta_mem := fun t ht htN=>(good_Delta_uniform hL hN ht htN).mem
  dsq_mem := fun t ht htN=>(good_Dsq_uniform hL hN ht htN).mem
  regular_delta := fun t ht _ hs=>(lam_regular_delta_dsq hL ht hs).1
  regular_dsq := fun t ht _ hs=>(lam_regular_delta_dsq hL ht hs).2
end CatalanCore.Arith.Hybrid.Periodic
