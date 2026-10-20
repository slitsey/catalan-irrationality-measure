module
public import CatalanCore.Arith.Hybrid.CyclicPrefix
public import CatalanCore.Basic.ZModGood
@[expose] public section
open Finset CatalanCore
namespace CatalanCore.Arith.Hybrid
variable {p : ℕ} [Fact p.Prime]

noncomputable def regularInverse (p : ℕ) (a : ℤ) : ℚ :=
  if (p:ℤ)∣a then 0 else (a:ℚ)⁻¹

lemma good_regularInverse (a : ℤ) : Good p (regularInverse p a) ((a:ZMod p)⁻¹) := by
  classical
  by_cases ha : (p:ℤ)∣a
  · have hz : (a:ZMod p)=0:=(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr ha
    simpa only [regularInverse,if_pos ha,hz,inv_zero] using (Good.zero (ℓ:=p))
  · have hn : (a:ZMod p)≠0:=by rwa [Ne,ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa only [regularInverse,if_neg ha] using (Good.intCast (ℓ:=p) a).inv hn

noncomputable def regularDelta (p : ℕ) (o a : ℤ) : ℚ :=
  regularInverse p a-4*regularInverse p (4*a-o)
noncomputable def regularDsq (p : ℕ) (o a : ℤ) : ℚ :=
  regularInverse p a^2-16*regularInverse p (4*a-o)^2

lemma good_regularDelta (o a : ℤ) :
    Good p (regularDelta p o a) ((a:ZMod p)⁻¹-4*(4*(a:ZMod p)-o)⁻¹) := by
  simpa only [regularDelta,Int.cast_sub,Int.cast_mul,Int.cast_ofNat] using
    (good_regularInverse (p:=p) a).sub ((Good.ofNat (ℓ:=p) 4).mul (good_regularInverse (4*a-o)))

lemma good_regularDsq (o a : ℤ) :
    Good p (regularDsq p o a) (((a:ZMod p)⁻¹)^2-16*((4*(a:ZMod p)-o)⁻¹)^2) := by
  simpa only [regularDsq,Int.cast_sub,Int.cast_mul,Int.cast_ofNat] using
    ((good_regularInverse (p:=p) a).pow' 2).sub
      ((Good.ofNat (ℓ:=p) 16).mul ((good_regularInverse (4*a-o)).pow' 2))

noncomputable def regularPrefix (p : ℕ) (o : ℤ) (a : ℕ) : ℚ :=
  ∑k∈range a,regularDelta p o (k+1)

lemma quarter_regular_residue (o : ℤ) (h4 : (4:ZMod p)≠0) (x : ZMod p) :
    x⁻¹-4*(4*x-o)⁻¹=x⁻¹-(x-(4:ZMod p)⁻¹*o)⁻¹ := by
  have he : 4*x-o=4*(x-(4:ZMod p)⁻¹*o) := by field_simp <;> ring
  rw [he,mul_inv,←mul_assoc,mul_inv_cancel₀ h4,one_mul]

lemma good_regularPrefix (o : ℤ) (h4 : (4:ZMod p)≠0) (a : ℕ) :
    Good p (regularPrefix p o a)
      (cyclicPrefix (fun x=>x⁻¹-(x-(4:ZMod p)⁻¹*o)⁻¹) a) := by
  apply Good.sum
  intro k hk
  have H:=good_regularDelta (p:=p) o ((k+1:ℕ):ℤ)
  rw [quarter_regular_residue o h4] at H
  simpa only [Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_one,Int.cast_natCast] using H

/-- The regular part has exactly the same residue on congruent prefixes. -/
theorem good_regularPrefix_difference (o : ℤ) (h4 : (4:ZMod p)≠0)
    {a b : ℕ} (hab : a%p=b%p) :
    Good p (regularPrefix p o b-regularPrefix p o a) 0 := by
  have H:=(good_regularPrefix o h4 b).sub (good_regularPrefix o h4 a)
  have he:=cyclicPrefix_congr (fun x=>x⁻¹-(x-(4:ZMod p)⁻¹*(o:ZMod p))⁻¹)
    (reciprocal_difference_zero_mean _) hab
  simpa only [he,sub_self] using H
end CatalanCore.Arith.Hybrid
