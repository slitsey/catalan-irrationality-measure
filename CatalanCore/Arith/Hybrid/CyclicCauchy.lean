module
public import CatalanCore.Arith.Hybrid.CyclicPrefix
@[expose] public section
open Finset
namespace CatalanCore.Arith.Hybrid
variable {p : ℕ} [Fact p.Prime]

def intervalCauchyPotential (h : ℕ) (z : ZMod p) : ZMod p :=
  ∑c∈range h,((c:ZMod p)-z)⁻¹

lemma intervalCauchyPotential_step (h : ℕ) (z : ZMod p) :
    intervalCauchyPotential h (z+1)-intervalCauchyPotential h z=
      -((z+1)⁻¹-(z+1-(h:ZMod p))⁻¹) := by
  have H:=Finset.sum_range_sub' (fun c:ℕ=>((c:ZMod p)-z-1)⁻¹) h
  have he (c : ℕ) : ((c:ZMod p)-z-1)⁻¹-(((c+1:ℕ):ZMod p)-z-1)⁻¹=
      ((c:ZMod p)-(z+1))⁻¹-((c:ZMod p)-z)⁻¹ := by
    simp only [Nat.cast_add,Nat.cast_one]
    congr 2 <;> ring
  simp_rw [he] at H
  rw [Finset.sum_sub_distrib] at H
  change intervalCauchyPotential h (z+1)-intervalCauchyPotential h z=_ at H
  rw [H]
  simp only [Nat.cast_zero,zero_sub,
    show -z-1=-(z+1) by ring,
    show (h:ZMod p)-z-1=-(z+1-h) by ring,inv_neg]
  ring

/-- The reciprocal-difference prefix is an exact finite Cauchy potential.
This replaces separate harmonic reflection cases. -/
theorem cyclicPrefix_cauchy_potential (h a : ℕ) :
    cyclicPrefix (fun x:ZMod p=>x⁻¹-(x-h)⁻¹) a=
      intervalCauchyPotential h 0-intervalCauchyPotential h a := by
  have he (k : ℕ) : ((k+1:ℕ):ZMod p)⁻¹-(((k+1:ℕ):ZMod p)-h)⁻¹=
      intervalCauchyPotential h (k:ZMod p)-intervalCauchyPotential h ((k+1:ℕ):ZMod p) := by
    have H:=intervalCauchyPotential_step (p:=p) h k
    push_cast
    linear_combination H
  unfold cyclicPrefix
  simp_rw [he]
  simpa only [Nat.cast_zero] using
    Finset.sum_range_sub' (fun c:ℕ=>intervalCauchyPotential (p:=p) h c) a

/-- Off the pole set, a difference of Cauchy potentials is its Gram kernel. -/
theorem cauchyPotential_difference {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (c : ι→K) (z y : K)
    (hz : ∀i∈s,c i≠z) (hy : ∀i∈s,c i≠y) :
    (∑i∈s,(c i-y)⁻¹)-(∑i∈s,(c i-z)⁻¹)=
      (y-z)*∑i∈s,((c i-z)*(c i-y))⁻¹ := by
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hz':c i-z≠0:=sub_ne_zero.mpr (hz i hi)
  have hy':c i-y≠0:=sub_ne_zero.mpr (hy i hi)
  field_simp [hz',hy']
  <;> ring

theorem cyclicPrefix_short_kernel (h z y : ℕ)
    (hz : ∀c<h,(c:ZMod p)≠z) (hy : ∀c<h,(c:ZMod p)≠y) :
    cyclicPrefix (fun x:ZMod p=>x⁻¹-(x-h)⁻¹) z-
      cyclicPrefix (fun x:ZMod p=>x⁻¹-(x-h)⁻¹) y=
      ((y:ZMod p)-z)*∑c∈range h,(((c:ZMod p)-z)*((c:ZMod p)-y))⁻¹ := by
  rw [cyclicPrefix_cauchy_potential,cyclicPrefix_cauchy_potential]
  have H:=cauchyPotential_difference (range h) (fun c:ℕ=>(c:ZMod p)) (z:ZMod p) y
    (fun c hc=>hz c (mem_range.mp hc)) (fun c hc=>hy c (mem_range.mp hc))
  change intervalCauchyPotential h (y:ZMod p)-intervalCauchyPotential h (z:ZMod p)=_ at H
  linear_combination H
end CatalanCore.Arith.Hybrid
