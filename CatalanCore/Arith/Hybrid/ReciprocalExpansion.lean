module
public import CatalanCore.Arith.Hybrid.LemmaE.Bridge
public import CatalanCore.Basic.ZModGood
@[expose] public section
open CatalanCore
namespace CatalanCore.Arith.Hybrid
variable {p : ℕ} [Fact p.Prime]

/-- Exact first variation, followed by reduction. This uses rational arithmetic
and never identifies a p-adic carry with a characteristic-p formal variable. -/
theorem good_reciprocal_difference {d t : ℚ} {dr tr : ZMod p}
    (hd : Good p d dr) (ht : Good p t tr) (hdr : dr≠0) :
    Good p (((d+(p:ℚ)*t)⁻¹-d⁻¹)/(p:ℚ)) (-tr/(dr*dr)) := by
  have hdt : Good p (d+(p:ℚ)*t) dr := by simpa using hd.add ht.ell_mul
  have gd : Good p d⁻¹ dr⁻¹:=hd.inv hdr
  have gdt : Good p (d+(p:ℚ)*t)⁻¹ dr⁻¹:=hdt.inv hdr
  have hp0 : (p:ℚ)≠0:=by exact_mod_cast (Fact.out:p.Prime).ne_zero
  have hd0 : d≠0 := by
    intro h
    apply hdr
    rw [←hd.eq,h]
    simp [red]
  have hdt0 : d+(p:ℚ)*t≠0 := by
    intro h
    apply hdr
    rw [←hdt.eq,h]
    simp [red]
  have H := (ht.neg.mul gd).mul gdt
  refine (H.congr' ?_).congr ?_
  · field_simp [hd0,hdt0,hp0]
    ring_nf
    have HH : t*(p:ℚ)+d≠0 := by simpa [mul_comm,add_comm] using hdt0
    field_simp [HH]
    <;> ring
  · simp only [div_eq_mul_inv,mul_inv]
    ring
end CatalanCore.Arith.Hybrid
