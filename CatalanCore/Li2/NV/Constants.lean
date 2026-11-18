module
public import CatalanCore.Li2.NV.TieFree
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable def KV (a c s : ℕ) (z : ℚ) : ℚ := K ⟨.V,a,c,s⟩ z
noncomputable def KU (a c s : ℕ) (z : ℚ) : ℚ := K ⟨.U,a,c,s⟩ z
end CatalanCore.Li2.NVMod
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
noncomputable def c1 (z : ℚ) (q k : ℕ) : ℚ :=
  KU q (4*q+k) (2*q+k) z*KV (q+1) (4*q+k) (2*q+k-2) z
noncomputable def c2 (z : ℚ) (q k : ℕ) : ℚ :=
  KU q (4*q+k) (2*q+k-1) z*KV (q+1) (4*q+k) (2*q+k-1) z
noncomputable def Tprime (z : ℚ) (n ℓ : ℕ) : ℚ :=
  c1 z (n/ℓ) (k n ℓ)-c2 z (n/ℓ) (k n ℓ)*BinTail (r n ℓ) (r' n ℓ) z⁻¹
noncomputable def constantInt {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (A : TypeKey) : PadicInt ℓ :=
  (Matrix.of fun i j : Fin A.size => R.moments A (i.val+j.val)).det
theorem constantInt_cast {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (A : TypeKey) (ha : A.a≤A.c) (hc : A.c<ℓ) :
    (constantInt R A:Padic ℓ)=(K A z:Padic ℓ) := by
  let M : Matrix (Fin A.size) (Fin A.size) (PadicInt ℓ) := fun i j => R.moments A (i.val+j.val)
  let N : Matrix (Fin A.size) (Fin A.size) ℚ := fun i j => L A z (X^(i.val+j.val))
  have hm : PadicInt.Coe.ringHom.mapMatrix M=(Rat.castHom (Padic ℓ)).mapMatrix N := by
    ext i j
    exact R.moments_cast A ha hc (i.val+j.val)
  have hd := congrArg Matrix.det hm
  rw [←RingHom.map_det,←RingHom.map_det] at hd
  exact hd
theorem constantInt_red {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (A : TypeKey) : reduceInt ℓ (constantInt R A)=redK R A := by
  rw [constantInt,(reduceInt ℓ).map_det]
  rfl
theorem constantInt_unit {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (A : TypeKey) (ha : A.a≤A.c) (hc : A.c<ℓ)
    (hK : Unit ℓ (K A z:Padic ℓ)) : Unit ℓ (constantInt R A:Padic ℓ) := by
  rwa [constantInt_cast R A ha hc]
theorem c1_c2_unit (z : ℚ) (q k ℓ : ℕ) [Fact ℓ.Prime]
    (hv : k<4 ∧ (1≤q ∨ k=3)) (hk : 1≤k)
    (hK : AllConstantsUnit z q k ℓ) :
    Unit ℓ (c1 z q k:Padic ℓ) ∧ Unit ℓ (c2 z q k:Padic ℓ) := by
  have hu : Unit ℓ (KU q (4*q+k) (2*q+k) z:Padic ℓ) :=
    hK _ (by simp [neededAtValid,hv,neededAt,hk])
  have hc : Unit ℓ (KV (q+1) (4*q+k) (2*q+k-2) z:Padic ℓ) :=
    hK _ (by simp [neededAtValid,hv,neededAt,hk])
  have hum : Unit ℓ (KU q (4*q+k) (2*q+k-1) z:Padic ℓ) :=
    hK _ (by simp [neededAtValid,hv,neededAt,hk])
  have hcp : Unit ℓ (KV (q+1) (4*q+k) (2*q+k-1) z:Padic ℓ) :=
    hK _ (by simp [neededAtValid,hv,neededAt,hk])
  simp only [Unit] at hu hc hum hcp
  constructor
  · simp only [c1,Rat.cast_mul,Unit,norm_mul,hu,hc,one_mul]
  · simp only [c2,Rat.cast_mul,Unit,norm_mul,hum,hcp,one_mul]
theorem reduceInt_ne_zero_iff_unit (ℓ : ℕ) [Fact ℓ.Prime] (x : PadicInt ℓ) :
    reduceInt ℓ x≠0 ↔ Unit ℓ (x:Padic ℓ) := by
  constructor
  · intro hx
    change ‖x‖=1
    apply le_antisymm (PadicInt.norm_le_one x)
    by_contra hn
    have hlt : ‖x‖<1 := lt_of_not_ge hn
    have hker : x∈RingHom.ker (PadicInt.toZMod : PadicInt ℓ→+*ZMod ℓ) := by
      rw [PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton]
      exact (PadicInt.norm_lt_one_iff_dvd x).mp hlt
    exact hx hker
  · exact reduce_ne_zero_of_unit ℓ x
noncomputable def c1Int {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) : PadicInt ℓ := constantInt R (keyU n ℓ)*constantInt R (keyC n ℓ)
noncomputable def c2Int {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) : PadicInt ℓ := constantInt R (keyUminus n ℓ)*constantInt R (keyCplus n ℓ)
theorem c1Int_cast {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ)
    (haC : (keyC n ℓ).a≤(keyC n ℓ).c) (hcC : (keyC n ℓ).c<ℓ)
    (haU : (keyU n ℓ).a≤(keyU n ℓ).c) (hcU : (keyU n ℓ).c<ℓ) :
    (c1Int R:Padic ℓ)=(c1 z (n/ℓ) (k n ℓ):Padic ℓ) := by
  rw [c1Int,PadicInt.coe_mul,constantInt_cast R _ haU hcU,constantInt_cast R _ haC hcC]
  rfl
theorem c2Int_cast {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ)
    (hsize : 2≤m0 n ℓ)
    (haC : (keyC n ℓ).a≤(keyC n ℓ).c) (hcC : (keyC n ℓ).c<ℓ)
    (haU : (keyU n ℓ).a≤(keyU n ℓ).c) (hcU : (keyU n ℓ).c<ℓ) :
    (c2Int R:Padic ℓ)=(c2 z (n/ℓ) (k n ℓ):Padic ℓ) := by
  rw [c2Int,PadicInt.coe_mul,constantInt_cast R (keyUminus n ℓ) haU hcU,
    constantInt_cast R (keyCplus n ℓ) haC hcC]
  have he : mC n ℓ+1=2*(n/ℓ)+k n ℓ-1 := by unfold mC m0 at *; omega
  simp only [c2,KU,KV,keyUminus,keyCplus,m0,he,Rat.cast_mul]
theorem c1Int_red {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ) :
    reduceInt ℓ (c1Int R)=redK R (keyU n ℓ)*redK R (keyC n ℓ) := by
  simp only [c1Int,map_mul,constantInt_red]
theorem c2Int_red {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ) :
    reduceInt ℓ (c2Int R)=redK R (keyUminus n ℓ)*redK R (keyCplus n ℓ) := by
  simp only [c2Int,map_mul,constantInt_red]
private theorem coe_inv_of_unit (ℓ : ℕ) [Fact ℓ.Prime] (x : PadicInt ℓ) (hx : ‖x‖=1) :
    ((x.inv:PadicInt ℓ):Padic ℓ)=(x:Padic ℓ)⁻¹ := by
  have hm:=congrArg (fun y : PadicInt ℓ=>(y:Padic ℓ)) (PadicInt.mul_inv hx)
  simp only [PadicInt.coe_mul,PadicInt.coe_one] at hm
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)
private theorem reduce_inv_of_unit (ℓ : ℕ) [Fact ℓ.Prime] (x : PadicInt ℓ) (hx : ‖x‖=1) :
    reduceInt ℓ x.inv=(reduceInt ℓ x)⁻¹ := by
  have hm:=congrArg (reduceInt ℓ) (PadicInt.mul_inv hx)
  simp only [map_mul,map_one] at hm
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)
def binTailInt (ℓ : ℕ) [Fact ℓ.Prime] (r t : ℕ) (y : PadicInt ℓ) : PadicInt ℓ :=
  ∑ i∈Finset.Ioc t r,(Nat.choose r i:PadicInt ℓ)*y^i*(1-y)^(r-i)
private theorem binTailInt_cast (ℓ : ℕ) [Fact ℓ.Prime] (r t : ℕ) (y : PadicInt ℓ) :
    (binTailInt ℓ r t y:Padic ℓ)=BinTail r t (y:Padic ℓ) := by
  change PadicInt.Coe.ringHom (binTailInt ℓ r t y)=_
  simp only [binTailInt,BinTail,map_sum,map_mul,map_pow,map_sub,map_one,map_natCast,
    PadicInt.Coe.ringHom_apply]
private theorem binTailInt_red (ℓ : ℕ) [Fact ℓ.Prime] (r t : ℕ) (y : PadicInt ℓ) :
    reduceInt ℓ (binTailInt ℓ r t y)=BinTail r t (reduceInt ℓ y) := by
  simp only [binTailInt,BinTail,map_sum,map_mul,map_pow,map_sub,map_one,map_natCast]
noncomputable def TprimeInt {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (hz : Unit ℓ (z:Padic ℓ)) : PadicInt ℓ :=
  c1Int R-c2Int R*binTailInt ℓ (r n ℓ) (r' n ℓ) (zInteger z ℓ hz).inv
theorem TprimeInt_cast {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ)
    (hz : Unit ℓ (z:Padic ℓ))
    (hsize : 2≤m0 n ℓ)
    (haC : (keyC n ℓ).a≤(keyC n ℓ).c) (hcC : (keyC n ℓ).c<ℓ)
    (haU : (keyU n ℓ).a≤(keyU n ℓ).c) (hcU : (keyU n ℓ).c<ℓ) :
    (TprimeInt R hz:Padic ℓ)=(Tprime z n ℓ:Padic ℓ) := by
  rw [TprimeInt,PadicInt.coe_sub,PadicInt.coe_mul,c1Int_cast R haC hcC haU hcU,
    c2Int_cast R hsize haC hcC haU hcU,binTailInt_cast,
    coe_inv_of_unit ℓ _ (show ‖zInteger z ℓ hz‖=1 from hz)]
  simp only [Tprime,BinTail,Rat.cast_sub,Rat.cast_mul,Rat.cast_sum,Rat.cast_pow,Rat.cast_inv,
    Rat.cast_natCast,Rat.cast_one,zInteger]
theorem TprimeInt_red {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (hz : Unit ℓ (z:Padic ℓ)) :
    reduceInt ℓ (TprimeInt R hz)=
      redK R (keyU n ℓ)*redK R (keyC n ℓ)-
        redK R (keyUminus n ℓ)*redK R (keyCplus n ℓ)*
          BinTail (r n ℓ) (r' n ℓ) (reduceInt ℓ (zInteger z ℓ hz))⁻¹ := by
  simp only [TprimeInt,map_sub,map_mul,c1Int_red,c2Int_red,binTailInt_red,
    reduce_inv_of_unit ℓ _ (show ‖zInteger z ℓ hz‖=1 from hz)]
theorem Tprime_unit_iff {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ)
    (hz : Unit ℓ (z:Padic ℓ))
    (hsize : 2≤m0 n ℓ)
    (haC : (keyC n ℓ).a≤(keyC n ℓ).c) (hcC : (keyC n ℓ).c<ℓ)
    (haU : (keyU n ℓ).a≤(keyU n ℓ).c) (hcU : (keyU n ℓ).c<ℓ) :
    Unit ℓ (Tprime z n ℓ:Padic ℓ) ↔ reduceInt ℓ (TprimeInt R hz)≠0 := by
  rw [reduceInt_ne_zero_iff_unit,TprimeInt_cast R hz hsize haC hcC haU hcU]
#print axioms constantInt_cast
#print axioms constantInt_red
#print axioms constantInt_unit
#print axioms c1_c2_unit
#print axioms reduceInt_ne_zero_iff_unit
#print axioms c1Int_cast
#print axioms c2Int_cast
#print axioms c1Int_red
#print axioms c2Int_red
#print axioms TprimeInt_cast
#print axioms TprimeInt_red
#print axioms Tprime_unit_iff
end
end CatalanCore.Li2.NV
