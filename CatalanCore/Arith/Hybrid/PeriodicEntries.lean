module

public import CatalanCore.Arith.Hybrid.UniformEntries
public import CatalanCore.Arith.Hybrid.ChainTransport

@[expose] public section
open Finset Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.Periodic

/-- Entry-level periodic pole data. No Schur or determinant conclusion is assumed. -/
structure PoleData (Fr : Frame) (p N : ℕ) [Fact p.Prime] where
  singular : ℤ → Prop
  periodic : ∀ t j : ℤ, singular (t+j*p) ↔ singular t
  norm_mem : Fr.norm ∈ S p
  norm_ne : red p Fr.norm ≠ 0
  delta_mem : ∀ k, 1≤k → k<N → (p:ℚ)*Fr.Delta k ∈ S p
  dsq_mem : ∀ k, 1≤k → k<N → (p:ℚ)^2*Fr.Dsq k ∈ S p
  regular_delta : ∀ k, 1≤k → k<N → ¬singular k → Fr.Delta k ∈ S p
  regular_dsq : ∀ k, 1≤k → k<N → ¬singular k → Fr.Dsq k ∈ S p

variable {Fr : Frame} {p N : ℕ} [Fact p.Prime]
namespace PoleData
noncomputable def dv (D : PoleData Fr p N) (k : ℕ) : ZMod p := red p ((p:ℚ)*Fr.Delta k)
noncomputable def sv (D : PoleData Fr p N) (k : ℕ) : ZMod p := red p ((p:ℚ)^2*Fr.Dsq k)
noncomputable def V (D : PoleData Fr p N) (a : ℕ) : ZMod p := ∑k∈Icc 1 a,D.dv k
noncomputable def W (D : PoleData Fr p N) (a : ℕ) : ZMod p := ∑k∈Icc 1 a,D.sv k

lemma good_delta (D : PoleData Fr p N) {k : ℕ} (hk : 1≤k) (hN : k<N) :
    Good p ((p:ℚ)*Fr.Delta k) (D.dv k) := good_red (D.delta_mem k hk hN)
lemma good_dsq (D : PoleData Fr p N) {k : ℕ} (hk : 1≤k) (hN : k<N) :
    Good p ((p:ℚ)^2*Fr.Dsq k) (D.sv k) := good_red (D.dsq_mem k hk hN)
lemma dv_zero (D : PoleData Fr p N) {k : ℕ} (hk : 1≤k) (hN : k<N)
    (hs : ¬D.singular k) : D.dv k=0 := by
  exact ((D.good_delta hk hN).eq.symm.trans ((good_red (D.regular_delta k hk hN hs)).ell_mul.eq))
lemma sv_zero (D : PoleData Fr p N) {k : ℕ} (hk : 1≤k) (hN : k<N)
    (hs : ¬D.singular k) : D.sv k=0 := by
  have g := ((good_red (D.regular_dsq k hk hN hs)).ell_mul).ell_mul
  have g' : Good p ((p:ℚ)^2*Fr.Dsq k) 0 := g.congr' (by ring)
  exact (D.good_dsq hk hN).eq.symm.trans g'.eq

lemma sum_delta (D : PoleData Fr p N) {a b : ℕ} (hb : b<N) :
    Good p ((p:ℚ)*∑k∈Ioc a b,Fr.Delta k) (∑k∈Ioc a b,D.dv k) := by
  rw [Finset.mul_sum]
  exact Good.sum _ _ _ fun k hk => D.good_delta (by have := (mem_Ioc.mp hk).1;omega)
    (by have := (mem_Ioc.mp hk).2;omega)
lemma sum_dsq (D : PoleData Fr p N) {a : ℕ} (ha : a<N) :
    Good p ((p:ℚ)^2*∑k∈Icc 1 a,Fr.Dsq k) (D.W a) := by
  rw [Finset.mul_sum]
  exact Good.sum _ _ _ fun k hk => D.good_dsq (mem_Icc.mp hk).1
    (by have := (mem_Icc.mp hk).2;omega)

lemma V_sub (D : PoleData Fr p N) {a b : ℕ} (hab : a≤b) :
    D.V b-D.V a=∑k∈Ioc a b,D.dv k := by
  have he (n : ℕ) : Icc 1 n=Ioc 0 n := by ext k;simp only [mem_Icc,mem_Ioc];omega
  unfold V
  rw [he,he,←Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

lemma good_square (D : PoleData Fr p N) (hN : N<p*p)
    {a b : ℕ} (hab : a<b) (hb : b<N) :
    Good p ((p:ℚ)^2*Fr.Mn a b)
      ((red p Fr.norm)⁻¹*invResidue p (b-a)*(D.V b-D.V a)) := by
  have gn := (good_red D.norm_mem).inv D.norm_ne
  have gd := good_scaled_inverse (p:=p) (n:=b-a) (by omega) (by omega)
  have gs := D.sum_delta hb (a:=a)
  have g := (gn.mul gd).mul gs
  rw [←D.V_sub hab.le] at g
  apply g.congr'
  rw [Frame.Mn,if_neg hab.ne,min_eq_left hab.le,max_eq_right hab.le]
  have hc : ((b-a:ℕ):ℚ)=(b:ℚ)-a := Nat.cast_sub hab.le
  rw [hc]
  simp only [div_eq_mul_inv]
  ring

lemma good_diagonal (D : PoleData Fr p N) {a : ℕ} (ha : a<N) :
    Good p ((p:ℚ)^2*Fr.Mn a a) (-(red p Fr.norm)⁻¹*D.W a) := by
  have g := ((good_red D.norm_mem).inv D.norm_ne).neg.mul (D.sum_dsq ha)
  apply g.congr'
  rw [Frame.Mn,if_pos rfl]
  simp only [div_eq_mul_inv]
  ring

lemma square_mem (D : PoleData Fr p N) (hN : N<p*p)
    {a b : ℕ} (ha : a<N) (hb : b<N) : (p:ℚ)^2*Fr.Mn a b∈S p := by
  rcases lt_trichotomy a b with h|rfl|h
  · exact (D.good_square hN h hb).mem
  · exact (D.good_diagonal ha).mem
  · rw [Mn_symm];exact (D.good_square hN h ha).mem

lemma good_cross_ordered (D : PoleData Fr p N)
    {a b : ℕ} (hab : a<b) (hb : b<N) (hd : ((b:ZMod p)-a)≠0) :
    Good p ((p:ℚ)*Fr.Mn a b)
      (((red p Fr.norm)*((b:ZMod p)-a))⁻¹*(D.V b-D.V a)) := by
  have gn := (good_red D.norm_mem).inv D.norm_ne
  have gd := ((Good.natCast (ℓ:=p) b).sub (Good.natCast a)).inv hd
  have gs := D.sum_delta hb (a:=a)
  rw [←D.V_sub hab.le] at gs
  have g := (gn.mul gd).mul gs
  refine (g.congr' ?_).congr ?_
  · rw [Frame.Mn,if_neg hab.ne,min_eq_left hab.le,max_eq_right hab.le]
    simp only [div_eq_mul_inv]
    ring
  · rw [mul_inv]

lemma good_cross (D : PoleData Fr p N) {a b : ℕ} (ha : a<N) (hb : b<N)
    (hd : ((b:ZMod p)-a)≠0) :
    Good p ((p:ℚ)*Fr.Mn a b)
      (((red p Fr.norm)*((b:ZMod p)-a))⁻¹*(D.V b-D.V a)) := by
  rcases lt_trichotomy a b with h|rfl|h
  · exact D.good_cross_ordered h hb hd
  · exact False.elim (hd (sub_self _))
  · have hd' : ((a:ZMod p)-b)≠0 := by intro he;apply hd;linear_combination -he
    rw [Mn_symm]
    refine (D.good_cross_ordered h ha hd').congr ?_
    rw [show (a:ZMod p)-b=-((b:ZMod p)-a) by ring,mul_neg,inv_neg]
    ring
end PoleData
end CatalanCore.Arith.Hybrid.Periodic
