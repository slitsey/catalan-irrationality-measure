module
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0145.Hdom
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0145.BaseN
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0145.Psi
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0145.Graph
public import CatalanMeasure.GenD.Uniform.W.Charts6.Unit13
public import CatalanMeasure.GenD.Uniform.Bank532.Final534
public import CatalanMeasure.GenD.Uniform.W.Charts6.MonoHost3
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Uniform.W.Charts6.L0145
section PartH
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- The reduced profile-coordinate atoms of the jet kernel. -/
abbrev X' (hW : Win N p) (x : Fin p → Fin pk.d → Fp) : Fin p → Fin 44 → Fp :=
  fun e => projExtras (hKp hW) (insL p (emb pk p 33 (x e)))

theorem poly_AE (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (k : Fin (bN dsg N p)) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inl (k, 1))) = polx (Xr x) ⟨3 * k.val, by
      have := k.isLt; have h10 := geom_bN hW; omega⟩ := by
  have hk : k.val < 10 := by have := k.isLt; have h10 := geom_bN hW; omega
  have e : (ckEquiv (hKp hW)).symm (Sum.inl (k, 1)) = iotaF ⟨3 * k.val, by omega⟩ := by
    apply Fin.ext
    rw [idx_val, iotaF_val]
    show 4 * k.val + _ = iotaN (3 * k.val)
    have := iota_blk k.val hk 0 (by norm_num)
    simp only [add_zero] at this
    rw [this]; first | rfl | omega | simp
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k 1), e]
  exact polx_ins (fun e => emb pk p 33 (x e)) _

theorem poly_CF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (k : Fin (bN dsg N p)) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inl (k, 2))) = polx (Xr x) ⟨3 * k.val + 1, by
      have := k.isLt; have h10 := geom_bN hW; omega⟩ := by
  have hk : k.val < 10 := by have := k.isLt; have h10 := geom_bN hW; omega
  have e : (ckEquiv (hKp hW)).symm (Sum.inl (k, 2)) = iotaF ⟨3 * k.val + 1, by omega⟩ := by
    apply Fin.ext
    rw [idx_val, iotaF_val]
    show 4 * k.val + _ = iotaN (3 * k.val + 1)
    rw [iota_blk k.val hk 1 (by norm_num)]; first | rfl | omega | simp
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k 2), e]
  exact polx_ins (fun e => emb pk p 33 (x e)) _

theorem poly_CE (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (k : Fin (bN dsg N p)) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inl (k, 3))) = polx (Xr x) ⟨3 * k.val + 2, by
      have := k.isLt; have h10 := geom_bN hW; omega⟩ := by
  have hk : k.val < 10 := by have := k.isLt; have h10 := geom_bN hW; omega
  have e : (ckEquiv (hKp hW)).symm (Sum.inl (k, 3)) = iotaF ⟨3 * k.val + 2, by omega⟩ := by
    apply Fin.ext
    rw [idx_val, iotaF_val]
    show 4 * k.val + _ = iotaN (3 * k.val + 2)
    rw [iota_blk k.val hk 2 (by norm_num)]; first | rfl | omega | simp
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k 3), e]
  exact polx_ins (fun e => emb pk p 33 (x e)) _

theorem poly_AF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (k : Fin (bN dsg N p)) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inl (k, 0))) = 0 := by
  have hk : k.val < 10 := by have := k.isLt; have h10 := geom_bN hW; omega
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k 0)]
  apply polx_ins_zero
  intro c' h
  have := iota_not_AF k.val hk c'
  rw [h, idx_val] at this
  simp at this

theorem poly_ZE (hW : Win N p) (x : Fin p → Fin pk.d → Fp) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inr (Sum.inl 1))) = polx (Xr x) 30 := by
  have e : (ckEquiv (hKp hW)).symm (Sum.inr (Sum.inl 1)) = iotaF 30 := by
    apply Fin.ext
    rw [Pilot146O.ck_Z_val, iotaF_val]
    have hb := geom_bN hW
    simp [iotaN, hb]
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_Z _ 1), e]
  exact polx_ins (fun e => emb pk p 33 (x e)) _

theorem poly_ZF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inr (Sum.inl 0))) = 0 := by
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_Z _ 0)]
  apply polx_ins_zero
  intro c' h
  have := iota_not_ZF c'
  rw [h, Pilot146O.ck_Z_val] at this
  have hb := geom_bN hW
  simp [hb] at this

set_option maxHeartbeats 4000000 in
theorem hdom_145 (hW : Win N p) (hp2 : p ≠ 2) (hn : 1 ≤ dsg.n N)
    (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∃ c : Fin (dsg.n N) → Fp, Theta (P := dsg) (N := N) hp2 hn (hKp hW) c = X' hW x := by
  have hb10 : bN dsg N p = 10 := geom_b hW
  have hb : 0 < bN dsg N p := by rw [hb10]; norm_num
  have hrN : dsg.h N % p = 3 * N := geom_hmod hW
  have hN20 : 20 ≤ N := hW.1
  have h59 : 59 * N < 10 * p := hW.2.1
  have h6N : 1 * p ≤ 6 * N := hW.2.2.1
  have hodd : p % 2 = 1 := hW.2.2.2
  have hk10 : ∀ k : Fin (bN dsg N p), k.val < 10 := fun k => by have := k.isLt; omega
  refine exists_rows_of_orders_high hp2 hn (hKp hW) hb (X' hW x) ?hX ?hr0 ?hrh ?hFA ?hFZ
    (8 * N - p) (56 * N - 9 * p - 1) ?hlob ?hlot ?hA ?hC ?hZ ?hVb ?hVt
  case hX =>
    intro e j
    show projExtras _ _ _ = 0
    rw [projExtras_apply, if_pos ⟨j, by simp⟩]
  case hr0 => rw [hrN]; omega
  case hrh => rw [hrN]; omega
  case hFA => exact fun k => poly_AF hW x k
  case hFZ => exact poly_ZF hW x
  case hlob => rw [hrN, geom_ja hW]; omega
  case hlot => rw [hrN, geom_rho hW]; omega
  case hA =>
    intro k
    have hk := hk10 k
    constructor
    · intro j hj
      rw [hrN] at hj
      rw [poly_AE hW x k]
      exact chainAE1 hW x hker _ (by simpa using pt1_AE ⟨k.val, hk⟩) j (by rw [wd3 hW]; omega)
    · intro i hi
      rw [hrN] at hi
      rw [poly_AE hW x k]
      have h6 := wd6 hW
      exact Pilot146O.coeff_of_inf _ (polx_degree _ _) (wd N p 6) (3 * N) (by omega) (by omega)
        (fun j hj => chainInf1 hW x hker _ (by simpa using inf_AE ⟨k.val, hk⟩) j hj) i hi
  case hC =>
    intro k
    have hk := hk10 k
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hrN] at hj
      rw [poly_CF hW x k]
      have := pt1_CF ⟨k.val, hk⟩
      exact chainCF hW x hker _ (by simpa using this.1) (by simpa using this.2.1) (by simpa using this.2.2) j hj
    · intro j hj
      rw [poly_CF hW x k, poly_CE hW x k]
      exact chainDiff hW x hker _ _ (by intro h; have := congrArg Fin.val h; simp at this)
        (by simpa using ptm1_C ⟨k.val, hk⟩) j hj
    · intro i hi
      rw [hrN] at hi
      rw [poly_CE hW x k]
      have h6 := wd6 hW; have h7 := wd7 hW
      have := inf_CE ⟨k.val, hk⟩
      exact Pilot146O.coeff_of_inf _ (polx_degree _ _) (wd N p 6 + wd N p 7) (3 * N - 1) (by omega) (by omega)
        (fun j hj => chainInf2 hW x hker _ (by simpa using this.1) (by simpa using this.2) j hj) i hi
  case hZ =>
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hrN] at hj
      rw [poly_ZE hW x]
      exact chainAE1 hW x hker _ (by simpa using pt1_ZE) j (by rw [wd3 hW]; omega)
    · intro i hi
      rw [hrN] at hi
      rw [poly_ZE hW x]
      have h6 := wd6 hW
      exact Pilot146O.coeff_of_inf _ (polx_degree _ _) (wd N p 6) (3 * N) (by omega) (by omega)
        (fun j hj => chainInf1 hW x hker _ (by simpa using inf_ZE) j hj) i hi
    · intro j hj
      rw [poly_ZF hW x, poly_ZE hW x]
      exact chainNeg2 hW hp2 x hker _ (by simpa using ptm1_Z) j hj
  case hVb =>
    intro i hi
    have e0 : ∀ h, (⟨3 * (⟨0, hb⟩ : Fin (bN dsg N p)).val, h⟩ : Fin 33) = 0 := fun h => Fin.ext (by simp)
    have e2 : ∀ h, (⟨3 * (⟨0, hb⟩ : Fin (bN dsg N p)).val + 2, h⟩ : Fin 33) = 2 := fun h => Fin.ext (by simp)
    rw [poly_AE hW x ⟨0, hb⟩, poly_CE hW x ⟨0, hb⟩, poly_ZE hW x]
    simp only [e0, e2]
    have h6 := wd6 hW; have h7 := wd7 hW; have h8 := wd8 hW; have h9 := wd9 hW
    exact Pilot146O.coeff_of_inf _ (lt_of_le_of_lt (degree_add_le _ _) (max_lt
        (lt_of_le_of_lt (degree_sub_le _ _) (max_lt (polx_degree _ _) (polx_degree _ _))) (polx_degree _ _)))
      (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9) (8 * N - p) (by omega) (by omega)
      (fun j hj => chainVB hW x hker j hj) i hi
  case hVt =>
    intro i hi
    rw [poly_AE hW x ⟨bN dsg N p - 1, by omega⟩, poly_CE hW x ⟨bN dsg N p - 1, by omega⟩]
    have h6 := wd6 hW; have h7 := wd7 hW; have h8 := wd8 hW
    have e1 : (⟨3 * (bN dsg N p - 1), by omega⟩ : Fin 33) = 27 := by
      apply Fin.ext; simp only; omega
    have e3 : (⟨3 * (bN dsg N p - 1) + 2, by omega⟩ : Fin 33) = 29 := by
      apply Fin.ext; simp only; omega
    simp only [e1, e3]
    exact Pilot146O.coeff_of_inf _ (lt_of_le_of_lt (degree_add_le _ _) (max_lt (polx_degree _ _) (polx_degree _ _)))
      (wd N p 6 + wd N p 7 + wd N p 8) (56 * N - 9 * p - 1) (by omega) (by omega)
      (fun j hj => chainVT hW x hker j hj) i hi

end
end PartH

section PartP
open Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts5 Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap)
noncomputable section

theorem insL_eq_sum {p : ℕ} [Fact p.Prime] (y : Fin 33 → ZMod p) :
    insL p y = ∑ c : Fin 33, y c • (Pi.single (iotaF c) (1 : ZMod p) : Fin 44 → ZMod p) := by
  funext c
  rw [insL_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c' _ => ?_
  by_cases h : iotaF c' = c
  · simp [h]
  · simp [h, Ne.symm h]

theorem psi_row {p : ℕ} [Fact p.Prime] (hp : 13 < p) (F : Prof p 44) (hF : pd146.Realises F)
    {g i J : ℕ} {S : ℤ} {ε : ℤ} {H : ℕ}
    (hok : rowOK g i J S ε = true) (hJ : J < 12) (hS : S.toNat + 3 ≤ 16) (hH : S.toNat + 3 ≤ H)
    (y : Fin 33 → ZMod p)
    (hy : ∑ c : Fin 33, ((((oRows g).getD i []).getD c 0 : ℤ) : ZMod p) * y c = 0) :
    F.psi H J S (insL p y) = y 31 + (ε : ZMod p) * y 32 := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨hi, hneg⟩, hdvd⟩, hε⟩, hall⟩, h42⟩, h43⟩ := hok
  set r := (oRows g).getD i [] with hr
  have hZp : ¬ p ∣ ZM := not_dvd_ZM hp
  have hZ : ((ZM : ℕ) : ZMod p) ≠ 0 := fun h => hZp ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hD : ((r.getD 31 0 : ℤ) : ZMod p) ≠ 0 :=
    CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ (Int.dvd_of_emod_eq_zero hdvd) (by omega)
  have hm : ∀ c : Fin 33, ((rowInt pd146 ZM J S (iotaN c.val) : ℤ) : ZMod p) =
      (ZM : ZMod p) * F.psi H J S (Pi.single (iotaF c) 1) :=
    fun c => rowInt_mod (Ub := 16) (Jb := 12) hZp pd146 F hF (iotaF c) hJ hS hH
  have hpsi0 : ∀ c : Fin 33, 31 ≤ c.val → F.psi H J S (Pi.single (iotaF c) 1) = 0 := by
    intro c hc
    have : c.val = 31 ∨ c.val = 32 := by have := c.isLt; omega
    have h0 : rowInt pd146 ZM J S (iotaN c.val) = 0 := by
      rcases this with h | h
      · rw [h]; exact h42
      · rw [h]; exact h43
    have := hm c
    rw [h0] at this
    simp only [Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hZ
  have hrow : ∀ c : Fin 33, c.val < 31 →
      ((r.getD c 0 : ℤ) : ZMod p) = -((r.getD 31 0 : ℤ) : ZMod p) * F.psi H J S (Pi.single (iotaF c) 1) := by
    intro c hc
    have e := hall c.val hc
    have e' := congrArg (fun z : ℤ => (z : ZMod p)) e
    simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast] at e'
    rw [hm c] at e'
    apply mul_right_cancel₀ hZ
    simp only [ZM] at e' ⊢
    linear_combination e'
  have hlin : F.psi H J S (insL p y) = ∑ c : Fin 33, y c * F.psi H J S (Pi.single (iotaF c) 1) := by
    rw [insL_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, smul_eq_mul]
  have hcoef : ∀ c : Fin 33, ((r.getD c 0 : ℤ) : ZMod p) * y c =
      -((r.getD 31 0 : ℤ) : ZMod p) * (y c * F.psi H J S (Pi.single (iotaF c) 1)) +
        (if c = 31 then ((r.getD 31 0 : ℤ) : ZMod p) * y c else 0) +
        (if c = 32 then ((r.getD 32 0 : ℤ) : ZMod p) * y c else 0) := by
    intro c
    by_cases hc : c.val < 31
    · have h1 : c ≠ 31 := fun h => by rw [h] at hc; simp at hc
      have h2 : c ≠ 32 := fun h => by rw [h] at hc; simp at hc
      rw [if_neg h1, if_neg h2, hrow c hc]; ring
    · rw [hpsi0 c (by omega)]
      have : c = 31 ∨ c = 32 := by
        rcases (by have := c.isLt; omega : c.val = 31 ∨ c.val = 32) with h | h
        · left; exact Fin.ext h
        · right; exact Fin.ext h
      rcases this with rfl | rfl
      · simp
      · simp
  have hsum : ∑ c : Fin 33, ((r.getD c 0 : ℤ) : ZMod p) * y c =
      -((r.getD 31 0 : ℤ) : ZMod p) * F.psi H J S (insL p y) + ((r.getD 31 0 : ℤ) : ZMod p) * y 31 +
        ((r.getD 32 0 : ℤ) : ZMod p) * y 32 := by
    simp_rw [hcoef]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hlin]
    simp
  rw [hsum, hε] at hy
  push_cast at hy
  apply mul_left_cancel₀ hD
  linear_combination -hy

end
end PartP
section Part0
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Charts CatalanMeasure.GenD.Uniform.W.Charts5 Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem chart_row_sum (g i : ℕ) (hg : g < 11) (hi : i < (oRows g).length)
    (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, by rw [pk_len]; exact hg⟩) p 33 y = 0) :
    ∑ c : Fin 33, ((((oRows g).getD i []).getD c 0 : ℤ) : Fp) * emb pk p 33 y c = 0 := by
  have hrows := chart_rows (⟨g, by rw [pk_len]; exact hg⟩ : Fin pk.charts.length)
  have hi' : i < (pk.chart ⟨g, by rw [pk_len]; exact hg⟩).rows.length := by
    rw [hrows]; exact hi
  have := row_of_chart (K := 33) _ hy i hi'
  convert this using 2
  rw [Mx, hrows]

theorem rowOK_lt {g i J : ℕ} {S ε : ℤ} (h : rowOK g i J S ε = true) : i < (oRows g).length := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1

theorem chart_unit32 (g : ℕ) (hg : g < 11) (h : hasRow g (unitL 32) = true) (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, by rw [pk_len]; exact hg⟩) p 33 y = 0) :
    emb pk p 33 y 32 = 0 := by
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp (List.contains_iff_mem.mp h)
  have := chart_row_sum g i hg hi y hy
  rw [List.getD_eq_getElem _ _ hi, hir] at this
  have e := sum_unitL (32 : Fin 33) (emb pk p 33 y)
  have e2 : ((32 : Fin 33) : ℕ) = 32 := rfl
  rw [e2] at e
  exact e.symm.trans this

theorem jet0_eq (m : ℕ) (e : Fin p) (h : m = e.val) :
    (jet0 m : (Fin p → Fin pk.d → Fp) →ₗ[Fp] (Fin pk.d → Fp)) = LinearMap.proj e := by
  subst h; simp [jet0, e.isLt]

theorem jetInf_eq (m : ℕ) (e : Fin p) (h : m = p - 1 - e.val) :
    (jetInf m : (Fin p → Fin pk.d → Fp) →ₗ[Fp] (Fin pk.d → Fp)) = LinearMap.proj e := by
  have hm : m < p := by have := e.isLt; omega
  simp only [jetInf, dif_pos hm]
  congr 1
  exact Fin.ext (by simp only; omega)

/-- A seen covector read off one stored row. -/
theorem cover_row (M : MonoData dsg N p 44) (hM : pd146.Realises M.prof) (hp : 13 < p)
    {g i J : ℕ} {S ε : ℤ} (hg : g < 11) (hok : rowOK g i J S ε = true) (hJ : J < 12)
    (hS : S.toNat + 3 ≤ 16) (hH : S.toNat + 3 ≤ dsg.H N) (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, by rw [pk_len]; exact hg⟩) p 33 y = 0) :
    M.sys.prof.psi (dsg.H N) J S (insL p (emb pk p 33 y)) =
      emb pk p 33 y 31 + (ε : Fp) * emb pk p 33 y 32 :=
  psi_row hp M.prof hM hok hJ hS hH (emb pk p 33 y) (chart_row_sum g i hg (rowOK_lt hok) y hy)

theorem rows_inf' (g J : ℕ) (hg6 : 6 ≤ g) (hg10 : g ≤ 10) (hJ2 : 2 ≤ J) (hJ11 : J ≤ 11)
    (h11 : J = 11 → g ≤ 9) : rowOK g (ridx g J) J 12 0 = true := by
  have := rows_inf ⟨g - 6, by omega⟩ ⟨J - 2, by omega⟩ (by intro h; simp only [Fin.val_mk] at h ⊢; have := h11 (by omega); omega)
  simp only [Fin.val_mk] at this
  have e1 : g - 6 + 6 = g := by omega
  have e2 : J - 2 + 2 = J := by omega
  rw [e1, e2] at this
  exact this

/-- The reversed jet `p - 1 - e` lies in one of the `∞` groups 6..10 (groups 6..9 when it is small). -/
theorem inf_group (hW : Win N p) (e : Fin p)
    (hm : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10) :
    ∃ g k, 6 ≤ g ∧ g ≤ 10 ∧ k < wd N p g ∧ jetP N p g k = LinearMap.proj e ∧
      (p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 → g ≤ 9) := by
  have hep := e.isLt
  by_cases h6 : p - 1 - e.val < wd N p 6
  · exact ⟨6, p - 1 - e.val, le_refl _, by norm_num, h6,
      by rw [show jetP N p 6 (p - 1 - e.val) = jetInf (p - 1 - e.val) by simp [jetP]]; exact jetInf_eq _ e rfl,
      fun _ => by norm_num⟩
  by_cases h7 : p - 1 - e.val < wd N p 6 + wd N p 7
  · refine ⟨7, p - 1 - e.val - wd N p 6, by norm_num, by norm_num, by omega, ?_, fun _ => by norm_num⟩
    rw [show jetP N p 7 (p - 1 - e.val - wd N p 6) = jetInf (wd N p 6 + (p - 1 - e.val - wd N p 6)) by simp [jetP]]
    exact jetInf_eq _ e (by omega)
  by_cases h8 : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8
  · refine ⟨8, p - 1 - e.val - (wd N p 6 + wd N p 7), by norm_num, by norm_num, by omega, ?_,
      fun _ => by norm_num⟩
    rw [show jetP N p 8 (p - 1 - e.val - (wd N p 6 + wd N p 7)) =
      jetInf (wd N p 6 + wd N p 7 + (p - 1 - e.val - (wd N p 6 + wd N p 7))) by simp [jetP]]
    exact jetInf_eq _ e (by omega)
  by_cases h9 : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9
  · refine ⟨9, p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8), by norm_num, by norm_num, by omega, ?_,
      fun _ => by norm_num⟩
    rw [show jetP N p 9 (p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8)) =
      jetInf (wd N p 6 + wd N p 7 + wd N p 8 + (p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8))) by simp [jetP]]
    exact jetInf_eq _ e (by omega)
  · refine ⟨10, p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9), by norm_num, le_refl _,
      by omega, ?_, fun h => absurd h h9⟩
    rw [show jetP N p 10 (p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9)) =
      jetInf (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 +
        (p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9))) by simp [jetP]]
    exact jetInf_eq _ e (by omega)

theorem lt_wNat {k : ℕ} (g : ℕ) (hg : g < 11) (hk : k < wd N p g) :
    k < wNat (⟨g, by rw [pk_len]; exact hg⟩ : Fin pk.charts.length) N p := hk

theorem jetS_eq (e : Fin p) (g k : ℕ) (hg : g < 11) (hk : k < wd N p g)
    (h : jetP N p g k = LinearMap.proj e) :
    (fun (g : Fin pk.charts.length) (k : Fin (wNat g N p)) => jetP N p g.val k.val)
      ⟨g, by rw [pk_len]; exact hg⟩ ⟨k, lt_wNat _ hg hk⟩ = LinearMap.proj e := h

theorem jet1_eq (e : Fin p) (he : e.val < wd N p 1) :
    jetP N p 1 e.val = LinearMap.proj e := by
  simp only [jetP]; exact jet0_eq _ e rfl

theorem jet2_eq (e : Fin p) (he : wd N p 1 ≤ e.val) :
    jetP N p 2 (e.val - wd N p 1) = LinearMap.proj e := by
  simp only [jetP]; exact jet0_eq _ e (by omega)

theorem cover_145 (hW : Win N p) (M : MonoData dsg N p 44) (hM : pd146.Realises M.prof) :
    CoverPt3 pk M (insL p) (low145 p) (fun g => wNat g N p) (dsg.q N / p)
      (fun g k => jetP N p g.val k.val) := by
  have hN := hW.1; have h59 := hW.2.1; have h6N := hW.2.2.1; have hodd := hW.2.2.2
  have hp13 : 13 < p := by omega
  have hq0 : dsg.q N / p = 0 := geom_qdiv hW
  have hH : dsg.H N = 78 * N := design_H N
  have w1 := wd1 hW; have w2 := wd2 hW; have w6 := wd6 hW; have w7 := wd7 hW; have w8 := wd8 hW
  have w9 := wd9 hW; have w10 := wd10 hW
  have hpne : (p : ℤ) ≠ 0 := by have := (Fact.out : p.Prime).pos; omega
  unfold CoverPt3
  intro j hj1 hj2 e hdvd
  rw [hq0] at hj2 ⊢
  rw [design_b] at hj1
  rw [design_L] at hj2
  have hj2' : j < 70 * N := by omega
  obtain ⟨s, hs0⟩ := hdvd
  have hs := hs0
  rw [hH] at hs
  have hjl : p * (j / p) + j % p = j := Nat.div_add_mod j p
  have hl : j % p < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
  generalize j / p = J at hjl ⊢
  generalize j % p = l at hjl hl hs0 hs ⊢
  have he := e.isLt
  have hpz : (0 : ℤ) ≤ p := by positivity
  have hJ12 : J < 12 := by
    by_contra h; push_neg at h
    have := Nat.mul_le_mul_left p h; omega
  have hs14 : s ≤ 13 := by
    by_contra h; push_neg at h
    have := Int.mul_le_mul_of_nonneg_left (show (14:ℤ) ≤ s by omega) hpz
    omega
  have hs12 : 12 ≤ s := by
    by_contra h; push_neg at h
    have := Int.mul_le_mul_of_nonneg_left (show s ≤ 11 by omega) hpz
    omega
  have fin : ∀ (S : ℤ) (y : Fin pk.d → Fp),
      M.sys.prof.psi (dsg.H N) (J) S (insL p (emb pk p 33 y)) = emb pk p 33 y 31 →
      ∑ v ∈ range (0 + 1), ((-1 : ZMod p) ^ (0 - v) * ((Nat.choose 0 v : ℕ) : ZMod p)) *
        M.sys.prof.psi (dsg.H N) (J + v) S (insL p (emb pk p 33 y)) = low145 p y := by
    intro S y h; simp [low145_apply, h]
  have hden : ((dsg.H N : ℤ) - 1 - ((l : ℕ) : ℤ) - (e : ℕ)) / (p : ℤ) = s := by
    rw [hs0, Int.mul_ediv_cancel_left _ hpne]
  have hs13 : s = 12 ∨ s = 13 := by omega
  rcases hs13 with h12 | h13
  · -- S = 12 : the position is seen through the infinite groups
    subst h12
    have hel : wd N p 1 ≤ e.val := by omega
    have hm5 : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10 := by omega
    obtain ⟨g', k', hg6, hg10, hk', hjet', hg9⟩ := inf_group hW e hm5
    have hrow' : hasRow g' (unitL 32) = true := by
      obtain ⟨r6, r7, r8, r9, r10⟩ := inf_low
      interval_cases g' <;> assumption
    have hJ1 : 1 ≤ J := by
      by_contra h
      have h0 : J = 0 := by omega
      rw [h0] at hjl; omega
    by_cases hJ1' : J = 1
    · -- the graph row of group 2 and the slack row
      subst hJ1'
      have hew2 : e.val - wd N p 1 < wd N p 2 := by omega
      refine ⟨⟨2, by rw [pk_len]; norm_num⟩, ⟨e.val - wd N p 1, lt_wNat _ (by norm_num) hew2⟩,
        ⟨g', by rw [pk_len]; omega⟩, ⟨k', lt_wNat _ (by omega) hk'⟩,
        jet2_eq e hel, jetS_eq e g' k' (by omega) hk' hjet', ?_⟩
      intro y hy hy'
      rw [hden]
      apply fin
      rw [cover_row M hM hp13 (g := 2) (i := 0) (J := 1) (S := 12) (ε := 1) (by norm_num)
        rows_graph.2 (by norm_num) (by norm_num) (by rw [hH]; omega) y hy,
        chart_unit32 g' (by omega) hrow' y hy']
      simp
    · have hJ2 : 2 ≤ J := by omega
      by_cases hJ11 : J = 11
      · have hel2 : 8 * N - p ≤ e.val := by rw [hJ11] at hjl; omega
        have hm4 : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 := by omega
        have hg9' := hg9 hm4
        refine ⟨⟨g', by rw [pk_len]; omega⟩, ⟨k', lt_wNat _ (by omega) hk'⟩,
          ⟨g', by rw [pk_len]; omega⟩, ⟨k', lt_wNat _ (by omega) hk'⟩,
          jetS_eq e g' k' (by omega) hk' hjet', jetS_eq e g' k' (by omega) hk' hjet', ?_⟩
        intro y hy _
        rw [hden]
        apply fin
        have hok := rows_inf' g' J hg6 hg10 hJ2 (by omega) (fun _ => hg9')
        have := cover_row M hM hp13 (g := g') (i := ridx g' J) (J := J) (S := 12) (ε := 0) (by omega)
          hok hJ12 (by norm_num) (by rw [hH]; omega) y hy
        rw [this]; simp
      · have hJ10 : J ≤ 10 := by omega
        refine ⟨⟨g', by rw [pk_len]; omega⟩, ⟨k', lt_wNat _ (by omega) hk'⟩,
          ⟨g', by rw [pk_len]; omega⟩, ⟨k', lt_wNat _ (by omega) hk'⟩,
          jetS_eq e g' k' (by omega) hk' hjet', jetS_eq e g' k' (by omega) hk' hjet', ?_⟩
        intro y hy _
        rw [hden]
        apply fin
        have hok := rows_inf' g' J hg6 hg10 hJ2 (by omega) (fun h => absurd h hJ11)
        have := cover_row M hM hp13 (g := g') (i := ridx g' J) (J := J) (S := 12) (ε := 0) (by omega)
          hok hJ12 (by norm_num) (by rw [hH]; omega) y hy
        rw [this]; simp
  · -- S = 13 : group 1, row raw[J,0].prefix
    subst h13
    have hew : e.val < wd N p 1 := by omega
    have hJ2 : 2 ≤ J := by
      by_contra h
      have : J = 0 ∨ J = 1 := by omega
      rcases this with rfl | rfl <;> omega
    have hJ11 : J ≤ 11 := by omega
    refine ⟨⟨1, by rw [pk_len]; norm_num⟩, ⟨e.val, lt_wNat _ (by norm_num) hew⟩,
      ⟨1, by rw [pk_len]; norm_num⟩, ⟨e.val, lt_wNat _ (by norm_num) hew⟩,
      jet1_eq e hew, jet1_eq e hew, ?_⟩
    intro y hy _
    rw [hden]
    apply fin
    have hok := rows_zero ⟨J - 2, by omega⟩
    simp only [show J - 2 + 2 = J by omega] at hok
    rw [cover_row M hM hp13 (g := 1) (i := J - 2) (J := J) (S := 13) (ε := 0) (by norm_num)
      hok hJ12 (by norm_num) (by rw [hH]; omega) y hy]
    simp

end
end Part0

section Part1
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Charts CatalanMeasure.GenD.Uniform.W.Charts5 Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section

theorem cNat_eq {N p : ℕ} (hp2 : p % 2 = 1) : cNat N p = p := by
  simp only [cNat, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.cNat]
  omega

theorem monoProfile_realises145 {N p : ℕ} [Fact p.Prime] (hW : Win N p) {K : ℕ}
    (hK : K = bN dsg N p * 4 + 2 + 2) : pd146.Realises (monoProfile dsg N p hK) := by
  have h0 := realises_abs (p := p) (geom_b hW) hK
  have e1 : k0N dsg N p = -1 := geom_k0 hW
  have e2 : dsg.h N / p = 0 := geom_hdiv hW
  unfold monoProfile
  rw [e1, e2]
  exact h0

/-- **The physical host of the L0145 packet.** -/
theorem physHost_145 : CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.Phys := by
  intro N p hN hp hp2 hH hApp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, hpD⟩ := hApp
  have hn : 1 ≤ dsg.n N := by rw [Pilot146O.design_n]; have := hW.1; omega
  have hK' : 44 = bN dsg N p * 4 + 2 + 2 := hKp hW
  let M : MonoData dsg N p 44 := monoData hp2 hn hK'
  have hM : pd146.Realises M.prof := monoProfile_realises145 hW hK'
  have hc : CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.cNat N p = p := cNat_eq hW.2.2.2
  rw [hc]
  refine ⟨M.sys, ⟨?_⟩⟩
  exact monoHost3 (width := fun g => wNat g N p) M (insL p) ((projExtras hK').comp (insL p))
    (fun y => sumProf_proj hK' _ (fun j => rfl) (insL p y))
    (fun y => sumProf_proj hK' _ (fun j => rfl) (insL p y))
    (low145 p) (dsg.q N / p) (dsg.q N % p) (fun g k => jetP N p g.val k.val)
    (fun x hker hproj => hinj_145 hW hpD x hker hproj)
    (fun x hker => by
      obtain ⟨c, hc⟩ := hdom_145 hW hp2 hn x hker
      exact ⟨c, hc⟩)
    (fun x hker => hG_145 hW x hker)
    (cover_145 hW M hM)

end
end Part1

section Part2
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

theorem win_L0145 :
    WinCert (NullityLB.ofPacketHost D58.Odd.design_admissible
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.pk
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.pk_sound
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.Win
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.cNat
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.wNat physHost_145)
      (cw (59 / 10 : ℝ) (6 : ℝ) (-59 : ℝ) (10 : ℝ)) :=
  CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.win0 D58.Odd.design_admissible physHost_145

end
end Part2


section Part3
open CatalanMeasure.GenD.Uniform.Bank532

/-- `Hosts534`: its single field is the physical host of the L0145 packet. -/
theorem hosts534 : Hosts534 := ⟨physHost_145⟩

/-- **`μ(G) ≤ 534`.** -/
theorem catalan_irrationalityMeasure_534 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(534 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  catalan_irrationalityMeasure_534_of_hosts hosts534
end Part3
end CatalanMeasure.GenD.Uniform.W.Charts6.L0145

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.hdom_145
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.hG_145
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.hinj_145
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.rows_zero
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.rows_graph
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.rows_inf
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.psi_row
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.cover_145
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.physHost_145
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.win_L0145
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0145.catalan_irrationalityMeasure_534
