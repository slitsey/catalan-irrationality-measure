module
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0135.Core
public import CatalanMeasure.GenD.Uniform.W.Charts5.Prof146
public import CatalanMeasure.GenD.Uniform.W.Charts6.ProfB
public import CatalanMeasure.GenD.Uniform.W.Charts6.Unit13
public import CatalanMeasure.GenD.Uniform.W.Charts6.MonoHost3
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Uniform.W.Charts6.L0135
section PartPsi
open Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts5
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap)
noncomputable section

/-- The moment denominator used for the rows. -/
abbrev ZM : ℕ := Zmom 17 14

def rowOK (g i J : ℕ) (S : ℤ) (ε13 ε1 : ℤ) : Bool :=
  let r := (oRows g).getD i []
  decide (i < (oRows g).length) && decide (r.getD 34 0 < 0) &&
    decide ((30030 ^ 40 : ℤ) % (r.getD 34 0) = 0) &&
    decide (r.getD 35 0 = ε13 * r.getD 34 0) && decide (r.getD 36 0 = ε1 * r.getD 34 0) &&
    (List.range 34).all (fun c => decide (r.getD c 0 * (ZM : ℤ) = -(r.getD 34 0) * rowInt (pdB 11) ZM J S (iotaN c))) &&
    decide (rowInt (pdB 11) ZM J S 46 = 0) && decide (rowInt (pdB 11) ZM J S 47 = 0) &&
    decide (rowInt (pdB 11) ZM J S 48 = 0)

theorem ZM_dvd : ZM ∣ 30030 ^ 40 := by decide +kernel

theorem not_dvd_ZM {p : ℕ} [Fact p.Prime] (hp : 13 < p) : ¬ p ∣ ZM := by
  intro h
  have h1 : p ∣ 30030 ^ 40 := h.trans ZM_dvd
  have hpn := (Fact.out : p.Prime)
  have h2 : p ∣ 30030 := hpn.dvd_of_dvd_pow h1
  have e : (30030 : ℕ) = 2 * 3 * 5 * 7 * 11 * 13 := by norm_num
  rw [e] at h2
  rcases (Nat.Prime.dvd_mul hpn).mp h2 with h | h
  · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
          · have := Nat.le_of_dvd (by norm_num) h; omega
          · have := Nat.le_of_dvd (by norm_num) h; omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

set_option maxRecDepth 100000 in
theorem rows_zero : ∀ J : Fin 11, rowOK 1 J.val (J.val + 2) 14 0 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rows_graph13 : rowOK 1 11 13 14 1 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rows_graph1 : rowOK 1 12 1 13 0 1 = true ∧ rowOK 2 0 1 13 0 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rows_inf : ∀ J : Fin 11, rowOK 6 (J.val + 1) (J.val + 2) 13 0 0 = true := by decide +kernel

end
end PartPsi
section Part0
open Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts5 Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap)
noncomputable section

theorem insL_eq_sum {p : ℕ} [Fact p.Prime] (y : Fin 37 → ZMod p) :
    insL p y = ∑ c : Fin 37, y c • (Pi.single (iotaF c) (1 : ZMod p) : Fin 49 → ZMod p) := by
  funext c
  rw [insL_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c' _ => ?_
  by_cases h : iotaF c' = c
  · simp [h]
  · simp [h, Ne.symm h]

theorem psi_row {p : ℕ} [Fact p.Prime] (hp : 13 < p) (F : Prof p 49) (hF : (pdB 11).Realises F)
    {g i J : ℕ} {S : ℤ} {ε13 ε1 : ℤ} {H : ℕ}
    (hok : rowOK g i J S ε13 ε1 = true) (hJ : J < 14) (hS : S.toNat + 3 ≤ 17) (hH : S.toNat + 3 ≤ H)
    (y : Fin 37 → ZMod p)
    (hy : ∑ c : Fin 37, ((((oRows g).getD i []).getD c 0 : ℤ) : ZMod p) * y c = 0) :
    F.psi H J S (insL p y) = y 34 + (ε13 : ZMod p) * y 35 + (ε1 : ZMod p) * y 36 := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hi, hneg⟩, hdvd⟩, hε13⟩, hε1⟩, hall⟩, h46⟩, h47⟩, h48⟩ := hok
  set r := (oRows g).getD i [] with hr
  have hZp : ¬ p ∣ ZM := not_dvd_ZM hp
  have hZ : ((ZM : ℕ) : ZMod p) ≠ 0 := fun h => hZp ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hD : ((r.getD 34 0 : ℤ) : ZMod p) ≠ 0 :=
    CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ (Int.dvd_of_emod_eq_zero hdvd) (by omega)
  have hm : ∀ c : Fin 37, ((rowInt (pdB 11) ZM J S (iotaN c.val) : ℤ) : ZMod p) =
      (ZM : ZMod p) * F.psi H J S (Pi.single (iotaF c) 1) :=
    fun c => rowInt_mod (Ub := 17) (Jb := 14) hZp (pdB 11) F hF (iotaF c) hJ hS hH
  have hpsi0 : ∀ c : Fin 37, 34 ≤ c.val → F.psi H J S (Pi.single (iotaF c) 1) = 0 := by
    intro c hc
    have : c.val = 34 ∨ c.val = 35 ∨ c.val = 36 := by have := c.isLt; omega
    have h0 : rowInt (pdB 11) ZM J S (iotaN c.val) = 0 := by
      rcases this with h | h | h
      · rw [h]; exact h46
      · rw [h]; exact h47
      · rw [h]; exact h48
    have := hm c
    rw [h0] at this
    simp only [Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hZ
  have hrow : ∀ c : Fin 37, c.val < 34 →
      ((r.getD c 0 : ℤ) : ZMod p) = -((r.getD 34 0 : ℤ) : ZMod p) * F.psi H J S (Pi.single (iotaF c) 1) := by
    intro c hc
    have e := hall c.val hc
    have e' := congrArg (fun z : ℤ => (z : ZMod p)) e
    simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast] at e'
    rw [hm c] at e'
    apply mul_right_cancel₀ hZ
    simp only [ZM] at e' ⊢
    linear_combination e'
  have hlin : F.psi H J S (insL p y) = ∑ c : Fin 37, y c * F.psi H J S (Pi.single (iotaF c) 1) := by
    rw [insL_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, smul_eq_mul]
  have hcoef : ∀ c : Fin 37, ((r.getD c 0 : ℤ) : ZMod p) * y c =
      -((r.getD 34 0 : ℤ) : ZMod p) * (y c * F.psi H J S (Pi.single (iotaF c) 1)) +
        (if c = 34 then ((r.getD 34 0 : ℤ) : ZMod p) * y c else 0) +
        (if c = 35 then ((r.getD 35 0 : ℤ) : ZMod p) * y c else 0) +
        (if c = 36 then ((r.getD 36 0 : ℤ) : ZMod p) * y c else 0) := by
    intro c
    by_cases hc : c.val < 34
    · have h1 : c ≠ 34 := fun h => by rw [h] at hc; simp at hc
      have h2 : c ≠ 35 := fun h => by rw [h] at hc; simp at hc
      have h3 : c ≠ 36 := fun h => by rw [h] at hc; simp at hc
      rw [if_neg h1, if_neg h2, if_neg h3, hrow c hc]; ring
    · rw [hpsi0 c (by omega)]
      have : c = 34 ∨ c = 35 ∨ c = 36 := by
        rcases (by have := c.isLt; omega : c.val = 34 ∨ c.val = 35 ∨ c.val = 36) with h | h | h
        · left; exact Fin.ext h
        · right; left; exact Fin.ext h
        · right; right; exact Fin.ext h
      rcases this with rfl | rfl | rfl <;> simp
  have hsum : ∑ c : Fin 37, ((r.getD c 0 : ℤ) : ZMod p) * y c =
      -((r.getD 34 0 : ℤ) : ZMod p) * F.psi H J S (insL p y) + ((r.getD 34 0 : ℤ) : ZMod p) * y 34 +
        ((r.getD 35 0 : ℤ) : ZMod p) * y 35 + ((r.getD 36 0 : ℤ) : ZMod p) * y 36 := by
    simp_rw [hcoef]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hlin]
    simp
  rw [hsum, hε13, hε1] at hy
  push_cast at hy
  apply mul_left_cancel₀ hD
  linear_combination -hy

end
end Part0

section Part1
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Charts CatalanMeasure.GenD.Uniform.W.Charts5 Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem chart_row_sum (g i : ℕ) (hg : g < 11) (hi : i < (oRows g).length)
    (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, by rw [pk_len]; exact hg⟩) p 37 y = 0) :
    ∑ c : Fin 37, ((((oRows g).getD i []).getD c 0 : ℤ) : Fp) * emb pk p 37 y c = 0 := by
  have hrows := chart_rows (⟨g, by rw [pk_len]; exact hg⟩ : Fin pk.charts.length)
  have hi' : i < (pk.chart ⟨g, by rw [pk_len]; exact hg⟩).rows.length := by
    rw [hrows]; exact hi
  have := row_of_chart (K := 37) _ hy i hi'
  convert this using 2
  rw [Mx, hrows]

theorem rowOK_lt {g i J : ℕ} {S ε13 ε1 : ℤ} (h : rowOK g i J S ε13 ε1 = true) : i < (oRows g).length := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1

theorem chart_unit (c : Fin 37) (g : ℕ) (hg : g < 11) (h : hasRow g (unitL c) = true) (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, by rw [pk_len]; exact hg⟩) p 37 y = 0) :
    emb pk p 37 y c = 0 := by
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp (List.contains_iff_mem.mp h)
  have := chart_row_sum g i hg hi y hy
  rw [List.getD_eq_getElem _ _ hi, hir] at this
  exact (sum_unitL c (emb pk p 37 y)).symm.trans this

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
theorem cover_row (M : MonoData dsg N p 49) (hM : (pdB 11).Realises M.prof) (hp : 13 < p)
    {g i J : ℕ} {S ε13 ε1 : ℤ} (hg : g < 11) (hok : rowOK g i J S ε13 ε1 = true) (hJ : J < 14)
    (hS : S.toNat + 3 ≤ 17) (hH : S.toNat + 3 ≤ dsg.H N) (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, by rw [pk_len]; exact hg⟩) p 37 y = 0) :
    M.sys.prof.psi (dsg.H N) J S (insL p (emb pk p 37 y)) =
      emb pk p 37 y 34 + (ε13 : Fp) * emb pk p 37 y 35 + (ε1 : Fp) * emb pk p 37 y 36 :=
  psi_row hp M.prof hM hok hJ hS hH (emb pk p 37 y) (chart_row_sum g i hg (rowOK_lt hok) y hy)

/-- The reversed jet `p - 1 - e` lies in one of the `∞` groups 6..10. -/
theorem inf_group (hW : Win N p) (e : Fin p)
    (hm : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10) :
    ∃ g k, 6 ≤ g ∧ g ≤ 10 ∧ k < wd N p g ∧ jetP N p g k = LinearMap.proj e := by
  have hep := e.isLt
  by_cases h6 : p - 1 - e.val < wd N p 6
  · exact ⟨6, p - 1 - e.val, le_refl _, by norm_num, h6,
      by rw [show jetP N p 6 (p - 1 - e.val) = jetInf (p - 1 - e.val) by simp [jetP]]; exact jetInf_eq _ e rfl⟩
  by_cases h7 : p - 1 - e.val < wd N p 6 + wd N p 7
  · refine ⟨7, p - 1 - e.val - wd N p 6, by norm_num, by norm_num, by omega, ?_⟩
    rw [show jetP N p 7 (p - 1 - e.val - wd N p 6) = jetInf (wd N p 6 + (p - 1 - e.val - wd N p 6)) by simp [jetP]]
    exact jetInf_eq _ e (by omega)
  by_cases h8 : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8
  · refine ⟨8, p - 1 - e.val - (wd N p 6 + wd N p 7), by norm_num, by norm_num, by omega, ?_⟩
    rw [show jetP N p 8 (p - 1 - e.val - (wd N p 6 + wd N p 7)) =
      jetInf (wd N p 6 + wd N p 7 + (p - 1 - e.val - (wd N p 6 + wd N p 7))) by simp [jetP]]
    exact jetInf_eq _ e (by omega)
  by_cases h9 : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9
  · refine ⟨9, p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8), by norm_num, by norm_num, by omega, ?_⟩
    rw [show jetP N p 9 (p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8)) =
      jetInf (wd N p 6 + wd N p 7 + wd N p 8 + (p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8))) by simp [jetP]]
    exact jetInf_eq _ e (by omega)
  · refine ⟨10, p - 1 - e.val - (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9), by norm_num, le_refl _,
      by omega, ?_⟩
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

theorem jet6_eq (e : Fin p) :
    jetP N p 6 (p - 1 - e.val) = LinearMap.proj e := by
  simp only [jetP]; exact jetInf_eq _ e rfl

theorem cover_135 (hW : Win N p) (M : MonoData dsg N p 49) (hM : (pdB 11).Realises M.prof) :
    CoverPt3 pk M (insL p) (low135 p) (fun g => wNat g N p) (dsg.q N / p)
      (fun g k => jetP N p g.val k.val) := by
  have hN := hW.1; have h69 := hW.2.1; have h16 := hW.2.2.1; have hodd := hW.2.2.2
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
  have hJ14 : J < 14 := by
    by_contra h; push_neg at h
    have := Nat.mul_le_mul_left p h; omega
  have hs15 : s ≤ 14 := by
    by_contra h; push_neg at h
    have := Int.mul_le_mul_of_nonneg_left (show (15:ℤ) ≤ s by omega) hpz
    omega
  have hs13 : 13 ≤ s := by
    by_contra h; push_neg at h
    have := Int.mul_le_mul_of_nonneg_left (show s ≤ 12 by omega) hpz
    omega
  have fin : ∀ (S : ℤ) (y : Fin pk.d → Fp),
      M.sys.prof.psi (dsg.H N) (J) S (insL p (emb pk p 37 y)) = emb pk p 37 y 34 →
      ∑ v ∈ range (0 + 1), ((-1 : ZMod p) ^ (0 - v) * ((Nat.choose 0 v : ℕ) : ZMod p)) *
        M.sys.prof.psi (dsg.H N) (J + v) S (insL p (emb pk p 37 y)) = low135 p y := by
    intro S y h; simp [low135_apply, h]
  have hden : ((dsg.H N : ℤ) - 1 - ((l : ℕ) : ℤ) - (e : ℕ)) / (p : ℤ) = s := by
    rw [hs0, Int.mul_ediv_cancel_left _ hpne]
  have hs1314 : s = 13 ∨ s = 14 := by omega
  rcases hs1314 with h13 | h14
  · -- S = 13 : the position is seen through group 6
    subst h13
    have hel : wd N p 1 ≤ e.val := by omega
    have hm6 : p - 1 - e.val < wd N p 6 := by omega
    have hJ1 : 1 ≤ J := by
      by_contra h
      have h0 : J = 0 := by omega
      rw [h0] at hjl; omega
    have hJ12 : J ≤ 12 := by
      by_contra h
      have h13 : J = 13 := by omega
      rw [h13] at hjl; omega
    by_cases hJ1' : J = 1
    · subst hJ1'
      have hew2 : e.val - wd N p 1 < wd N p 2 := by omega
      refine ⟨⟨2, by rw [pk_len]; norm_num⟩, ⟨e.val - wd N p 1, lt_wNat _ (by norm_num) hew2⟩,
        ⟨6, by rw [pk_len]; norm_num⟩, ⟨p - 1 - e.val, lt_wNat _ (by norm_num) hm6⟩,
        jet2_eq e hel, jet6_eq e, ?_⟩
      intro y hy hy'
      rw [hden]
      apply fin
      rw [cover_row M hM hp13 (g := 2) (i := 0) (J := 1) (S := 13) (ε13 := 0) (ε1 := 1) (by norm_num)
        rows_graph1.2 (by norm_num) (by norm_num) (by rw [hH]; omega) y hy,
        chart_unit 36 6 (by norm_num) inf_low1 y hy']
      simp
    · have hJ2 : 2 ≤ J := by omega
      refine ⟨⟨6, by rw [pk_len]; norm_num⟩, ⟨p - 1 - e.val, lt_wNat _ (by norm_num) hm6⟩,
        ⟨6, by rw [pk_len]; norm_num⟩, ⟨p - 1 - e.val, lt_wNat _ (by norm_num) hm6⟩,
        jet6_eq e, jet6_eq e, ?_⟩
      intro y hy _
      rw [hden]
      apply fin
      have hok := rows_inf ⟨J - 2, by omega⟩
      simp only [show J - 2 + 1 = J - 1 by omega, show J - 2 + 2 = J by omega] at hok
      rw [cover_row M hM hp13 (g := 6) (i := J - 1) (J := J) (S := 13) (ε13 := 0) (ε1 := 0) (by norm_num)
        hok (by omega) (by norm_num) (by rw [hH]; omega) y hy]
      simp
  · -- S = 14 : group 1, rows raw[J,0]
    subst h14
    have hew : e.val < wd N p 1 := by omega
    have hJ2 : 2 ≤ J := by
      by_contra h
      have : J = 0 ∨ J = 1 := by omega
      rcases this with rfl | rfl <;> omega
    by_cases hJ13 : J = 13
    · have hel2 : 8 * N - p ≤ e.val := by rw [hJ13] at hjl; omega
      have hm5 : p - 1 - e.val < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10 := by omega
      obtain ⟨g', k', hg6, hg10, hk', hjet'⟩ := inf_group hW e hm5
      have hrow' : hasRow g' (unitL 35) = true := by
        obtain ⟨r6, r7, r8, r9, r10⟩ := inf_low13
        interval_cases g' <;> assumption
      refine ⟨⟨1, by rw [pk_len]; norm_num⟩, ⟨e.val, lt_wNat _ (by norm_num) hew⟩,
        ⟨g', by rw [pk_len]; omega⟩, ⟨k', lt_wNat _ (by omega) hk'⟩,
        jet1_eq e hew, jetS_eq e g' k' (by omega) hk' hjet', ?_⟩
      intro y hy hy'
      rw [hden]
      apply fin
      rw [hJ13]
      rw [cover_row M hM hp13 (g := 1) (i := 11) (J := 13) (S := 14) (ε13 := 1) (ε1 := 0) (by norm_num)
        rows_graph13 (by norm_num) (by norm_num) (by rw [hH]; omega) y hy,
        chart_unit 35 g' (by omega) hrow' y hy']
      simp
    · have hJ12 : J ≤ 12 := by omega
      refine ⟨⟨1, by rw [pk_len]; norm_num⟩, ⟨e.val, lt_wNat _ (by norm_num) hew⟩,
        ⟨1, by rw [pk_len]; norm_num⟩, ⟨e.val, lt_wNat _ (by norm_num) hew⟩,
        jet1_eq e hew, jet1_eq e hew, ?_⟩
      intro y hy _
      rw [hden]
      apply fin
      have hok := rows_zero ⟨J - 2, by omega⟩
      simp only [show J - 2 + 2 = J by omega] at hok
      rw [cover_row M hM hp13 (g := 1) (i := J - 2) (J := J) (S := 14) (ε13 := 0) (ε1 := 0) (by norm_num)
        hok (by omega) (by norm_num) (by rw [hH]; omega) y hy]
      simp

end
end Part1

section Part2
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Charts CatalanMeasure.GenD.Uniform.W.Charts5 Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section

theorem cNat_eq {N p : ℕ} (hp2 : p % 2 = 1) : cNat N p = p := by
  simp only [cNat, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.cNat]
  omega

theorem ck_ok : ∀ k : Fin (11 * 4 + 2 + 3), ckEquiv (rfl : 11 * 4 + 2 + 3 = 11 * 4 + 2 + 3) k = ckOfB 11 3 k := by
  decide +kernel

theorem monoProfile_realises135 {N p : ℕ} [Fact p.Prime] (hW : Win N p) {K : ℕ}
    (hK : K = bN dsg N p * 4 + 2 + 3) : (pdB 11).Realises (monoProfile dsg N p hK) := by
  have h0 := realises_absB (p := p) (b0 := 11) (ex := 3) (geom_bN hW) hK ck_ok
  have e1 : k0N dsg N p = -1 := geom_k0 hW
  have e2 : dsg.h N / p = 0 := geom_hdiv hW
  unfold monoProfile
  rw [e1, e2]
  exact h0

/-- **The physical host of the L0135 packet.** -/
theorem physHost_135 : CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.Phys := by
  intro N p hN hp hp2 hH hApp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, hpD⟩ := hApp
  have hn : 1 ≤ dsg.n N := by rw [Pilot146O.design_n]; have := hW.1; omega
  have hK' : 49 = bN dsg N p * 4 + 2 + 3 := hKp hW
  let M : MonoData dsg N p 49 := monoData hp2 hn hK'
  have hM : (pdB 11).Realises M.prof := monoProfile_realises135 hW hK'
  have hc : CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.cNat N p = p := cNat_eq hW.2.2.2
  rw [hc]
  refine ⟨M.sys, ⟨?_⟩⟩
  exact monoHost3 (width := fun g => wNat g N p) M (insL p) ((projExtras hK').comp (insL p))
    (fun y => sumProf_proj hK' _ (fun j => rfl) (insL p y))
    (fun y => sumProf_proj hK' _ (fun j => rfl) (insL p y))
    (low135 p) (dsg.q N / p) (dsg.q N % p) (fun g k => jetP N p g.val k.val)
    (fun x hker hproj => hinj_135 hW hpD x hker hproj)
    (fun x hker => by
      obtain ⟨c, hc⟩ := hdom_135 hW hp2 hn x hker
      exact ⟨c, hc⟩)
    (fun x hker => hG_135 hW x hker)
    (cover_135 hW M hM)

end
end Part2

section Part3
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

theorem win_L0135 :
    WinCert (NullityLB.ofPacketHost D58.Odd.design_admissible
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.pk
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.pk_sound
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.Win
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.cNat
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wNat physHost_135)
      (cw (69 / 13 : ℝ) (16 / 3 : ℝ) (11 : ℝ) (-2 : ℝ)) :=
  CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.win0 D58.Odd.design_admissible physHost_135

end
end Part3

end CatalanMeasure.GenD.Uniform.W.Charts6.L0135

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.hdom_135
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.hG_135
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.hinj_135
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.rows_zero
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.rows_graph13
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.rows_graph1
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.rows_inf
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.psi_row
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.cover_135
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.physHost_135
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0135.win_L0135
