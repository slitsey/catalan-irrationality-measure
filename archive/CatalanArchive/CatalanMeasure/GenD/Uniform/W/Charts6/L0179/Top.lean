module
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0179.Core
public import CatalanMeasure.GenD.Uniform.W.Charts5.Prof146
public import CatalanMeasure.GenD.Uniform.W.Charts6.ProfB
public import CatalanMeasure.GenD.Uniform.W.Charts6.Unit13
public import CatalanMeasure.GenD.Uniform.W.Charts6.MonoHost3
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Uniform.W.Charts6.L0179
section PartPsi
open Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts5
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap)
noncomputable section

/-- The moment denominator used for the rows. -/
abbrev ZM : ℕ := Zmom 10 7

def rowOK (g i J : ℕ) (S : ℤ) (ε : ℤ) : Bool :=
  let r := (oRows g).getD i []
  decide (i < (oRows g).length) && decide (r.getD 26 0 < 0) &&
    decide ((30030 ^ 40 : ℤ) % (r.getD 26 0) = 0) &&
    decide (r.getD 27 0 = ε * r.getD 26 0) &&
    (List.range 26).all (fun c => decide (r.getD c 0 * (ZM : ℤ) = -(r.getD 26 0) * rowInt (pdB 6) ZM J S c)) &&
    decide (rowInt (pdB 6) ZM J S 26 = 0) && decide (rowInt (pdB 6) ZM J S 27 = 0)

/-- Row index of the `raw[J,1].degree` row (`J = 1..5`) in the `∞` group `g = 7..11`. -/
def ridx (g J : ℕ) : ℕ := match g with | 7 => J + 16 | 8 => J + 14 | 9 => J + 7 | 10 => J + 1 | _ => J

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
theorem rows_zero : ∀ J : Fin 6, rowOK 1 J.val (J.val + 1) 7 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rows_graph : rowOK 1 6 0 6 1 = true ∧ rowOK 2 0 0 6 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rows_inf : ∀ g : Fin 5, ∀ J : Fin 5,
    rowOK (g.val + 7) (ridx (g.val + 7) (J.val + 1)) (J.val + 1) 6 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rows_six : rowOK 7 1 6 6 0 = true := by decide +kernel

end
end PartPsi
section Part0
open Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts5
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap)
noncomputable section

theorem psi_row {p : ℕ} [Fact p.Prime] (hp : 13 < p) (F : Prof p 28) (hF : (pdB 6).Realises F)
    {g i J : ℕ} {S : ℤ} {ε : ℤ} {H : ℕ}
    (hok : rowOK g i J S ε = true) (hJ : J < 7) (hS : S.toNat + 3 ≤ 10) (hH : S.toNat + 3 ≤ H)
    (y : Fin 28 → ZMod p)
    (hy : ∑ c : Fin 28, ((((oRows g).getD i []).getD c 0 : ℤ) : ZMod p) * y c = 0) :
    F.psi H J S y = y 26 + (ε : ZMod p) * y 27 := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨hi, hneg⟩, hdvd⟩, hε⟩, hall⟩, h42⟩, h43⟩ := hok
  set r := (oRows g).getD i [] with hr
  have hZp : ¬ p ∣ ZM := not_dvd_ZM hp
  have hZ : ((ZM : ℕ) : ZMod p) ≠ 0 := fun h => hZp ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hD : ((r.getD 26 0 : ℤ) : ZMod p) ≠ 0 :=
    CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ (Int.dvd_of_emod_eq_zero hdvd) (by omega)
  have hm : ∀ c : Fin 28, ((rowInt (pdB 6) ZM J S c : ℤ) : ZMod p) = (ZM : ZMod p) * F.psi H J S (Pi.single c 1) :=
    fun c => rowInt_mod (Ub := 10) (Jb := 7) hZp (pdB 6) F hF c hJ hS hH
  have hpsi0 : ∀ c : Fin 28, 26 ≤ c.val → F.psi H J S (Pi.single c 1) = 0 := by
    intro c hc
    have : c.val = 26 ∨ c.val = 27 := by omega
    have h0 : rowInt (pdB 6) ZM J S c = 0 := by
      rcases this with h | h
      · rw [h]; exact h42
      · rw [h]; exact h43
    have := hm c
    rw [h0] at this
    simp only [Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hZ
  have hrow : ∀ c : Fin 28, c.val < 26 →
      ((r.getD c 0 : ℤ) : ZMod p) = -((r.getD 26 0 : ℤ) : ZMod p) * F.psi H J S (Pi.single c 1) := by
    intro c hc
    have e := hall c.val hc
    have e' := congrArg (fun z : ℤ => (z : ZMod p)) e
    simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast] at e'
    rw [hm c] at e'
    apply mul_right_cancel₀ hZ
    simp only [ZM] at e' ⊢
    linear_combination e'
  have hcoef : ∀ c : Fin 28, ((r.getD c 0 : ℤ) : ZMod p) =
      -((r.getD 26 0 : ℤ) : ZMod p) * F.psi H J S (Pi.single c 1) +
        (if c = 26 then ((r.getD 26 0 : ℤ) : ZMod p) else 0) +
        (if c = 27 then ((r.getD 27 0 : ℤ) : ZMod p) else 0) := by
    intro c
    by_cases hc : c.val < 26
    · have h1 : c ≠ 26 := fun h => by rw [h] at hc; simp at hc
      have h2 : c ≠ 27 := fun h => by rw [h] at hc; simp at hc
      rw [if_neg h1, if_neg h2, hrow c hc]; ring
    · rw [hpsi0 c (by omega)]
      by_cases h1 : c = 26
      · subst h1; simp
      · have h2 : c = 27 := by
          have : c.val = 27 := by
            have := c.isLt
            have h1' : c.val ≠ 26 := fun h => h1 (Fin.ext h)
            omega
          exact Fin.ext this
        subst h2; simp
  have hlin : F.psi H J S y = ∑ c : Fin 28, y c * F.psi H J S (Pi.single c 1) := by
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ (F.psi H J S) y]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_eq_mul]
    congr 2
    funext j
    by_cases h : j = c
    · subst h; simp [Pi.single_apply]
    · simp [Pi.single_apply, h, Ne.symm h]
  have hsum : ∑ c : Fin 28, ((r.getD c 0 : ℤ) : ZMod p) * y c =
      -((r.getD 26 0 : ℤ) : ZMod p) * F.psi H J S y + ((r.getD 26 0 : ℤ) : ZMod p) * y 26 +
        ((r.getD 27 0 : ℤ) : ZMod p) * y 27 := by
    have h1 : ∀ c : Fin 28, ((r.getD c 0 : ℤ) : ZMod p) * y c =
        -((r.getD 26 0 : ℤ) : ZMod p) * (y c * F.psi H J S (Pi.single c 1)) +
          (if c = 26 then ((r.getD 26 0 : ℤ) : ZMod p) * y c else 0) +
          (if c = 27 then ((r.getD 27 0 : ℤ) : ZMod p) * y c else 0) := by
      intro c; rw [hcoef c]; split_ifs <;> ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hlin]
    simp
  rw [hsum, hε] at hy
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

theorem chart_row_sum (g i : ℕ) (hg : g < 12) (hi : i < (oRows g).length)
    (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, by rw [pk_len]; exact hg⟩) p 28 y = 0) :
    ∑ c : Fin 28, ((((oRows g).getD i []).getD c 0 : ℤ) : Fp) * emb pk p 28 y c = 0 := by
  have hrows := chart_rows (⟨g, by rw [pk_len]; exact hg⟩ : Fin pk.charts.length)
  have hi' : i < (pk.chart ⟨g, by rw [pk_len]; exact hg⟩).rows.length := by
    rw [hrows]; exact hi
  have := row_of_chart (K := 28) _ hy i hi'
  convert this using 2
  rw [Mx, hrows]

theorem rowOK_lt {g i J : ℕ} {S ε : ℤ} (h : rowOK g i J S ε = true) : i < (oRows g).length := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1

theorem chart_unit (c : Fin 28) (g : ℕ) (hg : g < 12) (h : hasRow g (unitL c) = true) (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, by rw [pk_len]; exact hg⟩) p 28 y = 0) :
    emb pk p 28 y c = 0 := by
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp (List.contains_iff_mem.mp h)
  have := chart_row_sum g i hg hi y hy
  rw [List.getD_eq_getElem _ _ hi, hir] at this
  exact (sum_unitL c (emb pk p 28 y)).symm.trans this

/-- A seen covector read off one stored row. -/
theorem cover_row (M : MonoData dsg N p 28) (hM : (pdB 6).Realises M.prof) (hp : 13 < p)
    {g i J : ℕ} {S ε : ℤ} (hg : g < 12) (hok : rowOK g i J S ε = true) (hJ : J < 7)
    (hS : S.toNat + 3 ≤ 10) (hH : S.toNat + 3 ≤ dsg.H N) (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, by rw [pk_len]; exact hg⟩) p 28 y = 0) :
    M.sys.prof.psi (dsg.H N) J S (insL p (emb pk p 28 y)) =
      emb pk p 28 y 26 + (ε : Fp) * emb pk p 28 y 27 :=
  psi_row hp M.prof hM hok hJ hS hH (emb pk p 28 y) (chart_row_sum g i hg (rowOK_lt hok) y hy)

theorem rows_inf' (g J : ℕ) (hg7 : 7 ≤ g) (hg11 : g ≤ 11) (hJ1 : 1 ≤ J) (hJ5 : J ≤ 5) :
    rowOK g (ridx g J) J 6 0 = true := by
  have := rows_inf ⟨g - 7, by omega⟩ ⟨J - 1, by omega⟩
  simp only [Fin.val_mk] at this
  have e1 : g - 7 + 7 = g := by omega
  have e2 : J - 1 + 1 = J := by omega
  rw [e1, e2] at this
  exact this

theorem lt_wNat {k : ℕ} (g : ℕ) (hg : g < 12) (hk : k < wd N p g) :
    k < wNat (⟨g, by rw [pk_len]; exact hg⟩ : Fin pk.charts.length) N p := hk

theorem jetS_eq (e : Fin p) (g k : ℕ) (hg : g < 12) (hk : k < wd N p g)
    (h : jetP N p g k = LinearMap.proj e) :
    (fun (g : Fin pk.charts.length) (k : Fin (wNat g N p)) => jetP N p g.val k.val)
      ⟨g, by rw [pk_len]; exact hg⟩ ⟨k, lt_wNat _ hg hk⟩ = LinearMap.proj e := h

theorem jet1_eq (e : Fin p) (he : e.val < wd N p 1) :
    jetP N p 1 e.val = LinearMap.proj e := by
  simp only [jetP]; exact jet0_eq _ e rfl

theorem jet2_eq (e : Fin p) (he : wd N p 1 ≤ e.val) :
    jetP N p 2 (e.val - wd N p 1) = LinearMap.proj e := by
  simp only [jetP]; exact jet0_eq _ e (by omega)

theorem proj_of_inf (e : Fin p) (g k : ℕ) (h : jetP N p g k = jetInf (p - 1 - e.val)) :
    jetP N p g k = LinearMap.proj e := by
  rw [h]; exact jetInf_eq _ e rfl

theorem cover_179 (hW : Win N p) (M : MonoData dsg N p 28) (hM : (pdB 6).Realises M.prof) :
    CoverPt3 pk M (insL p) (low179 p) (fun g => wNat g N p) (dsg.q N / p)
      (fun g k => jetP N p g.val k.val) := by
  have hN := hW.1; have h11 := hW.2.1; have h78 := hW.2.2.1; have hodd := hW.2.2.2
  have hp13 : 13 < p := by omega
  have hq0 : dsg.q N / p = 0 := geom_qdiv hW
  have hH : dsg.H N = 78 * N := design_H N
  have w1 := wd1 hW; have w2 := wd2 hW; have w7 := wd7 hW; have w8 := wd8 hW; have w9 := wd9 hW
  have w10 := wd10 hW; have w11 := wd11 hW
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
  have hJ7 : J < 7 := by
    by_contra h; push_neg at h
    have := Nat.mul_le_mul_left p h; omega
  have hs8 : s ≤ 7 := by
    by_contra h; push_neg at h
    have := Int.mul_le_mul_of_nonneg_left (show (8:ℤ) ≤ s by omega) hpz
    omega
  have hs5 : 6 ≤ s := by
    by_contra h; push_neg at h
    have := Int.mul_le_mul_of_nonneg_left (show s ≤ 5 by omega) hpz
    omega
  have fin : ∀ (S : ℤ) (y : Fin pk.d → Fp),
      M.sys.prof.psi (dsg.H N) (J) S (insL p (emb pk p 28 y)) = emb pk p 28 y 26 →
      ∑ v ∈ range (0 + 1), ((-1 : ZMod p) ^ (0 - v) * ((Nat.choose 0 v : ℕ) : ZMod p)) *
        M.sys.prof.psi (dsg.H N) (J + v) S (insL p (emb pk p 28 y)) = low179 p y := by
    intro S y h; simp [low179_apply, h]
  have hden : ((dsg.H N : ℤ) - 1 - ((l : ℕ) : ℤ) - (e : ℕ)) / (p : ℤ) = s := by
    rw [hs0, Int.mul_ediv_cancel_left _ hpne]
  have hs67 : s = 6 ∨ s = 7 := by omega
  rcases hs67 with h6 | h7
  · -- S = 6 : the position is seen through the infinite groups
    subst h6
    have hel : wd N p 1 ≤ e.val := by omega
    have hm5 : p - 1 - e.val < wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10 + wd N p 11 := by omega
    obtain ⟨g', k', hg7, hg11, hk', hjet', hg7'⟩ := inf_group hW e hm5
    have hjetp := proj_of_inf e g' k' hjet'
    have hrow' : hasRow g' (unitL 27) = true := by
      obtain ⟨r7, r8, r9, r10, r11⟩ := inf_low
      interval_cases g' <;> assumption
    by_cases hJ0 : J = 0
    · -- the graph row of group 2 and the slack row
      subst hJ0
      have hew2 : e.val - wd N p 1 < wd N p 2 := by omega
      refine ⟨⟨2, by rw [pk_len]; norm_num⟩, ⟨e.val - wd N p 1, lt_wNat _ (by norm_num) hew2⟩,
        ⟨g', by rw [pk_len]; omega⟩, ⟨k', lt_wNat _ (by omega) hk'⟩,
        jet2_eq e hel, jetS_eq e g' k' (by omega) hk' hjetp, ?_⟩
      intro y hy hy'
      rw [hden]
      apply fin
      rw [cover_row M hM hp13 (g := 2) (i := 0) (J := 0) (S := 6) (ε := 1) (by norm_num)
        rows_graph.2 (by norm_num) (by norm_num) (by rw [hH]; omega) y hy,
        chart_unit 27 g' (by omega) hrow' y hy']
      simp
    · have hJ1 : 1 ≤ J := by omega
      by_cases hJ6 : J = 6
      · have hel2 : 8 * N ≤ e.val := by rw [hJ6] at hjl; omega
        have hm7 : p - 1 - e.val < wd N p 7 := by omega
        have hg7e := hg7' hm7
        subst hg7e
        refine ⟨⟨7, by rw [pk_len]; norm_num⟩, ⟨k', lt_wNat _ (by norm_num) hk'⟩,
          ⟨7, by rw [pk_len]; norm_num⟩, ⟨k', lt_wNat _ (by norm_num) hk'⟩,
          jetS_eq e 7 k' (by norm_num) hk' hjetp, jetS_eq e 7 k' (by norm_num) hk' hjetp, ?_⟩
        intro y hy _
        rw [hden]
        apply fin
        rw [hJ6]
        rw [cover_row M hM hp13 (g := 7) (i := 1) (J := 6) (S := 6) (ε := 0) (by norm_num)
          rows_six (by norm_num) (by norm_num) (by rw [hH]; omega) y hy]
        simp
      · have hJ5 : J ≤ 5 := by omega
        refine ⟨⟨g', by rw [pk_len]; omega⟩, ⟨k', lt_wNat _ (by omega) hk'⟩,
          ⟨g', by rw [pk_len]; omega⟩, ⟨k', lt_wNat _ (by omega) hk'⟩,
          jetS_eq e g' k' (by omega) hk' hjetp, jetS_eq e g' k' (by omega) hk' hjetp, ?_⟩
        intro y hy _
        rw [hden]
        apply fin
        have hok := rows_inf' g' J hg7 hg11 hJ1 hJ5
        have := cover_row M hM hp13 (g := g') (i := ridx g' J) (J := J) (S := 6) (ε := 0) (by omega)
          hok (by omega) (by norm_num) (by rw [hH]; omega) y hy
        rw [this]; simp
  · -- S = 7 : group 1, row raw[J,0].prefix
    subst h7
    have hew : e.val < wd N p 1 := by omega
    have hJ1 : 1 ≤ J := by
      by_contra h
      have h0 : J = 0 := by omega
      rw [h0] at hjl; omega
    refine ⟨⟨1, by rw [pk_len]; norm_num⟩, ⟨e.val, lt_wNat _ (by norm_num) hew⟩,
      ⟨1, by rw [pk_len]; norm_num⟩, ⟨e.val, lt_wNat _ (by norm_num) hew⟩,
      jet1_eq e hew, jet1_eq e hew, ?_⟩
    intro y hy _
    rw [hden]
    apply fin
    have hok := rows_zero ⟨J - 1, by omega⟩
    simp only [show J - 1 + 1 = J by omega] at hok
    rw [cover_row M hM hp13 (g := 1) (i := J - 1) (J := J) (S := 7) (ε := 0) (by norm_num)
      hok hJ7 (by norm_num) (by rw [hH]; omega) y hy]
    simp

end
end Part1

section Part2
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Charts CatalanMeasure.GenD.Uniform.W.Charts5 Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section

theorem cNat_eq {N p : ℕ} (hp2 : p % 2 = 1) : cNat N p = p := by
  simp only [cNat, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.cNat]
  omega

theorem ck_ok : ∀ k : Fin (6 * 4 + 2 + 2), ckEquiv (rfl : 6 * 4 + 2 + 2 = 6 * 4 + 2 + 2) k = ckOfB 6 2 k := by
  decide +kernel

theorem monoProfile_realises179 {N p : ℕ} [Fact p.Prime] (hW : Win N p) {K : ℕ}
    (hK : K = bN dsg N p * 4 + 2 + 2) : (pdB 6).Realises (monoProfile dsg N p hK) := by
  have h0 := realises_absB (p := p) (b0 := 6) (ex := 2) (geom_bN hW) hK ck_ok
  have e1 : k0N dsg N p = -1 := geom_k0 hW
  have e2 : dsg.h N / p = 0 := geom_hdiv hW
  unfold monoProfile
  rw [e1, e2]
  exact h0

/-- **The physical host of the L0179 packet.** -/
theorem physHost_179 : CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.Phys := by
  intro N p hN hp hp2 hH hApp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, hpD⟩ := hApp
  have hn : 1 ≤ dsg.n N := by rw [Pilot146O.design_n]; have := hW.1; omega
  have hK' : 28 = bN dsg N p * 4 + 2 + 2 := hKp hW
  let M : MonoData dsg N p 28 := monoData hp2 hn hK'
  have hM : (pdB 6).Realises M.prof := monoProfile_realises179 hW hK'
  have hc : CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.cNat N p = p := cNat_eq hW.2.2.2
  rw [hc]
  refine ⟨M.sys, ⟨?_⟩⟩
  exact monoHost3 (width := fun g => wNat g N p) M (insL p) ((projExtras hK').comp (insL p))
    (fun y => sumProf_proj hK' _ (fun j => rfl) (insL p y))
    (fun y => sumProf_proj hK' _ (fun j => rfl) (insL p y))
    (low179 p) (dsg.q N / p) (dsg.q N % p) (fun g k => jetP N p g.val k.val)
    (fun x hker hproj => hinj_179 hW hpD x hker hproj)
    (fun x hker => by
      obtain ⟨c, hc⟩ := hdom_179 hW hp2 hn x hker
      exact ⟨c, hc⟩)
    (fun x hker => hG_179 hW x hker)
    (cover_179 hW M hM)

end
end Part2

section Part3
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

theorem win_L0179 :
    WinCert (NullityLB.ofPacketHost D58.Odd.design_admissible
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.pk
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.pk_sound
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.Win
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.cNat
      CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wNat physHost_179)
      (cw (11 : ℝ) (78 / 7 : ℝ) (-11 : ℝ) (1 : ℝ)) :=
  CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.win0 D58.Odd.design_admissible physHost_179

end
end Part3

end CatalanMeasure.GenD.Uniform.W.Charts6.L0179

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.hdom_179
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.hG_179
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.hinj_179
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.rows_zero
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.rows_graph
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.rows_inf
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.rows_six
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.psi_row
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.cover_179
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.physHost_179
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.L0179.win_L0179
