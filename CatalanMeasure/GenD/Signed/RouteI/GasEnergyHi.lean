module

public import CatalanMeasure.GenD.Signed.RouteI.GasEnergyCert

@[expose] public section


/-!
# The upper bound `hi` on the intercept and gas constants of `capSource`
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

noncomputable section

theorem mul1 {x y a b e f g : ℝ} (hx : |x - a| ≤ e) (hy : |y - b| ≤ f) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hg : e + f + e * f ≤ g) : |x * y - a * b| ≤ g := by
  have e0 : 0 ≤ e := (abs_nonneg _).trans hx
  have f0 : 0 ≤ f := (abs_nonneg _).trans hy
  have m := mul_box hx hy
  have m1 : e * |b| ≤ e := by nlinarith [abs_nonneg b]
  have m2 : |a| * f ≤ f := by nlinarith [abs_nonneg a]
  linarith

theorem hi_alg {EPP ENN EPN ECC EPD END p m Ap An L2 t Lp Ln RP RN Rf uP uN sP sN aL LP LM tau
      κp κn : ℝ}
    (k1 : κp = 14762657 / 100000000) (k2 : κn = 5463909 / 100000000)
    (hPP : |EPP - (-38127071179348) / 10 ^ 14| ≤ 1 / 10 ^ 7)
    (hNN : |ENN - (-5279775549395) / 10 ^ 14| ≤ 1 / 10 ^ 7)
    (hCC : |ECC - (-147373193052358) / 10 ^ 14| ≤ 1 / 10 ^ 7)
    (hPN : |EPN - 40455650519392 / 10 ^ 14| ≤ 1 / 10 ^ 7)
    (hPD : |EPD - (-5925935229269) / 10 ^ 14| ≤ 1 / 10 ^ 7)
    (hND : |END - 51466727869246 / 10 ^ 14| ≤ 1 / 10 ^ 7)
    (hp : |p - 63489562168082 / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hm : |m - 36510437831917 / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hAp : |Ap - 36510437831917 / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hAn : |An - 54868872512909 / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hL2 : |L2 - 69314718055994 / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (ht : |t - 788755782 / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hLp : |Lp - (-39541675682036) / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hLn : |Ln - (-29512640381580) / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hRP : |RP - (-853339519085) / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hRN : |RN - (-1357201154220) / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hRf : 23239004899126 / 10 ^ 14 - 1 / 10 ^ 9 ≤ Rf)
    (huP : |uP - (-3944317782559) / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (huN : |uN - (-5869925662132) / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hsP : |sP - 6880564215755 / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hsN : |sN - 43657136919364 / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (haL : |aL - (-53351287497253) / 10 ^ 14| ≤ 1 / 10 ^ 9)
    (hτ : 14253339 / 10000 ≤ tau)
    (hLP : EPP + 2 * p * Lp + Rf + (-sP - Ap * Ap * t + uP) + 2 * (RP - p * (Ap * t)) ≤ LP)
    (hLM : ENN - m ^ 2 * L2 + (sN - An * An * (L2 + 2 * t) + uN) +
      2 * (RN - m * (An * (t * 2)) - An * (m * L2 + Ln) - m * aL) ≤ LM) :
    -((EPP + ENN + 2 * EPN) / 2 + ECC - (EPD + END)) +
      (κp + 53 / 58 * (κn - (Ln + aL)) - (53 / 58) ^ 2 / 2 * L2 - (LP + LM) / 2 -
        tau / (2 * 58 ^ 2)) ≤ 2366997 / 1000000 := by
  have u : ∀ {a : ℝ}, -1 ≤ a → a ≤ 1 → |a| ≤ 1 := fun h1 h2 => abs_le.mpr ⟨h1, h2⟩
  have b1 := mul1 (g := 1 / 10 ^ 8) hp hLp (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b2 := mul1 (g := 1 / 10 ^ 8) hAp hAp (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b3 := mul1 (g := 1 / 10 ^ 7) b2 ht (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b4 := mul1 (g := 1 / 10 ^ 8) hAp ht (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b5 := mul1 (g := 1 / 10 ^ 7) hp b4 (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b6 := mul1 (g := 1 / 10 ^ 8) hm hm (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b7 := mul1 (g := 1 / 10 ^ 7) b6 hL2 (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b8 := mul1 (g := 1 / 10 ^ 8) hAn hAn (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b9 := mul1 (g := 1 / 10 ^ 7) b8 hL2 (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b10 := mul1 (g := 1 / 10 ^ 7) b8 ht (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b11 := mul1 (g := 1 / 10 ^ 8) hAn ht (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b12 := mul1 (g := 1 / 10 ^ 7) hm b11 (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b13 := mul1 (g := 1 / 10 ^ 8) hm hL2 (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b14 := mul1 (g := 1 / 10 ^ 7) hAn b13 (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b15 := mul1 (g := 1 / 10 ^ 8) hAn hLn (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  have b16 := mul1 (g := 1 / 10 ^ 8) hm haL (u (by norm_num) (by norm_num)) (u (by norm_num) (by norm_num)) (by norm_num)
  obtain ⟨c1, d1⟩ := abs_le.mp b1
  obtain ⟨c3, d3⟩ := abs_le.mp b3
  obtain ⟨c5, d5⟩ := abs_le.mp b5
  obtain ⟨c7, d7⟩ := abs_le.mp b7
  obtain ⟨c9, d9⟩ := abs_le.mp b9
  obtain ⟨c10, d10⟩ := abs_le.mp b10
  obtain ⟨c12, d12⟩ := abs_le.mp b12
  obtain ⟨c14, d14⟩ := abs_le.mp b14
  obtain ⟨c15, d15⟩ := abs_le.mp b15
  obtain ⟨c16, d16⟩ := abs_le.mp b16
  obtain ⟨e1, f1⟩ := abs_le.mp hPP
  obtain ⟨e2, f2⟩ := abs_le.mp hNN
  obtain ⟨e3, f3⟩ := abs_le.mp hCC
  obtain ⟨e4, f4⟩ := abs_le.mp hPN
  obtain ⟨e5, f5⟩ := abs_le.mp hPD
  obtain ⟨e6, f6⟩ := abs_le.mp hND
  obtain ⟨e7, f7⟩ := abs_le.mp hL2
  obtain ⟨e8, f8⟩ := abs_le.mp hLn
  obtain ⟨e9, f9⟩ := abs_le.mp hRP
  obtain ⟨e10, f10⟩ := abs_le.mp hRN
  obtain ⟨e11, f11⟩ := abs_le.mp huP
  obtain ⟨e12, f12⟩ := abs_le.mp huN
  obtain ⟨e13, f13⟩ := abs_le.mp hsP
  obtain ⟨e14, f14⟩ := abs_le.mp hsN
  obtain ⟨e15, f15⟩ := abs_le.mp haL
  subst k1 k2
  have q1 : m ^ 2 * L2 = m * m * L2 := by ring
  rw [q1] at hLM
  have r1 : An * (m * L2 + Ln) = An * (m * L2) + An * Ln := by ring
  have r2 : An * An * (L2 + 2 * t) = An * An * L2 + 2 * (An * An * t) := by ring
  have r3 : m * (An * (t * 2)) = 2 * (m * (An * t)) := by ring
  have r4 : 2 * p * Lp = 2 * (p * Lp) := by ring
  rw [r1, r2, r3] at hLM
  rw [r4] at hLP
  linarith

theorem cast_lit {x e r : ℝ} {c : ℤ} (h : |x - (c : ℝ) / 10 ^ 14| ≤ e) (hc : (c : ℝ) = r) :
    |x - r / 10 ^ 14| ≤ e := hc ▸ h

theorem len_P : (capSource.gas Sign.pos).length = 427 := by
  rw [gas_pos_eq, List.length_map]
  exact lens.1

theorem len_N : (capSource.gas Sign.neg).length = 277 := by
  rw [gas_neg_eq, List.length_map]
  exact lens.2.1

theorem len_C : (capSource.refCol 0).length = 628 := by
  rw [refCol0, List.length_map]
  exact lens.2.2

theorem len_D : (dilL (capSource.refCol 0)).length = 628 := by
  unfold dilL
  rw [List.length_map]
  exact len_C

theorem tvP : tvR (ptsOf LPq) ≤ 8175 * 2 ^ 72 := (tvOf_spec _).trans (by exact_mod_cast tv_bd.1)
theorem tvN : tvR (ptsOf LNq) ≤ 2069544 * 2 ^ 72 :=
  (tvOf_spec _).trans (by exact_mod_cast tv_bd.2.1)
theorem tvC : tvR (ptsOf LCq) ≤ 5402 * 2 ^ 72 :=
  (tvOf_spec _).trans (by exact_mod_cast tv_bd.2.2.1)
theorem tvD' : tvR (ptsOf LDq) ≤ 5402 * 2 ^ 72 :=
  (tvOf_spec _).trans (by exact_mod_cast tv_bd.2.2.2)

theorem E_PP : |energy gP gP - (-38127071179348) / 10 ^ 14| ≤ 1 / 10 ^ 7 := by
  have h := pair_link c1 (by norm_num) rep_P (one_rep rep_P) gas_end_pos gas_end_pos (r := rPP)
    (encl_sym ptsPos) (q := qZ ptsPos ptsPos) rfl box_PP tvP tvP
  rw [len_P] at h
  refine (cast_lit h (by norm_num)).trans ?_
  norm_num [linkC, kap]

theorem E_NN : |energy gN gN - (-5279775549395) / 10 ^ 14| ≤ 1 / 10 ^ 7 := by
  have h := pair_link c1 (by norm_num) rep_N (one_rep rep_N) gas_end_neg gas_end_neg (r := rNN)
    (encl_sym ptsNeg) (q := qZ ptsNeg ptsNeg) rfl box_NN tvN tvN
  rw [len_N] at h
  refine (cast_lit h (by norm_num)).trans ?_
  norm_num [linkC, kap]

theorem E_CC : |energy cC cC - (-147373193052358) / 10 ^ 14| ≤ 1 / 10 ^ 7 := by
  have h := pair_link c1 (by norm_num) rep_C (one_rep rep_C) colE colE (r := rCC)
    (encl_sym ptsC) (q := qZ ptsC ptsC) rfl box_CC tvC tvC
  rw [len_C] at h
  refine (cast_lit h (by norm_num)).trans ?_
  norm_num [linkC, kap]

theorem E_PN : |energy gP gN - 40455650519392 / 10 ^ 14| ≤ 1 / 10 ^ 7 := by
  have h := pair_link c1 (by norm_num) rep_P (one_rep rep_N) gas_end_pos gas_end_neg (r := rPN)
    (encl_chk ptsPos ptsNeg) (q := qZ ptsPos ptsNeg) rfl box_PN tvP tvN
  rw [len_P, len_N] at h
  refine (cast_lit h (by norm_num)).trans ?_
  norm_num [linkC, kap]

theorem E_PD : |energy gP dC - (-5925935229269) / 10 ^ 14| ≤ 1 / 10 ^ 7 := by
  have h := pair_link c2 (by norm_num) rep_P (half_rep rep_D) gas_end_pos dilE (r := rPD)
    (encl_chk ptsPos ptsDl) (q := qZ ptsPos ptsDl) rfl box_PD tvP tvD'
  rw [len_P, len_D] at h
  refine (cast_lit h (by norm_num)).trans ?_
  norm_num [linkC, kap]

theorem E_ND : |energy gN dC - 51466727869246 / 10 ^ 14| ≤ 1 / 10 ^ 7 := by
  have h := pair_link c2 (by norm_num) rep_N (half_rep rep_D) gas_end_neg dilE (r := rND)
    (encl_chk ptsNeg ptsDl) (q := qZ ptsNeg ptsDl) rfl box_ND tvN tvD'
  rw [len_N, len_D] at h
  refine (cast_lit h (by norm_num)).trans ?_
  norm_num [linkC, kap]

theorem good_of {V : List Pt} (h : V.all (fun u => ptOK u.1.natAbs) = true) :
    ∀ p ∈ V.map (mkPD L2c), p.Good := fun p hp => by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
  exact mkPD_good u (List.all_eq_true.mp h u hu)

theorem small_pos {c e : ℝ} (hc : 0 ≤ c) (hl : c ≤ e) {x y z : ℝ} (h : |x - y| ≤ z + c) (hz : z + e ≤ 1 / 10 ^ 9) :
    |x - y| ≤ 1 / 10 ^ 9 := by linarith

theorem lenP_le : lenL gP ≤ 26 * 427 := by
  have h := lenL_le gas_end_pos
  rwa [len_P] at h

theorem lenN_le : lenL gN ≤ 26 * 277 := by
  have h := lenL_le gas_end_neg
  rwa [len_N] at h

theorem scale_le {L c : ℝ} (hL : L ≤ c) (K : ℝ) (hK : 0 ≤ K) : kap * K * L ≤ kap * K * c :=
  mul_le_mul_of_nonneg_left hL (mul_nonneg kap_pos.le hK)

theorem len_nn (F : List YCell) : 0 ≤ lenL F := by
  unfold lenL
  apply List.sum_nonneg
  intro x hx
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  linarith [c.lo_lt]

theorem G0_nn : (0 : ℝ) ≤ G0 := by norm_num [G0]

theorem mass_P : |massL gP - 63489562168082 / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
  have h := cast_lit (qBox_le box_scal.1) (r := 63489562168082) (by norm_num)
  have e : massL gP = (sumP gasPosT : ℝ) / (sumP row0 : ℝ) := massPos
  rw [e]
  exact h.trans (by norm_num)

theorem mass_N : |massL gN - 36510437831917 / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
  have h := cast_lit (qBox_le box_scal.2.1) (r := 36510437831917) (by norm_num)
  have e : massL gN = (sumP gasNegT : ℝ) / (sumP row0 : ℝ) := massNeg
  rw [e]
  exact h.trans (by norm_num)

theorem am_P : |capSource.auxMass Sign.pos - 36510437831917 / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
  have h := cast_lit (qBox_le box_scal.2.2.1) (r := 36510437831917) (by norm_num)
  have t0 : (sumP row0 : ℝ) ≠ 0 := by exact_mod_cast row0_tot.ne'
  have e : capSource.auxMass Sign.pos = (cPn : ℝ) / (sumP row0 : ℝ) := by
    rw [auxMass_eq]
    simp only [tgt, massPos, cPn]
    push_cast
    field_simp
  rw [e]
  exact h.trans (by norm_num)

theorem am_N : |capSource.auxMass Sign.neg - 54868872512909 / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
  have h := cast_lit (qBox_le box_scal.2.2.2.1) (r := 54868872512909) (by norm_num)
  have t0 : (sumP row0 : ℝ) ≠ 0 := by exact_mod_cast row0_tot.ne'
  have e : capSource.auxMass Sign.neg = (cNn : ℝ) / ((58 * sumP row0 : ℤ) : ℝ) := by
    rw [auxMass_eq]
    simp only [tgt, massNeg, cNn]
    push_cast
    field_simp
  rw [e]
  exact h.trans (by norm_num)

theorem log2_box : |Real.log 2 - 69314718055994 / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
  have h := cast_lit (qBox_le box_scal.2.2.2.2.2.2.2) (r := 69314718055994) (by norm_num)
  have l := L2c_close
  have g : (LG : ℕ) = 96 := rfl
  rw [g] at l
  have c : ((L2c : ℤ) : ℝ) / ((2 ^ 96 : ℤ) : ℝ) = (L2c : ℝ) / 2 ^ 96 := by
    rw [Int.cast_natCast, Int.cast_pow]
    norm_num
  rw [c] at h
  have := Ttri l h
  exact this.trans (by norm_num)

theorem tail_box : |tailUnit capSource KK - 788755782 / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
  obtain ⟨b0, b1, b2⟩ := box_tail
  have h := ballBox_le (tailB_has b1 b2) b0
  have e : ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ) * tailUnit capSource KK = tailUnit capSource KK := by
    norm_num
  rw [e] at h
  have := cast_lit h (r := 788755782) (by norm_num)
  exact this.trans (by norm_num)

theorem sP_box : |cS Sign.pos * cS Sign.pos * ((SminZ paT : ℝ) / 10 ^ 17) -
    6880564215755 / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
  have h := cast_lit (qBox_le box_scal.2.2.2.2.1) (r := 6880564215755) (by norm_num)
  have e : ((cPn ^ 2 * SminZ paT : ℤ) : ℝ) / ((cPd ^ 2 * 10 ^ 17 : ℤ) : ℝ) =
      cS Sign.pos * cS Sign.pos * ((SminZ paT : ℝ) / 10 ^ 17) := by
    rw [cS_pos_eq]
    push_cast
    ring
  rw [e] at h
  exact h.trans (by norm_num)

theorem sN_box : |cS Sign.neg * cS Sign.neg * ((SmaxZ naT : ℝ) / 10 ^ 17) -
    43657136919364 / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
  have h := cast_lit (qBox_le box_scal.2.2.2.2.2.1) (r := 43657136919364) (by norm_num)
  have e : ((cNn ^ 2 * SmaxZ naT : ℤ) : ℝ) / ((cNd ^ 2 * 10 ^ 17 : ℤ) : ℝ) =
      cS Sign.neg * cS Sign.neg * ((SmaxZ naT : ℝ) / 10 ^ 17) := by
    rw [cS_neg_eq]
    push_cast
    ring
  rw [e] at h
  exact h.trans (by norm_num)

theorem aL_box : |auxLog capSource - (-53351287497253) / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
  have h := cast_lit (qBox_le box_scal.2.2.2.2.2.2.1) (r := 53351287497253) (by norm_num)
  have e : ((cNn * SlinZ naT : ℤ) : ℝ) / ((cNd * 10 ^ 17 : ℤ) : ℝ) =
      cS Sign.neg * ((SlinZ naT : ℝ) / 10 ^ 17) := by
    rw [cS_neg_eq]
    push_cast
    ring
  rw [e] at h
  rw [auxLog_form]
  have e2 : -(cS Sign.neg * ((SlinZ naT : ℝ) / 10 ^ 17)) - (-53351287497253) / 10 ^ 14 =
      -(cS Sign.neg * ((SlinZ naT : ℝ) / 10 ^ 17) - 53351287497253 / 10 ^ 14) := by ring
  rw [e2, abs_neg]
  exact h.trans (by norm_num)

theorem mass_aux (σ : Sign) : cS σ * (sumP (auxT σ) : ℝ) = capSource.auxMass σ := by
  have h : (sumP (auxT σ) : ℝ) ≠ 0 := by
    cases σ
    · exact_mod_cast na_tot.ne'
    · exact_mod_cast pa_tot.ne'
  rw [auxMass_eq, cS, div_mul_cancel₀ _ h]

/-- The target bound `hi` (design C: 2366997 / 1000000). -/
theorem hi_final :
    -InterceptSource.refQuad capSource 0 + CompletedGas.gasConst capSource ≤ 2366997 / 1000000 := by
  have hU : ∀ p ∈ Up, p.Good := good_of pts_okP
  have hN : ∀ p ∈ Un, p.Good := good_of pts_okN
  obtain ⟨r1, l1, f1, a1⟩ := pos_out box_pos hU tv_up
  obtain ⟨r2, l2, a2⟩ := neg_out box_neg hN tv_un
  have lP := len_nn gP
  have lN := len_nn gN
  have sG : ∀ {L c : ℝ}, 0 ≤ L → L ≤ c → c ≤ 26 * 427 → kap * G0 * L ≤ 1 / 10 ^ 10 := by
    intro L c _ h1 h2
    have := scale_le (h1.trans h2) G0 G0_nn
    refine this.trans ?_
    norm_num [kap, G0]
  have s13 : ∀ {L : ℝ}, L ≤ 26 * 427 → kap * 13 * L ≤ 1 / 10 ^ 10 := by
    intro L h1
    have := scale_le h1 13 (by norm_num)
    refine this.trans ?_
    norm_num [kap]
  have s1 : ∀ {L : ℝ}, L ≤ 26 * 427 → 1000 * (kap * 1 * L) ≤ 1 / 10 ^ 10 := by
    intro L h1
    have := scale_le h1 1 (by norm_num)
    have k : kap * 1 * (26 * 427) * 1000 ≤ 1 / 10 ^ 10 := by norm_num [kap]
    linarith
  have lN' : lenL gN ≤ 26 * 427 := lenN_le.trans (by norm_num)
  have hRP : |physL gP (capSource.radialA (Trunc.finite KK) Sign.pos) -
      (-853339519085) / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
    have h := cast_lit r1 (r := -853339519085) (by norm_num)
    have g := sG lP lenP_le le_rfl
    refine h.trans ?_
    have : ((2 : ℤ) : ℝ) / 10 ^ 14 ≤ 1 / 10 ^ 10 := by norm_num
    linarith [show (1 : ℝ) / 10 ^ 10 + 1 / 10 ^ 10 ≤ 1 / 10 ^ 9 by norm_num]
  have hLp : |physL gP (fun u => Real.log |u|) - (-39541675682036) / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
    have h := cast_lit l1 (r := -39541675682036) (by norm_num)
    have g := s13 lenP_le
    refine h.trans ?_
    have : ((2 : ℤ) : ℝ) / 10 ^ 14 ≤ 1 / 10 ^ 10 := by norm_num
    linarith [show (1 : ℝ) / 10 ^ 10 + 1 / 10 ^ 10 ≤ 1 / 10 ^ 9 by norm_num]
  have hRN : |physL gN (capSource.radialA (Trunc.finite KK) Sign.neg) -
      (-1357201154220) / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
    have e : physL gN (capSource.radialA (Trunc.finite KK) Sign.neg) - (-1357201154220) / 10 ^ 14 =
        physL gN (capSource.radialA (Trunc.finite KK) Sign.neg) + ((1357201154220 : ℤ) : ℝ) / 10 ^ 14 := by
      push_cast
      ring
    rw [e]
    have g := sG lN lN' le_rfl
    refine r2.trans ?_
    have : ((2 : ℤ) : ℝ) / 10 ^ 14 ≤ 1 / 10 ^ 10 := by norm_num
    linarith [show (1 : ℝ) / 10 ^ 10 + 1 / 10 ^ 10 ≤ 1 / 10 ^ 9 by norm_num]
  have hLn : |physL gN (fun u => Real.log |u|) - (-29512640381580) / 10 ^ 14| ≤ 1 / 10 ^ 9 := by
    have e : physL gN (fun u => Real.log |u|) - (-29512640381580) / 10 ^ 14 =
        physL gN (fun u => Real.log |u|) + ((29512640381580 : ℤ) : ℝ) / 10 ^ 14 := by
      push_cast
      ring
    rw [e]
    have g := s13 lN'
    refine l2.trans ?_
    have : ((2 : ℤ) : ℝ) / 10 ^ 14 ≤ 1 / 10 ^ 10 := by norm_num
    linarith [show (1 : ℝ) / 10 ^ 10 + 1 / 10 ^ 10 ≤ 1 / 10 ^ 9 by norm_num]
  have hRf : 23239004899126 / 10 ^ 14 - 1 / 10 ^ 9 ≤
      ∑ k ∈ Finset.range KK, physL gP (fun u => u ^ (k + 1)) ^ 2 / ((k : ℝ) + 1) := by
    have g := s1 lenP_le
    refine le_trans ?_ f1
    push_cast
    norm_num at g ⊢
    linarith
  have huP := cast_lit a1 (r := -3944317782559) (by norm_num)
  have huN := cast_lit a2 (r := -5869925662132) (by norm_num)
  have huP' : |cS Sign.pos * cS Sign.pos * aqV false paT - (-3944317782559) / 10 ^ 14| ≤ 1 / 10 ^ 9 :=
    huP.trans (by norm_num)
  have huN' : |cS Sign.neg * cS Sign.neg * aqV true naT - (-5869925662132) / 10 ^ 14| ≤ 1 / 10 ^ 9 :=
    huN.trans (by norm_num)
  have hP := energyP_ge capSource_admissible KK KK
  have hM := energyM_ge capSource_admissible KK
  have mP : (PsumZ paT : ℝ) = (sumP paT : ℝ) := by rw [sums_eq.1]
  have mN : (PsumZ naT : ℝ) = (sumP naT : ℝ) := by rw [sums_eq.2]
  have eP : auxQuadP capSource KK = -(cS Sign.pos * cS Sign.pos * ((SminZ paT : ℝ) / 10 ^ 17)) -
      capSource.auxMass Sign.pos * capSource.auxMass Sign.pos * tailUnit capSource KK +
      cS Sign.pos * cS Sign.pos * aqV false paT := by
    rw [aqP_form, mP, ← mass_aux Sign.pos]
    simp only [auxT]
    ring
  have eN : auxQuadN capSource KK = cS Sign.neg * cS Sign.neg * ((SmaxZ naT : ℝ) / 10 ^ 17) -
      capSource.auxMass Sign.neg * capSource.auxMass Sign.neg *
        (Real.log 2 + 2 * tailUnit capSource KK) +
      cS Sign.neg * cS Sign.neg * aqV true naT := by
    rw [aqN_form, mN, ← mass_aux Sign.neg]
    simp only [auxT]
    ring
  have tP : tailS capSource KK Sign.pos = tailUnit capSource KK := by simp [tailS]
  have tN : tailS capSource KK Sign.neg = tailUnit capSource KK * 2 := by simp [tailS]
  rw [eP, tP] at hP
  rw [eN, tN] at hM
  have hLP := hP
  have hLM := hM
  unfold InterceptSource.refQuad CompletedGas.gasConst
  rw [energy_RR, energy_RD]
  have hcM : cM capSource = physL gN (fun u => Real.log |u|) + auxLog capSource := rfl
  rw [hcM]
  have h := hi_alg (κp := kappa Sign.pos) (κn := kappa Sign.neg)
    (LP := planarEnergy (qP capSource)) (LM := planarEnergy (qM capSource)) rfl rfl E_PP E_NN E_CC E_PN E_PD E_ND
    mass_P mass_N am_P am_N log2_box tail_box hLp hLn hRP hRN hRf huP' huN' sP_box sN_box aL_box
    tauInt_ge (by linarith) (by linarith)
  exact h

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

#print axioms CatalanMeasure.GenD.Signed.RouteI.GasEnergy.hi_final
