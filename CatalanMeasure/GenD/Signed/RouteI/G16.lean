module

public import CatalanMeasure.GenD.Signed.RouteI.TerminalC
public import CatalanMeasure.GenD.Signed.RouteI.ChordLineData
public import CatalanMeasure.GenD.Signed.RouteI.NearDataCert
public import CatalanMeasure.GenD.Signed.RouteI.OrdHf
public import CatalanMeasure.GenD.Signed.RouteI.AngAll

@[expose] public section
set_option Elab.async false

/-!
# Route I `G16`: the ordinary, near and angular caps of the terminal at the node correction `δ̂` (ledger G16)

Inputs of `TerminalC.NearData`: `ho`, `hn`, `hoc`, `hnc`, `ha`.

* `ho σ`: `capSource.OrdCap Trunc.exact σ (nodeD P58 δc) Gd (-976/1000)`, by `CompactCells.ordCap_of_chain` on the
  built cells `CompactCellsB.All`, the polynomial majorants `OrdHf.posHf`, `OrdHf.negHf` and the chord pieces of
  the cells (`ChordLineData.pos_chord`, `neg_chord`), then `CompactCap.ordCap_exact`.
* `hn`: `NearCap` likewise (`nearCap_of_chain`, `NearDataCert.nearHf_capSource`, `near_chord`); the zero region
  `(0, 1/10]` is the zero geometry of the near field plus `δ̂ ≤ 52`.
* `ha`: the angular caps `κ σ` at the exact fields from `AngAll.certN`, `certP` through the generic
  `AngularCap.angCap_of_certs`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.G16

open CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.CapFields
  CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource CatalanMeasure.GenD.Signed.RouteI.CapSourceData
  CatalanMeasure.GenD.Signed.RouteI.ChordTable CatalanMeasure.GenD.Signed.RouteI.ChordTableData
  CatalanMeasure.GenD.Signed.RouteI.ChordLine CatalanMeasure.GenD.Signed.RouteI.ChordLineData
  CatalanMeasure.GenD.Signed.RouteI.CompactCells CatalanMeasure.GenD.Signed.RouteI.CompactCap
  CatalanMeasure.GenD.Signed.RouteI.CompactCellsB.All CatalanMeasure.GenD.Signed.RouteI.TerminalC
  CatalanMeasure.GenD.Signed.RouteI.Family CatalanMeasure.GenD.Signed.RouteI.IntervalNodesData
  OAI.InternalCatalan Set

noncomputable section

/-! ### The window `Gd` against the hull of the knots -/

theorem knot0 : kt 0 = -(1098755891408 : ℝ) / 2 ^ 40 := by
  have : knotZ 0 = -1098755891408 := by decide +kernel -- kcost: 0.01 s (one packed-knot decode, measured in the merged build)
  unfold kt; rw [this]; push_cast; ring

theorem knot865 : kt 865 = (1099511436971 : ℝ) / 2 ^ 40 := by
  have : knotZ 865 = 1099511436971 := by decide +kernel -- kcost: 0.01 s (one packed-knot decode, measured in the merged build)
  unfold kt; rw [this]; push_cast; ring

theorem gd_hull {x : ℝ} (h : Gd x) : kt 0 < 2 * x / (1 + x ^ 2) ∧ 2 * x / (1 + x ^ 2) < kt 865 := by
  obtain ⟨-, hU⟩ := h
  obtain ⟨c, hc⟩ := mem_iUnion.mp hU
  have hh := hull_table c
  exact ⟨lt_of_le_of_lt hh.1 hc.1, lt_of_lt_of_le hc.2 hh.2⟩

theorem gd_abs {x : ℝ} (h : Gd x) : |x| ≤ 1 := h.1

/-- The window of the design in `x`. -/
theorem gd_window {x : ℝ} (h : Gd x) : -9636 / 10000 ≤ x ∧ x ≤ 99942 / 100000 := by
  obtain ⟨h0, h1⟩ := gd_hull h
  have hx := abs_le.mp (gd_abs h)
  constructor
  · by_contra hlt
    push_neg at hlt
    have := tau_mono hx.1 hlt.le (by norm_num : (-9636 / 10000 : ℝ) ≤ 1)
    rw [knot0] at h0
    norm_num at this h0
    linarith
  · by_contra hlt
    push_neg at hlt
    have := tau_mono (by norm_num : (-1 : ℝ) ≤ 99942 / 100000) hlt.le hx.2
    rw [knot865] at h1
    norm_num at this h1
    linarith

/-- Upper end of the cells in `x`. -/
theorem gd_top {x : ℝ} (h : Gd x) : x ≤ 1098864064970 / 1099511627776 := by
  obtain ⟨h0, h1⟩ := gd_hull h
  have hx := abs_le.mp (gd_abs h)
  by_contra hlt
  push_neg at hlt
  have := tau_mono (by norm_num : (-1 : ℝ) ≤ 1098864064970 / 1099511627776) hlt.le hx.2
  rw [knot865] at h1
  norm_num at this h1
  linarith

/-! ### Chord pieces of the cells -/

theorem cell_core {ylo yhi A B : ℚ} {cc : ChordCell} (h : yChk ylo yhi A B cc = true) {y : ℝ}
    (hy1 : (ylo : ℝ) ≤ y) (hy2 : y ≤ (yhi : ℝ)) (hG : Gd y) :
    δc (2 * y / (1 + y ^ 2)) ≤ (A : ℝ) + (B : ℝ) * (2 * y / (1 + y ^ 2)) := by
  obtain ⟨h0, h1⟩ := gd_hull hG
  exact yChk_sound h hy1 hy2 h0.le h1.le

theorem nodeD_eq (u : ℝ) : nodeD P58 δc u = δc (2 * u / (1 + u ^ 2)) / 58 := by
  unfold nodeD realCoordinateInv; rfl

theorem hd_pos_of (cl : CellData) (hex : ∃ cc, yChk ((cl.u0 : ℚ) / 1099511627776) ((cl.u1 : ℚ) / 1099511627776)
        (58 * (cl.a : ℚ) / 2 ^ 60) (58 * (cl.b : ℚ) / 2 ^ 60) cc = true) {y : ℝ}
    (hy1 : (cl.u0 : ℝ) / 1099511627776 ≤ y)
    (hy2 : y ≤ (cl.u1 : ℝ) / 1099511627776) (hG : Gd y) :
    nodeD P58 δc y ≤ (cl.a : ℝ) / 2 ^ 60 + ((cl.b : ℝ) / 2 ^ 60) * (2 * y / (1 + y ^ 2)) := by
  obtain ⟨cc, hcc⟩ := hex
  have := cell_core hcc (y := y) (by push_cast; exact hy1) (by push_cast; exact hy2) hG
  rw [nodeD_eq, div_le_iff₀ (by norm_num)]
  push_cast at this
  linarith

theorem hd_neg_of (cl : CellData) (hex : ∃ cc, yChk (-((cl.u1 : ℚ) / 1099511627776)) (-((cl.u0 : ℚ) / 1099511627776))
        (58 * (cl.a : ℚ) / 2 ^ 60) (-(58 * (cl.b : ℚ) / 2 ^ 60)) cc = true) {u : ℝ}
    (hy1 : (cl.u0 : ℝ) / 1099511627776 ≤ u)
    (hy2 : u ≤ (cl.u1 : ℝ) / 1099511627776) (hG : Gd (-u)) :
    nodeD P58 δc (-u) ≤ (cl.a : ℝ) / 2 ^ 60 + ((cl.b : ℝ) / 2 ^ 60) * (2 * u / (1 + u ^ 2)) := by
  obtain ⟨cc, hcc⟩ := hex
  have := cell_core hcc (y := -u) (by push_cast; linarith) (by push_cast; linarith) hG
  rw [nodeD_eq, div_le_iff₀ (by norm_num)]
  push_cast at this
  have e : 2 * -u / (1 + (-u) ^ 2) = -(2 * u / (1 + u ^ 2)) := by ring
  rw [e] at this ⊢
  linarith

theorem chk_pos : ∀ cl ∈ posCells, ∃ cc, yChk ((cl.u0 : ℚ) / 1099511627776) ((cl.u1 : ℚ) / 1099511627776)
        (58 * (cl.a : ℚ) / 2 ^ 60) (58 * (cl.b : ℚ) / 2 ^ 60) cc = true := by
  intro cl hcl
  have h := List.all_eq_true.mp pos_chord cl hcl
  unfold posChk at h
  cases hl : lookupCC posTab cl.u0 with
  | none => rw [hl] at h; simp at h
  | some cc => rw [hl] at h; exact ⟨cc, h⟩

theorem chk_near : ∀ cl ∈ nearCells, ∃ cc, yChk ((cl.u0 : ℚ) / 1099511627776) ((cl.u1 : ℚ) / 1099511627776)
        (58 * (cl.a : ℚ) / 2 ^ 60) (58 * (cl.b : ℚ) / 2 ^ 60) cc = true := by
  intro cl hcl
  have h := List.all_eq_true.mp near_chord cl hcl
  unfold nearChk at h
  cases hl : lookupCC nearTab cl.u0 with
  | none => rw [hl] at h; simp at h
  | some cc => rw [hl] at h; exact ⟨cc, h⟩

theorem chk_neg : ∀ cl ∈ negCells, ∃ cc, yChk (-((cl.u1 : ℚ) / 1099511627776)) (-((cl.u0 : ℚ) / 1099511627776))
        (58 * (cl.a : ℚ) / 2 ^ 60) (-(58 * (cl.b : ℚ) / 2 ^ 60)) cc = true := by
  intro cl hcl
  have h := List.all_eq_true.mp neg_chord cl hcl
  unfold negChk at h
  cases hl : lookupCC negTab cl.u0 with
  | none => rw [hl] at h; simp at h
  | some cc => rw [hl] at h; exact ⟨cc, h⟩


/-! ### Ordinary caps -/

theorem pwl_le_52 (t : ℝ) : δc t ≤ 52 := by
  have hv : ∀ i, i ≤ 865 → vt i ≤ 52 := by
    have h : (List.range 866).all (fun i => decide (vq i ≤ 52)) = true := by
      decide +kernel -- kcost: 866 rational comparisons, 0.67 s measured 7 Nov
    intro i hi
    have := of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr (by omega)))
    rw [vt_eq]; exact_mod_cast Rat.cast_le.mpr this
  by_cases ht : kt 0 ≤ t ∧ t ≤ kt 865
  · obtain ⟨i, hi, hseg⟩ := exists_seg (K := 865) (k := kt) (by norm_num) ht.1 ht.2
    have := pwl_le_max (v := vt) kt_lt hi hseg
    exact this.trans (max_le (hv i (by omega)) (hv (i + 1) (by omega)))
  · have h0 : δc t = 0 := by
      apply pwl_zero_outside kt_lt
      by_contra hn
      push_neg at hn
      exact ht hn
    rw [h0]; norm_num

theorem ordCap_neg_fin : capSource.OrdCap (Trunc.finite 384) Sign.neg (nodeD P58 δc) Gd (-976 / 1000) := by
  refine ordCap_of_chain capSource (Trunc.finite 384) Sign.neg (nodeD P58 δc) Gd (-976 / 1000)
    (P := CompactInstance.negP) (D := CompactInstance.D) (loN := 19501) (loD := 100000) (MN := -976) (MD := 1000)
    (eN := negEN) (eD := negED) (Q := 1099511627776) CompactInstance.D_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [negED]) (by simp [ordLo]) (by norm_num) ?_ negCells neg_chk
    neg_cover (a := negA) (hi := negHi) (by norm_num [negA, ordLo]) ?_ ?_
  · intro u hu
    have h := OrdHf.negHf u (by simpa [ordDom_eq, ordLo] using hu)
    have e : ((if Sign.neg = Sign.neg then (-1 : ℝ) else 1) * u) = -u := by simp
    rw [e]
    have e2 : (CompactInstance.negEps : ℝ) = (negEN : ℝ) / (negED : ℝ) := by
      norm_num [CompactInstance.negEps, negEN, negED]
    simp only [ordLo]
    rw [← e2]; exact h
  · intro u hu hG
    have e : ((if Sign.neg = Sign.neg then (-1 : ℝ) else 1) * u) = -u := by simp
    rw [e] at hG
    have hw := (gd_window hG).1
    have hu1 : u ≤ 9636 / 10000 := by linarith
    refine hu1.trans ?_
    norm_num [negHi]
  · intro cl hcl u hu h1 h2 hG
    have e : ((if Sign.neg = Sign.neg then (-1 : ℝ) else 1) * u) = -u := by simp
    rw [e] at hG ⊢
    exact hd_neg_of cl (chk_neg cl hcl) (by exact_mod_cast h1) (by exact_mod_cast h2) hG

theorem ordCap_pos_fin : capSource.OrdCap (Trunc.finite 384) Sign.pos (nodeD P58 δc) Gd (-976 / 1000) := by
  refine ordCap_of_chain capSource (Trunc.finite 384) Sign.pos (nodeD P58 δc) Gd (-976 / 1000)
    (P := CompactInstance.posP) (D := CompactInstance.D) (loN := 98749) (loD := 1000000) (MN := -976) (MD := 1000)
    (eN := posEN) (eD := posED) (Q := 1099511627776) CompactInstance.D_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [posED]) (by simp [ordLo]) (by norm_num) ?_ posCells pos_chk
    pos_cover (a := posA) (hi := posHi) (by norm_num [posA, ordLo]) ?_ ?_
  · intro u hu
    have h := OrdHf.posHf u (by simpa [ordDom_eq, ordLo] using hu)
    have e : ((if Sign.pos = Sign.neg then (-1 : ℝ) else 1) * u) = u := by simp
    rw [e]
    have e2 : (CompactInstance.posEps : ℝ) = (posEN : ℝ) / (posED : ℝ) := by
      norm_num [CompactInstance.posEps, posEN, posED]
    simp only [ordLo]
    rw [← e2]; exact h
  · intro u hu hG
    have e : ((if Sign.pos = Sign.neg then (-1 : ℝ) else 1) * u) = u := by simp
    rw [e] at hG
    have := gd_top hG
    simpa [posHi] using this
  · intro cl hcl u hu h1 h2 hG
    have e : ((if Sign.pos = Sign.neg then (-1 : ℝ) else 1) * u) = u := by simp
    rw [e] at hG ⊢
    exact hd_pos_of cl (chk_pos cl hcl) (by exact_mod_cast h1) (by exact_mod_cast h2) hG

theorem ho : ∀ σ, capSource.OrdCap Trunc.exact σ (nodeD P58 δc) Gd (-976 / 1000) := by
  intro σ
  cases σ
  · exact ordCap_exact capSource capSource_admissible ordCap_neg_fin
  · exact ordCap_exact capSource capSource_admissible ordCap_pos_fin

/-! ### Near cap -/

theorem nearCap_fin : capSource.NearCap (Trunc.finite 384) (nodeD P58 δc) Gd (-976 / 1000) := by
  obtain ⟨hs, hc⟩ := CompactInstance.strength_curvature_le capSource
    capSource_admissible.eps_pos capSource_eps_le
  have hM : capSource.auxMass Sign.pos ≤ 37 / 100 := by
    rw [capSource_admissible.aux_pos_mass]; linarith [capSource_massL_pos_ge]
  have hM0 : 0 ≤ capSource.auxMass Sign.pos := by
    unfold CapSource.auxMass
    exact List.sum_nonneg (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact e.w_nonneg)
  have hs0 : 0 ≤ capSource.strength := by
    unfold CapSource.strength CapSource.normalizer
    obtain ⟨h1, h2⟩ := CompactInstance.r_bounds capSource capSource_eps_le capSource_admissible.eps_pos
    have : 0 < 1 - capSource.q ^ 2 := by linarith
    positivity
  have hc0 : 0 ≤ capSource.curvature := by
    unfold CapSource.curvature CapSource.normalizer
    obtain ⟨h1, h2⟩ := CompactInstance.r_bounds capSource capSource_eps_le capSource_admissible.eps_pos
    have : 0 < 1 - capSource.q ^ 2 := by linarith
    positivity
  have hE := CompactInstance.auxTail_pos_le capSource hs hc hs0 hc0 capSource_eps_ge hM hM0
  refine nearCap_of_chain capSource (Trunc.finite 384) (nodeD P58 δc) Gd (-976 / 1000)
    (P := CompactInstance.nearP) (D := CompactInstance.D) (loN := 1) (loD := 10) (MN := -976) (MD := 1000)
    (eN := nearEN) (eD := nearED) (Q := 1099511627776) CompactInstance.D_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [nearED]) (by norm_num) (by norm_num) ?_ ?_ nearCells near_chk
    near_cover (a := nearA) (hi := nearHi) (by norm_num [nearA]) ?_ ?_
  · intro y hy
    have h := NearDataCert.nearHf_capSource y hy
    have e2 : (CompactInstance.nearEps : ℝ) = (nearEN : ℝ) / (nearED : ℝ) := by
      norm_num [CompactInstance.nearEps, nearEN, nearED]
    rw [← e2]; exact h
  · intro y hy hG
    have hg := CompactSource.near_zero_geometry capSource capSource_admissible (Trunc.finite 384) hs hc hM hy.1 hy.2
    have z := zero_near_gen hy.1 hy.2 (show (1 / 10 : ℝ) ≤ kappa Sign.pos by norm_num [kappa])
    have hd : nodeD P58 δc y ≤ 52 / 58 := by
      rw [nodeD_eq, div_le_iff₀ (by norm_num)]
      linarith [pwl_le_52 (2 * y / (1 + y ^ 2))]
    have : (24 / 29) * Real.log y + Real.log (1 + y) - kappa Sign.pos + capSource.auxTail (Trunc.finite 384) Sign.pos
        ≤ -19 / 10 + 1 / 100 := by linarith
    linarith
  · intro y hy hG
    have := gd_top hG
    simpa [nearHi] using this
  · intro cl hcl y hy h1 h2 hG
    exact hd_pos_of cl (chk_near cl hcl) (by exact_mod_cast h1) (by exact_mod_cast h2) hG

theorem hn : capSource.NearCap Trunc.exact (nodeD P58 δc) Gd (-976 / 1000) :=
  nearCap_exact capSource capSource_admissible nearCap_fin

/-! ### Angular caps at the exact fields -/

theorem ha : ∀ σ, capSource.AngCap Trunc.exact σ (kappa σ) := by
  intro σ i hi θ
  refine (AngularSource.angular_dominates capSource capSource_admissible 384 σ i hi θ).trans ?_
  cases σ
  · have := AngularCap.angCap_of_certs capSource capSource_admissible Sign.neg (5463909 / 100000000)
      AngAll.certN i hi θ
    norm_num [kappa] at this ⊢
    exact this
  · have := AngularCap.angCap_of_certs capSource capSource_admissible Sign.pos (14762657 / 100000000)
      AngAll.certP i hi θ
    norm_num [kappa] at this ⊢
    exact this

end

end CatalanMeasure.GenD.Signed.RouteI.G16

#print axioms CatalanMeasure.GenD.Signed.RouteI.G16.ho
#print axioms CatalanMeasure.GenD.Signed.RouteI.G16.hn
#print axioms CatalanMeasure.GenD.Signed.RouteI.G16.ha
