module

public import CatalanMeasure.GenD.Signed.RouteI.ShiftGFirst
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafX
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1b
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2a
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2b

@[expose] public section
set_option Elab.async false

/-!
# G5 shiftG, assembly: the record skeletons of `TerminalC`

* `Y2fun`, `Y1fun`: the piecewise affine column caps through the knots of `ShiftGLeafY2a/b`,
  `ShiftGLeafY1a/b` (`τ = 1`, `γ = β`), and the ray caps `τ y(a₁)`, `τ y(11/50)` of the physical
  windows;
* `largeDataOf`, `firstDataOf`: `TerminalC.LargeData` and `FirstData` from the cell data (`A, B`,
  the cap polynomials `nC, fC, rs, np`, `hPoly`) and four elementary domination hypotheses
  (polynomial against the exact cap function of `β`); the record `R` is `ShiftGSecond.secondRec`
  resp. `ShiftGFirst.firstRec`;
* `nearRp`, `hSp_of`, `hp2p_of`: the unsigned fields `Rp, hNp, hFp, hSp, hp2p` of `NearData`.
-/

open Set Filter

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGAsm
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.ShiftG
  CatalanMeasure.GenD.Signed.RouteI.ShiftGNum CatalanMeasure.GenD.Signed.RouteI.ShiftGSecond
  CatalanMeasure.GenD.Signed.RouteI.ShiftGFirst CatalanMeasure.GenD.Signed.RouteI.Family
  CatalanMeasure.GenD.Signed.RouteI.TerminalC CatalanMeasure.GenD.Signed.RouteI.T4Instance
  CatalanMeasure.GenD.Signed.RouteI.CompletedGas CatalanMeasure.GenD.D58 CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.RouteI

noncomputable section

/-! ### Interpolation of the knot caps -/

/-- The affine interpolation of the knot caps `ya` at `ga`, `yb` at `gb`. -/
def yI (ga gb ya yb β : ℝ) : ℝ := ya + (β - ga) / (gb - ga) * (yb - ya)

theorem yI_seg {ga gb ya yb β T g : ℝ} (hab : ga < gb) (ha : 2 * T + ga * g ≤ ya)
    (hb : 2 * T + gb * g ≤ yb) (h0 : ga ≤ β) (h1 : β ≤ gb) :
    β * g + 2 * T ≤ yI ga gb ya yb β := by
  have hd : 0 < gb - ga := sub_pos.mpr hab
  set w : ℝ := (β - ga) / (gb - ga) with hw
  have hw0 : 0 ≤ w := div_nonneg (by linarith) hd.le
  have hw1 : w ≤ 1 := by rw [hw, div_le_one hd]; linarith
  have hwe : w * (gb - ga) = β - ga := by rw [hw]; field_simp
  have := col_interp (T := T) (g := g) (ta := 1) (ga := ga) (tb := 1) (gb := gb) (Ya := ya) (Yb := yb)
    (w := w) (by simpa using ha) (by simpa using hb) hw0 hw1
  have e1 : (1 - w) * 1 + w * 1 = 1 := by ring
  have e2 : (1 - w) * ga + w * gb = β := by linarith [hwe]
  have e3 : yI ga gb ya yb β = (1 - w) * ya + w * yb := by unfold yI; rw [← hw]; ring
  rw [e1, e2] at this
  rw [e3]
  linarith

/-- A ray cap: `(τ, β) = τ (1, γ)`. -/
theorem yRay {γ y τ β T g : ℝ} (h : 2 * T + γ * g ≤ y) (hτ : 0 ≤ τ) (hβ : β = τ * γ) :
    β * g + 2 * (τ * T) ≤ τ * y := by
  subst hβ
  have := mul_le_mul_of_nonneg_left h hτ
  nlinarith [this]

/-! ### The row caps -/

def X2cap : ℝ := 1484272 / 10 ^ 8
def X1cap : ℝ := 2748620 / 10 ^ 8

theorem hX2 : ∀ x ∈ Icc (-1 : ℝ) 1, -(4 * barrierTrialT duS x) - barrierTrialS dvS x ≤ X2cap :=
  fun x hx => by
    have := ShiftGLeafX.X2_leaf x hx
    unfold X2cap
    exact this

theorem hX1 : ∀ x ∈ Icc (-1 : ℝ) 1, -(2 * barrierTrialT duF x) - barrierTrialS dvF x +
    (213407 / 2 ^ 23 : ℝ) * (5 / 29 - 2 * x ^ 2 / (1 + x ^ 2)) ≤ X1cap :=
  fun x hx => by
    have := ShiftGLeafX.X1_leaf x hx
    unfold X1cap
    exact this

/-! ### The second-population column cap, `τ = 1` -/

def y2 (i : ℕ) : ℝ :=
  ((![13909310, 19392203, 24989188, 30584470, 41776613, 52968854, 64161468] : Fin 7 → ℤ) (Fin.ofNat 7 i) : ℝ) / 10 ^ 8

/-- Column cap of the large sheet at `γ = β ∈ [51/500, 1]`. -/
def Y2fun (β : ℝ) : ℝ :=
  if β ≤ 1 / 5 then yI (51 / 500) (1 / 5) (13909310 / 10 ^ 8) (19392203 / 10 ^ 8) β
  else if β ≤ 3 / 10 then yI (1 / 5) (3 / 10) (19392203 / 10 ^ 8) (24989188 / 10 ^ 8) β
  else if β ≤ 2 / 5 then yI (3 / 10) (2 / 5) (24989188 / 10 ^ 8) (30584470 / 10 ^ 8) β
  else if β ≤ 3 / 5 then yI (2 / 5) (3 / 5) (30584470 / 10 ^ 8) (41776613 / 10 ^ 8) β
  else if β ≤ 4 / 5 then yI (3 / 5) (4 / 5) (41776613 / 10 ^ 8) (52968854 / 10 ^ 8) β
  else yI (4 / 5) 1 (52968854 / 10 ^ 8) (64161468 / 10 ^ 8) β

theorem Y2fun_hY {β : ℝ} (h0 : 51 / 500 ≤ β) (h1 : β ≤ 1) :
    ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (1 * barrierTrialT dvS s) ≤ Y2fun β := by
  intro s hs
  have a0 := ShiftGLeafY2a.Y2_51_500_leaf s hs
  have a1 := ShiftGLeafY2b.Y2_1_5_leaf s hs
  have a2 := ShiftGLeafY2b.Y2_3_10_leaf s hs
  have a3 := ShiftGLeafY2b.Y2_2_5_leaf s hs
  have a4 := ShiftGLeafY2b.Y2_3_5_leaf s hs
  have a5 := ShiftGLeafY2b.Y2_4_5_leaf s hs
  have a6 := ShiftGLeafY2b.Y2_1_1_leaf s hs
  simp only [one_mul]
  unfold Y2fun
  split_ifs with c1 c2 c3 c4 c5
  · exact yI_seg (by norm_num) (T := barrierTrialT dvS s) a0 a1 h0 c1
  · exact yI_seg (by norm_num) (T := barrierTrialT dvS s) a1 a2 (by linarith) c2
  · exact yI_seg (by norm_num) (T := barrierTrialT dvS s) a2 a3 (by linarith) c3
  · exact yI_seg (by norm_num) (T := barrierTrialT dvS s) a3 a4 (by linarith) c4
  · exact yI_seg (by norm_num) (T := barrierTrialT dvS s) a4 a5 (by linarith) c5
  · exact yI_seg (by norm_num) (T := barrierTrialT dvS s) a5 (by simpa [dvS] using a6) (by linarith) h1

/-- The ray cap of the physical window of the near sheet: `ΔY = τ y(a₁)`, `τ = β / a₁`. -/
def Y2ray : ℝ := 13909310 / 10 ^ 8

theorem Y2ray_hY {β τ : ℝ} (hτ : 0 ≤ τ) (hβ : β = τ * (51 / 500)) :
    ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (τ * barrierTrialT dvS s) ≤ τ * Y2ray :=
  fun s hs => yRay (ShiftGLeafY2a.Y2_51_500_leaf s hs) hτ hβ

/-! ### The first-population column cap -/

/-- Column cap of the first sheet at `γ = β ∈ [11/50, 1]`, `τ = 1`. -/
def Y1fun (β : ℝ) : ℝ :=
  if β ≤ 3 / 10 then yI (11 / 50) (3 / 10) (14224759 / 10 ^ 8) (18683771 / 10 ^ 8) β
  else if β ≤ 2 / 5 then yI (3 / 10) (2 / 5) (18683771 / 10 ^ 8) (24277698 / 10 ^ 8) β
  else if β ≤ 3 / 5 then yI (2 / 5) (3 / 5) (24277698 / 10 ^ 8) (35470014 / 10 ^ 8) β
  else if β ≤ 4 / 5 then yI (3 / 5) (4 / 5) (35470014 / 10 ^ 8) (46662331 / 10 ^ 8) β
  else yI (4 / 5) 1 (46662331 / 10 ^ 8) (57854647 / 10 ^ 8) β

theorem Y1fun_hY {β : ℝ} (h0 : 11 / 50 ≤ β) (h1 : β ≤ 1) :
    ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (1 * barrierTrialT dvF s) ≤ Y1fun β := by
  intro s hs
  have a0 := ShiftGLeafY1a.Y1_11_50_leaf s hs
  have a1 := ShiftGLeafY1b.Y1_3_10_leaf s hs
  have a2 := ShiftGLeafY1b.Y1_2_5_leaf s hs
  have a3 := ShiftGLeafY1b.Y1_3_5_leaf s hs
  have a4 := ShiftGLeafY1b.Y1_4_5_leaf s hs
  have a5 := ShiftGLeafY1b.Y1_1_1_leaf s hs
  simp only [one_mul]
  unfold Y1fun
  split_ifs with c1 c2 c3 c4
  · exact yI_seg (by norm_num) (T := barrierTrialT dvF s) a0 a1 h0 c1
  · exact yI_seg (by norm_num) (T := barrierTrialT dvF s) a1 a2 (by linarith) c2
  · exact yI_seg (by norm_num) (T := barrierTrialT dvF s) a2 a3 (by linarith) c3
  · exact yI_seg (by norm_num) (T := barrierTrialT dvF s) a3 a4 (by linarith) c4
  · exact yI_seg (by norm_num) (T := barrierTrialT dvF s) a4 (by simpa [dvF] using a5) (by linarith) h1

/-- The ray cap of the physical window of the first sheet: `τ = β / (11/50)`. -/
def Y1ray : ℝ := 14224759 / 10 ^ 8

/-- The parameter of the first sheet: `τ = min (1, 50 β / 11)`. -/
def tau1 (β : ℝ) : ℝ := min 1 (β * 50 / 11)

/-- The column cap of the first sheet. -/
def Y1tot (β : ℝ) : ℝ := if β ≤ 11 / 50 then (β * 50 / 11) * Y1ray else Y1fun β

theorem tau1_mem {β : ℝ} (h : 0 ≤ β) : 0 ≤ tau1 β ∧ tau1 β ≤ 1 :=
  ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩

theorem Y1tot_hY {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (tau1 β * barrierTrialT dvF s) ≤ Y1tot β := by
  intro s hs
  unfold Y1tot
  split_ifs with hc
  · have ht : tau1 β = β * 50 / 11 := by
      unfold tau1
      exact min_eq_right (by linarith)
    rw [ht]
    exact yRay (ShiftGLeafY1a.Y1_11_50_leaf s hs) (by positivity) (by ring)
  · have ht : tau1 β = 1 := by
      unfold tau1
      exact min_eq_left (by linarith [not_le.mp hc])
    rw [ht]
    exact Y1fun_hY (by linarith [not_le.mp hc]) h1 s hs

/-! ### `LargeData` -/

theorem tQ_def : (tQ : ℝ) = 563964709 / 250000000 + (616 / 25) / 3364 := by
  unfold tQ; push_cast; norm_num

/-- **The large sheet from its cell data.**  Besides the cells and `hPoly`, the four hypotheses say that
the cap polynomials dominate the exact cap functions at every `β` of every cell. -/
def largeDataOf {κ : ℕ} (A B : Fin κ → ℚ) (hA0 : ∀ k, (51 / 500 : ℝ) ≤ A k) (hB1 : ∀ k, B k ≤ 1)
    (hAB : ∀ k, A k < B k)
    (hcov : ∀ α ∈ Icc (51 / 500 : ℝ) 1, ∃ k, (A k : ℝ) ≤ α ∧ α ≤ B k)
    (nC fC rs np : Fin κ → QP) (η : ℚ) (hη : 0 < η)
    (hPoly : ∀ k, PolyNonneg (wPq sigQ η 0 (nC k) (fC k) (rs k) (np k)) (A k) (B k))
    (hN : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k), normCap2 1 ≤ evalQ (nC k) β)
    (hF : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k), K590.fieldCap + 1 * X2cap + Y2fun β ≤ evalQ (fC k) β)
    (hr : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k), (7 / 1000 : ℝ) + 1 * (-268 / 10000 - 7 / 1000) ≤ evalQ (rs k) β)
    (hnp : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k), (7 / 1000 : ℝ) + 1 * (233 / 10000 - 7 / 1000) ≤ evalQ (np k) β) :
    LargeData where
  κ := κ
  A := A
  B := B
  hA0 := hA0
  hB1 := hB1
  hAB := hAB
  hcov := hcov
  nC := nC
  fC := fC
  rs := rs
  np := np
  η := η
  hη := hη
  hPoly := hPoly
  R := fun k β hβ => secondRec X2cap hX2 (tQ : ℝ) ((c2Q : ℝ) + sigQ) (evalQ (rs k) β)
    (evalQ (np k) β - Real.log 2) β 1 (Y2fun β) zero_le_one le_rfl
    (Y2fun_hY (le_trans (hA0 k) hβ.1) (le_trans hβ.2 (by exact_mod_cast hB1 k)))
    (hr k β hβ) (by linarith [hnp k β hβ])
  hN := fun k β hβ => hN k β hβ
  hF := fun k β hβ => hF k β hβ

/-! ### `FirstData` -/

/-- **The first sheet from its cell data.** -/
def firstDataOf {κ : ℕ} (A B : Fin κ → ℚ) (hA0 : ∀ k, 0 ≤ A k) (hB1 : ∀ k, B k ≤ 1)
    (hAB : ∀ k, A k < B k)
    (hcov : ∀ α ∈ Icc (0 : ℝ) 1, ∃ k, (A k : ℝ) ≤ α ∧ α ≤ B k)
    (nC fC rs : Fin κ → QP) (η : ℚ) (hη : 0 < η)
    (hPoly : ∀ k, PolyNonneg (wPq sigQ η 0 (nC k) (fC k) (rs k) (rs k)) (A k) (B k))
    (hN : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k), normCap1 (tau1 β) ≤ evalQ (nC k) β)
    (hF : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k), F1 + tau1 β * X1cap + Y1tot β ≤ evalQ (fC k) β)
    (hM : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k),
      (1 - tau1 β) * (35072 / 100000 : ℝ) + tau1 β * (35295 / 100000) ≤ evalQ (rs k) β) :
    FirstData where
  κ := κ
  A := A
  B := B
  hA0 := hA0
  hB1 := hB1
  hAB := hAB
  hcov := hcov
  nC := nC
  fC := fC
  rs := rs
  η := η
  hη := hη
  hPoly := hPoly
  R := fun k β hβ =>
    have hb0 : 0 ≤ β := le_trans (by exact_mod_cast hA0 k) hβ.1
    have hb1 : β ≤ 1 := le_trans hβ.2 (by exact_mod_cast hB1 k)
    firstRec X1cap hX1 (tQ : ℝ) ((c2Q : ℝ) + sigQ) (evalQ (rs k) β) β (tau1 β) (Y1tot β)
      (tau1_mem hb0).1 (tau1_mem hb0).2 (Y1tot_hY hb0 hb1) (hM k β hβ)
  hN := fun k β hβ => hN k β hβ
  hF := fun k β hβ => hF k β hβ
  hM := fun k β hβ => le_rfl

/-! ### The unsigned fields of `NearData` -/

/-- `τ = β / a₁` of the physical window. -/
def tauN (β : ℝ) : ℝ := β / (51 / 500)

/-- **The near-sheet record `Rp j β`** with the step constant `Δ`, the caps `rsf`, `npf` of `β` and
the cost `cost` (`c2Q + σ`). -/
def nearRp (Δ cost : ℝ) (rsf npf : ℝ → ℝ) (β : ℝ) (hβ : β ∈ Icc (0 : ℝ) (51 / 500))
    (hr : (7 / 1000 : ℝ) + tauN β * (-268 / 10000 - 7 / 1000) ≤ rsf β)
    (hnp : (7 / 1000 : ℝ) + tauN β * (233 / 10000 - 7 / 1000) ≤ npf β) :
    SecondTrialBoundsEnd P58 ∅ (colCell P58 (3 / 4) β) (nodeD P58 δc) ((tQ : ℝ) - Δ) (rsf β)
      (npf β - Real.log 2) cost Gd :=
  secondRec X2cap hX2 ((tQ : ℝ) - Δ) cost (rsf β) (npf β - Real.log 2) β (tauN β) (tauN β * Y2ray)
    (div_nonneg hβ.1 (by norm_num)) ((div_le_one (by norm_num)).mpr hβ.2)
    (Y2ray_hY (div_nonneg hβ.1 (by norm_num)) (by unfold tauN; field_simp)) hr (by linarith)

theorem nearRp_p (Δ cost : ℝ) (rsf npf : ℝ → ℝ) (β : ℝ) hβ hr hnp (k : ℕ) :
    (nearRp Δ cost rsf npf β hβ hr hnp).p k = base2.p k + tauN β * duS k := rfl

theorem nearRp_normCap (Δ cost : ℝ) (rsf npf : ℝ → ℝ) (β : ℝ) hβ hr hnp :
    (nearRp Δ cost rsf npf β hβ hr hnp).normCap = normCap2 (tauN β) := rfl

theorem nearRp_fieldCap (Δ cost : ℝ) (rsf npf : ℝ → ℝ) (β : ℝ) hβ hr hnp :
    (nearRp Δ cost rsf npf β hβ hr hnp).fieldCap = K590.fieldCap + tauN β * X2cap + tauN β * Y2ray := rfl

/-- The exact sum `Σ_{k<32} testF(k+1) du(k+1)`. -/
def FUex : ℚ := ((List.range 32).map fun k =>
  ((Cl.getD (k + 1) 0 : ℚ) / 2 ^ 31) * ((du40.getD k 0 : ℚ) / 2 ^ 24)).sum

theorem a1Q_real : (a1Q : ℝ) = 51 / 500 := by unfold a1Q; push_cast; norm_num

theorem testSum_du : ∑' k : ℕ, testF (k + 1) * duS (k + 1) = (FUex : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range 32)]
  · unfold FUex
    rw [lsum_range]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold testF duS
    rw [trialSeqOf_succ, if_neg (Nat.succ_ne_zero k)]
    push_cast
    ring
  · intro k hk
    have : 32 ≤ k := by simpa using hk
    rw [testF_zero (by omega)]
    simp

theorem hSp_of {Δ cost : ℝ} {rsf npf : ℝ → ℝ} {β : ℝ} {hβ hr hnp} (U FU : ℚ)
    (hU : (U : ℝ) ≤ 879 / 10000) (hFU : (FU : ℝ) ≤ FUex) :
    (U : ℝ) + (β / (a1Q : ℝ)) * FU ≤
      ∑' k : ℕ, testT.F (k + 1) * (nearRp Δ cost rsf npf β hβ hr hnp).p (k + 1) := by
  have hτ : 0 ≤ tauN β := div_nonneg hβ.1 (by norm_num)
  have hs0 : ∀ f : ℕ → ℝ, Summable (fun k : ℕ => testF (k + 1) * f (k + 1)) := fun f =>
    summable_of_ne_finset_zero (s := Finset.range 32) fun k hk => by
      have : 32 ≤ k := by simpa using hk
      rw [testF_zero (by omega)]
      simp
  have e1 : ∑' k : ℕ, testT.F (k + 1) * (nearRp Δ cost rsf npf β hβ hr hnp).p (k + 1) =
      ∑' k : ℕ, testF (k + 1) * trialSeqS Cert590.Pc Cert590.P (k + 1) +
        tauN β * ∑' k : ℕ, testF (k + 1) * duS (k + 1) := by
    rw [← tsum_mul_left, ← (hs0 _).tsum_add ((hs0 _).mul_left _)]
    refine tsum_congr fun k => ?_
    show testF (k + 1) * (base2.p (k + 1) + tauN β * duS (k + 1)) = _
    rw [base2_p]
    ring
  rw [e1, testSum_du]
  have h1 := U_lower
  have h2 : (β / (a1Q : ℝ)) = tauN β := by rw [a1Q_real]; rfl
  rw [h2]
  have h3 : tauN β * (FU : ℝ) ≤ tauN β * FUex := mul_le_mul_of_nonneg_left hFU hτ
  linarith

theorem hp2p_of {Δ cost : ℝ} {rsf npf : ℝ → ℝ} {β : ℝ} {hβ hr hnp} (p2 du2 : ℚ)
    (hp2 : (p2 : ℝ) ≤ -187 / 1000) (hdu : (du2 : ℝ) ≤ (du40.getD 1 0 : ℝ) / 2 ^ 24) :
    (p2 : ℝ) + (β / (a1Q : ℝ)) * du2 ≤ (nearRp Δ cost rsf npf β hβ hr hnp).p 2 := by
  have hτ : 0 ≤ tauN β := div_nonneg hβ.1 (by norm_num)
  have h2 : (β / (a1Q : ℝ)) = tauN β := by rw [a1Q_real]; rfl
  have hd2 : duS 2 = (du40.getD 1 0 : ℝ) / 2 ^ 24 := by
    unfold duS
    exact (trialSeqOf_succ du40 (2 ^ 24) 1).trans (by push_cast; ring)
  rw [h2, nearRp_p, base2_p]
  have h3 := u2_lower
  have h4 : tauN β * (du2 : ℝ) ≤ tauN β * ((du40.getD 1 0 : ℝ) / 2 ^ 24) := mul_le_mul_of_nonneg_left hdu hτ
  rw [hd2]
  linarith

end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGAsm

#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGAsm.largeDataOf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGAsm.firstDataOf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGAsm.nearRp
