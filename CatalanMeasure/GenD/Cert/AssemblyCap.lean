module

public import CatalanMeasure.GenD.Cert.Assembly

@[expose] public section

namespace CatalanMeasure.CellCert
open Set Nat CatalanMeasure.Cert
set_option maxRecDepth 100000

/-- **Pointwise sup from blocks with one cap per block** (G32a).  `capOf b` is the cap of block `b`;
the conclusion records the block `b` whose range contains `x`, so a block-constant bound of a second
term (the chord `δ̂/58`, the trial term) can be added. -/
theorem field_le_of_blocks_cap (F : ℝ → ℝ) (S : ℕ → Spec) (D : PolyData) (hD : D.Ok) (m LT : ℕ) (MGL : ℤ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + LT) y| ≤ (MGL : ℝ)) (capOf : Block → ℚ)
    (bs : List Block) (hsound : ∀ c ∈ blocksCells bs, (S c.2.2).Sound D F)
    (L0 : ℤ) (ghi : ℚ) (hcov : coverFrom ghi L0 (blocksCells bs) = true)
    (hbs : ∀ b ∈ bs, blockOK S D m LT MGL (capOf b) b = true)
    (x : ℝ) (hL : (L0 : ℝ) / TT ≤ x) (hx : x ≤ (ghi : ℝ))
    (hxp : ∀ c ∈ blocksCells bs, ∀ pr, (S c.2.2).peel = some pr → x ≠ (pr.2 : ℝ)) :
    ∃ b ∈ bs, |x - (b.cB : ℝ) / TT| ≤ (b.HB : ℝ) / TT ∧ F x ≤ (capOf b : ℝ) := by
  obtain ⟨c, hc, hcx⟩ := cover_spec ghi (blocksCells bs) L0 hcov x hL hx
  obtain ⟨b, hbmem, hcb⟩ := List.mem_flatMap.mp hc
  obtain ⟨hct, hloc⟩ := blockOK_cell S D hD m LT MGL (capOf b) hMGL b (hbs b hbmem) c hcb
  refine ⟨b, hbmem, ?_, cellValP_soundL F (S c.2.2) D hD m b.L b.BB (hsound c hc) (capOf b) c.1 c.2.1
    hloc hct x hcx (hxp c hc)⟩
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  have hcell : |(c.1 : ℝ) - b.cB| + c.2.1 ≤ b.HB := by
    have := (by
      have h := hbs b hbmem
      unfold blockOK at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
      exact (h.2 c hcb).1 : |c.1 - b.cB| + c.2.1 ≤ b.HB)
    exact_mod_cast this
  have h1 : |x - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT := hcx
  have h2 : |(c.1 : ℝ) / TT - (b.cB : ℝ) / TT| = |(c.1 : ℝ) - b.cB| / TT := by
    rw [← sub_div, abs_div, abs_of_pos hT]
  have h3 : |x - (b.cB : ℝ) / TT| ≤ |x - (c.1 : ℝ) / TT| + |(c.1 : ℝ) / TT - (b.cB : ℝ) / TT| := by
    have := abs_add_le (x - (c.1 : ℝ) / TT) ((c.1 : ℝ) / TT - (b.cB : ℝ) / TT)
    simpa using this
  rw [h2] at h3
  have h4 : |(c.1 : ℝ) - b.cB| / TT + (c.2.1 : ℝ) / TT ≤ (b.HB : ℝ) / TT := by
    rw [← add_div]; exact div_le_div_of_nonneg_right hcell hT.le
  linarith

/-- the block-wise sum: `F x + δ x ≤ res` when every block has `capOf b + dOf b ≤ res` and `δ ≤ dOf b`
on the range of `b`. -/
theorem field_add_le_of_blocks_cap (F δ : ℝ → ℝ) (S : ℕ → Spec) (D : PolyData) (hD : D.Ok) (m LT : ℕ)
    (MGL : ℤ) (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + LT) y| ≤ (MGL : ℝ))
    (capOf dOf : Block → ℚ) (res : ℝ)
    (bs : List Block) (hsound : ∀ c ∈ blocksCells bs, (S c.2.2).Sound D F)
    (L0 : ℤ) (ghi : ℚ) (hcov : coverFrom ghi L0 (blocksCells bs) = true)
    (hbs : ∀ b ∈ bs, blockOK S D m LT MGL (capOf b) b = true)
    (hd : ∀ b ∈ bs, ∀ y : ℝ, |y - (b.cB : ℝ) / TT| ≤ (b.HB : ℝ) / TT → δ y ≤ (dOf b : ℝ))
    (hr : ∀ b ∈ bs, (capOf b : ℝ) + (dOf b : ℝ) ≤ res)
    (x : ℝ) (hL : (L0 : ℝ) / TT ≤ x) (hx : x ≤ (ghi : ℝ))
    (hxp : ∀ c ∈ blocksCells bs, ∀ pr, (S c.2.2).peel = some pr → x ≠ (pr.2 : ℝ)) :
    F x + δ x ≤ res := by
  obtain ⟨b, hb, hrange, hF⟩ :=
    field_le_of_blocks_cap F S D hD m LT MGL hMGL capOf bs hsound L0 ghi hcov hbs x hL hx hxp
  have := hd b hb x hrange
  have := hr b hb
  linarith

/-! ### One cap per CELL (G32a, per-cell variant)

The cap `capC c` of a cell `c` is chosen per cell (the chord maximum and the trial-term lower bound vary
across a block).  `blockOKc` is `blockOK` of the singleton blocks, so the data-side assembly is
`blockOKc_ofS` with the unchanged block tower proof and a per-cell `cellT` list. -/

def blockOKc (S : ℕ → Spec) (D : PolyData) (m LT : ℕ) (MGL : ℤ) (capC : TCell → ℚ) (b : Block) : Bool :=
  b.cells.all (fun c => blockOK S D m LT MGL (capC c) { b with cells := [c] })

theorem blockOKc_ofS (S : ℕ → Spec) (D : PolyDataS) (m LT : ℕ) (MGL : ℤ) (capC : TCell → ℚ) (b : Block)
    (hL : b.L ≤ LT) (hlv : m + LT ≤ D.LV.length) (hH : 0 ≤ b.HB) (hlow : -TT ≤ b.cB - b.HB)
    (hhigh : b.cB + b.HB ≤ TT)
    (hPb : decide (PbV D.N b.cB b.HB (polyValsS D b.cB (m + LT)) (m + b.L) (LT - b.L) MGL ≤ b.BB) = true)
    (hcells : ∀ c ∈ b.cells, |c.1 - b.cB| + c.2.1 ≤ b.HB ∧ cellT S D.toD m b.L b.BB (capC c) c = true) :
    blockOKc S D.toD m LT MGL capC b = true := by
  unfold blockOKc
  rw [List.all_eq_true]
  intro c hc
  refine blockOK_ofS S D m LT MGL (capC c) { b with cells := [c] } hL hlv hH hlow hhigh hPb ?_
  intro c' hc'
  have : c' = c := by simpa using hc'
  subst this
  exact hcells c' hc

theorem blockOKc_cell (S : ℕ → Spec) (D : PolyData) (hD : D.Ok) (m LT : ℕ) (MGL : ℤ) (capC : TCell → ℚ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + LT) y| ≤ (MGL : ℝ))
    (b : Block) (hb : blockOKc S D m LT MGL capC b = true) (c : TCell) (hc : c ∈ b.cells) :
    cellT S D m b.L b.BB (capC c) c = true ∧
    ∀ y : ℝ, |y - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT →
      (SC : ℝ) * |ptZ D.Z (m + b.L) y| ≤ (b.BB : ℝ) := by
  unfold blockOKc at hb
  rw [List.all_eq_true] at hb
  exact blockOK_cell S D hD m LT MGL (capC c) hMGL { b with cells := [c] } (hb c hc) c (List.mem_singleton_self c)

/-- **Pointwise sup with one cap per cell.** -/
theorem field_le_of_blocks_capc (F : ℝ → ℝ) (S : ℕ → Spec) (D : PolyData) (hD : D.Ok) (m LT : ℕ) (MGL : ℤ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + LT) y| ≤ (MGL : ℝ)) (capC : TCell → ℚ)
    (bs : List Block) (hsound : ∀ c ∈ blocksCells bs, (S c.2.2).Sound D F)
    (L0 : ℤ) (ghi : ℚ) (hcov : coverFrom ghi L0 (blocksCells bs) = true)
    (hbs : ∀ b ∈ bs, blockOKc S D m LT MGL capC b = true)
    (x : ℝ) (hL : (L0 : ℝ) / TT ≤ x) (hx : x ≤ (ghi : ℝ))
    (hxp : ∀ c ∈ blocksCells bs, ∀ pr, (S c.2.2).peel = some pr → x ≠ (pr.2 : ℝ)) :
    ∃ c ∈ blocksCells bs, |x - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT ∧ F x ≤ (capC c : ℝ) := by
  obtain ⟨c, hc, hcx⟩ := cover_spec ghi (blocksCells bs) L0 hcov x hL hx
  obtain ⟨b, hbmem, hcb⟩ := List.mem_flatMap.mp hc
  obtain ⟨hct, hloc⟩ := blockOKc_cell S D hD m LT MGL capC hMGL b (hbs b hbmem) c hcb
  exact ⟨c, hc, hcx, cellValP_soundL F (S c.2.2) D hD m b.L b.BB (hsound c hc) (capC c) c.1 c.2.1
    hloc hct x hcx (hxp c hc)⟩

/-- the sum with a second term bounded cell-wise: `F x + δ x ≤ res` when `capC c + ddC c ≤ res` and
`δ ≤ ddC c` on each cell. -/
theorem field_add_le_of_blocks_capc (F δ : ℝ → ℝ) (S : ℕ → Spec) (D : PolyData) (hD : D.Ok) (m LT : ℕ)
    (MGL : ℤ) (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + LT) y| ≤ (MGL : ℝ))
    (capC ddC : TCell → ℚ) (res : ℝ)
    (bs : List Block) (hsound : ∀ c ∈ blocksCells bs, (S c.2.2).Sound D F)
    (L0 : ℤ) (ghi : ℚ) (hcov : coverFrom ghi L0 (blocksCells bs) = true)
    (hbs : ∀ b ∈ bs, blockOKc S D m LT MGL capC b = true)
    (hd : ∀ c ∈ blocksCells bs, ∀ y : ℝ, |y - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT → δ y ≤ (ddC c : ℝ))
    (hr : ∀ c ∈ blocksCells bs, (capC c : ℝ) + (ddC c : ℝ) ≤ res)
    (x : ℝ) (hL : (L0 : ℝ) / TT ≤ x) (hx : x ≤ (ghi : ℝ))
    (hxp : ∀ c ∈ blocksCells bs, ∀ pr, (S c.2.2).peel = some pr → x ≠ (pr.2 : ℝ)) :
    F x + δ x ≤ res := by
  obtain ⟨c, hc, hrange, hF⟩ :=
    field_le_of_blocks_capc F S D hD m LT MGL hMGL capC bs hsound L0 ghi hcov hbs x hL hx hxp
  have := hd c hc x hrange
  have := hr c hc
  linarith

/-! ### `cellFin` is monotone in the cap

The cap enters `cellFin` only in the last inequality `... ≤ qfloor (SC * cap)`, so one check at the smaller
of two caps serves both. -/

theorem qfloor_mono {a b : ℚ} (h : a ≤ b) : qfloor a ≤ qfloor b := by
  have h1 := qfloor_le a
  have h2 := lt_qfloor_add_one b
  have h3 : ((qfloor a : ℤ) : ℚ) < ((qfloor b : ℤ) : ℚ) + 1 := by linarith
  have h4 : qfloor a < qfloor b + 1 := by exact_mod_cast h3
  omega

theorem cellFin_mono {D : PolyData} {poles : List PoleR} {m L : ℕ} {MGL : ℤ} {pe : Option ℚ} {cap cap' : ℚ}
    {cell : ℤ × ℤ} {U : ℚ} {FH AA : List ℤ} {Mp : ℤ} (h : cap ≤ cap')
    (hf : cellFin D poles m L MGL pe cap cell U FH AA Mp = true) :
    cellFin D poles m L MGL pe cap' cell U FH AA Mp = true := by
  unfold cellFin at hf ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
  refine ⟨hf.1, le_trans hf.2 (qfloor_mono ?_)⟩
  have hSC : (0 : ℚ) ≤ (SC : ℚ) := by unfold SC; positivity
  exact mul_le_mul_of_nonneg_left h hSC

end CatalanMeasure.CellCert
#print axioms CatalanMeasure.CellCert.field_le_of_blocks_cap
#print axioms CatalanMeasure.CellCert.field_add_le_of_blocks_cap
#print axioms CatalanMeasure.CellCert.field_le_of_blocks_capc
#print axioms CatalanMeasure.CellCert.field_add_le_of_blocks_capc
#print axioms CatalanMeasure.CellCert.cellFin_mono
