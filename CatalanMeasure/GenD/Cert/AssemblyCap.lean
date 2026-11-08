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

end CatalanMeasure.CellCert
#print axioms CatalanMeasure.CellCert.field_le_of_blocks_cap
#print axioms CatalanMeasure.CellCert.field_add_le_of_blocks_cap
