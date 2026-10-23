module
public import CatalanMeasure.G728.Cover
@[expose] public section
/-! # Cell checks as small pieces with literal witnesses (G728)

The monolithic `cellVal ... = true` is replaced, per cell, by independent small kernel theorems:
`evLe` (centre enclosure `v + e ≤ U`), `fhL = FH`, `AL = AA`, `MpoleV = Mp`, and `cellFin` (guards and the final
integer inequality on the literal witnesses).  `cellVal_of_pieces` assembles them. -/
namespace CatalanMeasure.G728
open Set Nat CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000

/-- the floored scaled derivative levels `0 .. m-1` at the centre -/
def fhL (N : ℕ) (poles : List PoleR) (cc : ℤ) (V : List ℤ) (m : ℕ) : List ℤ :=
  (List.range m).map (fhatV N poles cc V)

/-- `|SC * P^(m+k)(c)| ≤ A_k` -/
def AL (N : ℕ) (V : List ℤ) (m L : ℕ) : List ℤ :=
  (List.range L).map (fun k => zabs (V.getD (m + k) 0 * SC / (K40 * TPN N)) + 1)

def BsumF (E hh : ℤ) (FH : List ℤ) (m : ℕ) : ℤ :=
  ((List.range m).map (fun j =>
    cdiv ((zabs (FH.getD j 0) + E) * zpw hh (j + 1)) (tf (j + 1)))).sum

def PbF (AA : List ℤ) (hh : ℤ) (L : ℕ) (MGL : ℤ) : ℤ :=
  ((List.range L).map (fun k => cdiv (AA.getD k 0 * zpw hh k) (tf k))).sum +
    cdiv (MGL * zpw hh L) (tf L)

def evLe (ev : ℚ → Option (ℚ × ℚ)) (c U : ℚ) : Bool :=
  match ev c with
  | none => false
  | some ve => decide (ve.1 + ve.2 ≤ U)

/-- guards and the final inequality, on literal witnesses only -/
def cellFin (D : PolyData) (poles : List PoleR) (m L : ℕ) (MGL : ℤ) (pe : Option ℚ) (cap : ℚ)
    (cell : ℤ × ℤ) (U : ℚ) (FH AA : List ℤ) (Mp : ℤ) : Bool :=
  let cc := cell.1
  let hh := cell.2
  let lo : ℚ := ((cc - hh : ℤ) : ℚ) / (TT : ℚ)
  let hi : ℚ := ((cc + hh : ℤ) : ℚ) / (TT : ℚ)
  decide (m + L ≤ D.LV.length) && decide (0 ≤ hh) &&
      decide (-TT ≤ cc - hh) && decide (cc + hh ≤ TT) && peOK pe lo hi &&
      poles.all (fun q => decide (0 < poleDl q lo hi)) &&
      decide (qceil (SC * U) + BsumF (EcntV poles) hh FH m +
        cdiv ((Mp + PbF AA hh L MGL) * zpw hh (m + 1)) (tf (m + 1)) ≤ qfloor (SC * cap))

theorem qceil_mono {a b : ℚ} (h : a ≤ b) : qceil a ≤ qceil b := by
  have h1 := qceil_lt_add_one a
  have h2 := le_qceil b
  have : ((qceil a : ℤ) : ℚ) < ((qceil b : ℤ) : ℚ) + 1 := by linarith
  have : qceil a < qceil b + 1 := by exact_mod_cast this
  omega

theorem BsumV_eq (N : ℕ) (poles : List PoleR) (cc hh : ℤ) (V FH : List ℤ) (m : ℕ)
    (h : fhL N poles cc V m = FH) : BsumV N poles cc hh V m = BsumF (EcntV poles) hh FH m := by
  unfold BsumV BsumF
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [← h]
  unfold fhL
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]

theorem PbV_eq (N : ℕ) (cc hh : ℤ) (V AA : List ℤ) (m L : ℕ) (MGL : ℤ)
    (h : AL N V m L = AA) : PbV N cc hh V m L MGL = PbF AA hh L MGL := by
  unfold PbV PbF
  congr 2
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [← h]
  unfold AL
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hk]

theorem cellVal_of_pieces (ev : ℚ → Option (ℚ × ℚ)) (D : PolyData) (poles : List PoleR)
    (m L : ℕ) (MGL : ℤ) (pe : Option ℚ) (cap : ℚ) (cc hh : ℤ) (U : ℚ) (FH AA : List ℤ) (Mp : ℤ)
    (hev : evLe ev ((cc : ℚ) / (TT : ℚ)) U = true)
    (hfh : fhL D.N poles cc (polyValsD D cc (m + L)) m = FH)
    (hA : AL D.N (polyValsD D cc (m + L)) m L = AA)
    (hMp : MpoleV poles m (((cc - hh : ℤ) : ℚ) / (TT : ℚ)) (((cc + hh : ℤ) : ℚ) / (TT : ℚ)) = Mp)
    (hfin : cellFin D poles m L MGL pe cap (cc, hh) U FH AA Mp = true) :
    cellVal ev D poles m L MGL pe cap (cc, hh) = true := by
  unfold evLe at hev
  unfold cellFin at hfin
  unfold cellVal
  simp only at hfin ⊢
  rcases hc : ev ((cc : ℚ) / (TT : ℚ)) with _ | ve
  · rw [hc] at hev; simp at hev
  · rw [hc] at hev
    simp only [decide_eq_true_eq] at hev
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hfin ⊢
    obtain ⟨⟨⟨⟨⟨⟨hm, hh0⟩, hlow⟩, hhigh⟩, hpe⟩, hpos⟩, hineq⟩ := hfin
    refine ⟨⟨⟨⟨⟨⟨hm, hh0⟩, hlow⟩, hhigh⟩, hpe⟩, hpos⟩, ?_⟩
    rw [BsumV_eq _ _ _ _ _ _ _ hfh, PbV_eq _ _ _ _ _ _ _ _ hA, hMp]
    have hq : qceil (SC * (ve.1 + ve.2)) ≤ qceil (SC * U) := by
      apply qceil_mono
      have : (0 : ℚ) ≤ SC := by have := SC_pos; exact_mod_cast this.le
      exact mul_le_mul_of_nonneg_left hev this
    omega

theorem cellValP_none_of (ev : ℚ → Option (ℚ × ℚ)) (D : PolyData) (poles : List PoleR)
    (m L : ℕ) (MGL : ℤ) (cap : ℚ) (cell : ℤ × ℤ)
    (h : cellVal ev D poles m L MGL none cap cell = true) :
    cellValP ev D poles m L MGL none cap cell = true := h

theorem cellValP_some_of (ev : ℚ → Option (ℚ × ℚ)) (D : PolyData) (poles : List PoleR)
    (m L : ℕ) (MGL : ℤ) (w p cap u : ℚ) (cc hh : ℤ)
    (hpb : peelBound w p (((cc - hh : ℤ) : ℚ) / (TT : ℚ)) (((cc + hh : ℤ) : ℚ) / (TT : ℚ)) = some u)
    (h : cellVal ev D poles m L MGL (some p) (cap - u) (cc, hh) = true) :
    cellValP ev D poles m L MGL (some (w, p)) cap (cc, hh) = true := by
  unfold cellValP
  simp only
  rw [hpb]
  exact h

end CatalanMeasure.G728
