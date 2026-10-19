module

public import CatalanFrames.LambdaHybrid.NV.Entries
public import CatalanFrames.LambdaHybrid.NV.Schur
public import CatalanCore.Rect.Geometry
public import CatalanCore.NV.ModL

/-!
# The mod-`ℓ` reduction of `Full(x)` for a hybrid geometry (DO Prop 1.3, instance level)
-/

@[expose] public section

open Finset CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

open CatalanFrames.Lambda

section Setup

variable {ℓ K : ℕ} [Fact ℓ.Prime] (G : Geometry)

/-- the high common nodes -/
abbrev HiC (K : ℕ) (G : Geometry) := {b : G.C // ¬ (b : ℕ) < K}

/-- `Cauchy` column of the node `n`, indexed by the low nodes `a < K`: `1/(a - n)` in `𝔽_ℓ`. -/
noncomputable def Wnode (ℓ K : ℕ) [Fact ℓ.Prime] (n : ℕ) : Fin K → ZMod ℓ :=
  fun a => 1 / (((a : ℕ) : ZMod ℓ) - (n : ZMod ℓ))

/-- low block `A = (cc δ + G)/16` -/
noncomputable def Alow (ℓ K : ℕ) [Fact ℓ.Prime] : Matrix (Fin K) (Fin K) (ZMod ℓ) :=
  Matrix.of fun a b => ((if a = b then CatalanLambda.cc ℓ K else 0) +
    CatalanLambda.G ℓ K a b) / 16

noncomputable def WC (ℓ K : ℕ) [Fact ℓ.Prime] (G : Geometry) : Matrix (Fin K) (HiC K G) (ZMod ℓ) :=
  Matrix.of fun a b => Wnode ℓ K (b.1 : ℕ) a

noncomputable def WX (ℓ K : ℕ) [Fact ℓ.Prime] (G : Geometry) : Matrix (Fin K) (Fin G.k) (ZMod ℓ) :=
  Matrix.of fun a i => Wnode ℓ K (G.xs i) a

noncomputable def WY (ℓ K : ℕ) [Fact ℓ.Prime] (G : Geometry) : Matrix (Fin K) (Fin G.k) (ZMod ℓ) :=
  Matrix.of fun a i => Wnode ℓ K (G.ys i) a

/-- the low common nodes are `Fin K` -/
def eLow (K : ℕ) (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C) :
    Fin K ≃ {b : G.C // (b : ℕ) < K} where
  toFun a := ⟨⟨a, hlow a a.2⟩, a.2⟩
  invFun b := ⟨b.1.1, b.2⟩
  left_inv a := rfl
  right_inv b := rfl

def eIdx (K : ℕ) (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C) :
    (Fin K ⊕ HiC K G) ⊕ Fin G.k ≃ G.C ⊕ Fin G.k :=
  Equiv.sumCongr ((Equiv.sumCongr (eLow K G hlow) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun b : G.C => (b : ℕ) < K))) (Equiv.refl _)


end Setup

section Entries

lemma full_ll (G : Geometry) (x : ℚ) (a b : G.C) :
    G.Full lamFrame x (Sum.inl a) (Sum.inl b) =
      (if a = b then x else 0) + CatalanLambda.M0n a b := by
  simp [Geometry.Full, FullN, Blk, blkA, Matrix.one_apply, Mn_eq, add_comm]

lemma full_lr (G : Geometry) (x : ℚ) (a : G.C) (j : Fin G.k) :
    G.Full lamFrame x (Sum.inl a) (Sum.inr j) = 0 + CatalanLambda.M0n a (G.ys j) := by
  simp [Geometry.Full, FullN, Blk, blkB, Mn_eq]

lemma full_rl (G : Geometry) (x : ℚ) (i : Fin G.k) (b : G.C) :
    G.Full lamFrame x (Sum.inr i) (Sum.inl b) = 0 + CatalanLambda.M0n (G.xs i) b := by
  simp [Geometry.Full, FullN, Blk, blkC, Mn_eq]

lemma full_rr (G : Geometry) (x : ℚ) (i j : Fin G.k) :
    G.Full lamFrame x (Sum.inr i) (Sum.inr j) = 0 + CatalanLambda.M0n (G.xs i) (G.ys j) := by
  simp [Geometry.Full, FullN, Blk, blkD, Mn_eq]


end Entries

section YGood

variable {ℓ K : ℕ} [Fact ℓ.Prime]

lemma inv_flip {F : Type*} [Field F] (u v : F) :
    (v - u)⁻¹ * 4⁻¹ = -(4⁻¹ * (u - v)⁻¹) := by
  rw [← neg_sub v u, inv_neg]; ring

lemma cauchy_flip {F : Type*} [Field F] (u v : F) :
    -(1 / 4 : F) * (1 / (u - v)) = -(-(1 / (4 * (v - u)))) := by
  by_cases h : v - u = 0
  · have h' : u - v = 0 := by rw [← neg_sub, h, neg_zero]
    simp [h, h']
  · have h' : u - v = -(v - u) := by ring
    rw [h']
    field_simp

/-- row node / column node of the `FullN` index. -/
noncomputable def rn (G : Geometry) : G.C ⊕ Fin G.k → ℕ := Sum.elim (fun a : G.C => (a : ℕ)) G.xs
noncomputable def cn (G : Geometry) : G.C ⊕ Fin G.k → ℕ := Sum.elim (fun a : G.C => (a : ℕ)) G.ys

/-- the negated, `D`-scaled hybrid matrix. -/
noncomputable def Ncell (ℓ K : ℕ) (G : Geometry) (x : ℚ) :
    Matrix (G.C ⊕ Fin G.k) (G.C ⊕ Fin G.k) ℚ :=
  Matrix.of fun i j => -(CatalanLambda.Dq ℓ K (rn G i) * CatalanLambda.Dq ℓ K (cn G j) *
    G.Full lamFrame x i j)

lemma xs_mem (G : Geometry) (i : Fin G.k) : G.xs i ∈ G.X' := Finset.orderEmbOfFin_mem _ _ _
lemma ys_mem (G : Geometry) (i : Fin G.k) : G.ys i ∈ G.Y' := Finset.orderEmbOfFin_mem _ _ _

theorem y_good (hlK : ℓ + 1 = 4 * K) (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < ℓ)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {x : ℚ} {xb : ZMod ℓ} (hx : Good ℓ x xb) (i j : (Fin K ⊕ HiC K G) ⊕ Fin G.k) :
    Good ℓ (Ncell ℓ K G x (eIdx K G hlow i) (eIdx K G hlow j))
      (Zmat (-xb) (Alow ℓ K) (WC ℓ K G) (WX ℓ K G) (WY ℓ K G) i j) := by
  have h4 := CatalanLambda.four_ne (ℓ := ℓ) hlK
  have hKl : K ≤ ℓ := by omega
  have hxsK : ∀ i : Fin G.k, K ≤ G.xs i ∧ G.xs i < ℓ := fun i =>
    ⟨hhi _ (Or.inl (xs_mem G i)), hlt _ (Or.inr (Or.inl (xs_mem G i)))⟩
  have hysK : ∀ i : Fin G.k, K ≤ G.ys i ∧ G.ys i < ℓ := fun i =>
    ⟨hhi _ (Or.inr (ys_mem G i)), hlt _ (Or.inr (Or.inr (ys_mem G i)))⟩
  have hCl : ∀ b : G.C, (b : ℕ) < ℓ := fun b => hlt _ (Or.inl b.2)
  have hCxs : ∀ (b : G.C) (i : Fin G.k), (b : ℕ) ≠ G.xs i := fun b i h =>
    Finset.disjoint_left.1 G.disjCX b.2 (h ▸ xs_mem G i)
  have hCys : ∀ (b : G.C) (i : Fin G.k), (b : ℕ) ≠ G.ys i := fun b i h =>
    Finset.disjoint_left.1 G.disjCY b.2 (h ▸ ys_mem G i)
  have hxy : ∀ i j : Fin G.k, G.xs i ≠ G.ys j := fun i j h =>
    Finset.disjoint_left.1 G.disjXY (xs_mem G i) (h ▸ ys_mem G j)
  have hdiff : ∀ {u v : ℕ}, u < K → K ≤ v → v < ℓ → (v : ZMod ℓ) - u ≠ 0 := fun {u v} hu hv hvl =>
    sub_ne_zero.2 (CatalanCore.natCast_ne_natCast hvl (by omega) (by omega))
  rcases i with (a | b) | i <;> rcases j with (a' | b') | j
  · -- low / low
    have ha := a.2
    have ha' := a'.2
    have he : Good ℓ (if (a : ℕ) = a' then x else 0) (if (a : ℕ) = a' then xb else 0) := by
      split_ifs
      · exact hx
      · exact Good.zero
    have hg := (node_ll hlK ha ha' he).neg
    have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inl a)))
        (eIdx K G hlow (Sum.inl (Sum.inl a'))) = -(CatalanLambda.Dq ℓ K a * CatalanLambda.Dq ℓ K a' *
          ((if (a : ℕ) = a' then x else 0) + CatalanLambda.M0n a a')) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_ll, Fin.ext_iff]
    rw [hN]
    refine hg.congr ?_
    by_cases haa : a = a'
    · subst haa; simp [Zmat, Alow]; ring
    · have : (a : ℕ) ≠ a' := fun h => haa (Fin.ext h)
      simp [Zmat, Alow, haa, this]
  · -- low / high common
    have ha := a.2
    have hb : K ≤ (b' : G.C).1 := by have := b'.2; omega
    have hbl := hCl b'.1
    have hne : (a : ℕ) ≠ (b'.1 : ℕ) := by omega
    have hg := (node_lh hlK ha hb hbl).neg
    have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inl a)))
        (eIdx K G hlow (Sum.inl (Sum.inr b'))) = -(CatalanLambda.Dq ℓ K a *
          CatalanLambda.Dq ℓ K b'.1.1 * (0 + CatalanLambda.M0n a b'.1.1)) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_ll, Subtype.ext_iff, hne]
    rw [hN]
    refine hg.congr ?_
    simp only [Zmat, WC, Wnode]
    simp
    first | exact inv_flip _ _ | (rw [← neg_sub]; simp [inv_neg]; ring)
  · -- low / Y'
    have ha := a.2
    have hg := (node_lh hlK ha (hysK j).1 (hysK j).2).neg
    have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inl a)))
        (eIdx K G hlow (Sum.inr j)) = -(CatalanLambda.Dq ℓ K a *
          CatalanLambda.Dq ℓ K (G.ys j) * (0 + CatalanLambda.M0n a (G.ys j))) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_lr]
    rw [hN]
    refine hg.congr ?_
    simp only [Zmat, WY, Wnode]
    simp
    first | exact inv_flip _ _ | (rw [← neg_sub]; simp [inv_neg]; ring)
  · -- high common / low
    have ha := a'.2
    have hb : K ≤ (b : G.C).1 := by have := b.2; omega
    have hbl := hCl b.1
    have hne : (b.1 : ℕ) ≠ (a' : ℕ) := by omega
    have hg := (node_hl hlK hb hbl ha).neg
    have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inr b)))
        (eIdx K G hlow (Sum.inl (Sum.inl a'))) = -(CatalanLambda.Dq ℓ K b.1.1 *
          CatalanLambda.Dq ℓ K a' * (0 + CatalanLambda.M0n b.1.1 a')) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_ll, Subtype.ext_iff, hne]
    rw [hN]
    refine hg.congr ?_
    simp only [Zmat, WC, Wnode]
    simp
    first | exact inv_flip _ _ | (rw [← neg_sub]; simp [inv_neg]; ring)
  · -- high common / high common
    have hb : K ≤ (b : G.C).1 := by have := b.2; omega
    have hb' : K ≤ (b' : G.C).1 := by have := b'.2; omega
    by_cases hbb : b = b'
    · subst hbb
      have hg := (node_hh_diag hlK hb (hCl b.1) hx).neg
      have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inr b)))
          (eIdx K G hlow (Sum.inl (Sum.inr b))) = -(CatalanLambda.Dq ℓ K b.1.1 *
            CatalanLambda.Dq ℓ K b.1.1 * (x + CatalanLambda.M0n b.1.1 b.1.1)) := by
        simp [Ncell, eIdx, rn, cn, full_ll]
      rw [hN]
      refine hg.congr ?_
      simp [Zmat]
    · have hne : (b.1 : ℕ) ≠ (b'.1 : ℕ) := fun h => hbb (Subtype.ext (Subtype.ext h))
      have hg := (node_hh_off hlK hb (hCl b.1) hb' (hCl b'.1) hne).neg
      have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inr b)))
          (eIdx K G hlow (Sum.inl (Sum.inr b'))) = -(CatalanLambda.Dq ℓ K b.1.1 *
            CatalanLambda.Dq ℓ K b'.1.1 * (0 + CatalanLambda.M0n b.1.1 b'.1.1)) := by
        have hne' : b.1 ≠ b'.1 := fun h => hne (congrArg Subtype.val h)
        simp [Ncell, eIdx, rn, cn, full_ll, hne']
      rw [hN]
      refine hg.congr ?_
      simp [Zmat, hbb]
  · -- high common / Y'
    have hb : K ≤ (b : G.C).1 := by have := b.2; omega
    have hg := (node_hh_off hlK hb (hCl b.1) (hysK j).1 (hysK j).2 (hCys b.1 j)).neg
    have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inr b)))
        (eIdx K G hlow (Sum.inr j)) = -(CatalanLambda.Dq ℓ K b.1.1 *
          CatalanLambda.Dq ℓ K (G.ys j) * (0 + CatalanLambda.M0n b.1.1 (G.ys j))) := by
      simp [Ncell, eIdx, rn, cn, full_lr]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat]
  · -- X' / low
    have ha := a'.2
    have hg := (node_hl hlK (hxsK i).1 (hxsK i).2 ha).neg
    have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inr i))
        (eIdx K G hlow (Sum.inl (Sum.inl a'))) = -(CatalanLambda.Dq ℓ K (G.xs i) *
          CatalanLambda.Dq ℓ K a' * (0 + CatalanLambda.M0n (G.xs i) a')) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_rl]
    rw [hN]
    refine hg.congr ?_
    simp only [Zmat, WX, Wnode]
    simp
    first | exact inv_flip _ _ | (rw [← neg_sub]; simp [inv_neg]; ring)
  · -- X' / high common
    have hb' : K ≤ (b' : G.C).1 := by have := b'.2; omega
    have hg := (node_hh_off hlK (hxsK i).1 (hxsK i).2 hb' (hCl b'.1) (Ne.symm (hCxs b'.1 i))).neg
    have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inr i))
        (eIdx K G hlow (Sum.inl (Sum.inr b'))) = -(CatalanLambda.Dq ℓ K (G.xs i) *
          CatalanLambda.Dq ℓ K b'.1.1 * (0 + CatalanLambda.M0n (G.xs i) b'.1.1)) := by
      simp [Ncell, eIdx, rn, cn, full_rl]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat]
  · -- X' / Y'
    have hg := (node_hh_off hlK (hxsK i).1 (hxsK i).2 (hysK j).1 (hysK j).2 (hxy i j)).neg
    have hN : Ncell ℓ K G x (eIdx K G hlow (Sum.inr i))
        (eIdx K G hlow (Sum.inr j)) = -(CatalanLambda.Dq ℓ K (G.xs i) *
          CatalanLambda.Dq ℓ K (G.ys j) * (0 + CatalanLambda.M0n (G.xs i) (G.ys j))) := by
      simp [Ncell, eIdx, rn, cn, full_rr]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat]

end YGood

end CatalanFrames.LambdaHybrid.NV
