module

public import CatalanCore.Uniform.Decay.PolyWire3.Kinds
public import CatalanCore.Uniform.Decay.NearFast.Cell

@[expose] public section
set_option Elab.async false

/-!
# Far-piece cache and modulus hoist for the cover checker (lane H, wave H3; ledger CK3, M20)

Parent and child cells (`LOWNER-AVOIDANCE` section 3.3).  A parent jet of order `n'` for the far
pieces over `|S| <= H` is checked once (`parOk`); a child cell on the same line evaluates only the
near pieces, adds the parent polynomial shifted to the child's centre (`shiftL`, exact) and runs the
Bernstein and modulus steps (`childOk`, `childOk_sound`).  The modulus test of the whole piece list is
per cover (the hoist).  Below, blocks and items carry this through the tube test (`tubeCheckC`,
`tubeCheckC_sound`); `CellKind` is closed and protected (M20), so blocks sit in a parallel item type.
-/

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.NearCells

/-- The parent test: done once per macro cell. -/
def parOk (n' : ℕ) (far : List WP) (Zc dd : CQ) (H : ℚ) (Cp : List ℚ) (Fp : ℚ) : Bool :=
  match aggEvalMF n' Zc dd H far with
  | some (C0, F0) => decide (C0 = Cp) && decide (F0 ≤ Fp)
  | none => false

/-- The parent polynomial about `σ`. -/
def shiftL (Cp : List ℚ) (n' : ℕ) (σ : ℚ) : List ℚ :=
  (List.range n').map (affK (coeffs Cp) (n' - 1) σ 1)

/-- The child's centre. -/
def childC (Zc dd : CQ) (σ : ℚ) : CQ := ⟨Zc.re + σ * dd.re, Zc.im + σ * dd.im⟩

/-- The child test: near pieces only.  `MS` is the modulus sum of all pieces, checked once per cover. -/
def childOk (n n' : ℕ) (near : List WP) (Zc dd : CQ) (σ H h W cpi lo m' : ℚ) (C : List ℚ) (Fs : ℚ)
    (Cp : List ℚ) (Fp MS : ℚ) : Bool :=
  match aggEvalMF n (childC Zc dd σ) dd h near with
  | some (C0, F0) =>
    decide (0 < h) && decide (0 < W) && decide (0 ≤ cpi) && decide (2 ≤ n') && decide (n ≤ n') &&
      decide (C0.length ≤ n) && decide (|σ| + h ≤ H) &&
      decide (0 ≤ (childC Zc dd σ).im - h * |dd.im|) &&
      decide (addL C0 (shiftL Cp n' σ) = C) && decide (F0 + Fp ≤ Fs) &&
      bernLoOk2 (coeffs (cellPoly C cpi (childC Zc dd σ) dd)) (n' - 1) (-h) (2 * h) lo &&
      decide (m' ≤ lo - Fs - MS)
  | none => false

theorem shiftL_sum (Cp : List ℚ) {n' : ℕ} (hn : 1 ≤ n') (σ : ℚ) (s : ℝ) :
    ∑ m ∈ range n', ((coeffs (shiftL Cp n' σ) m : ℚ) : ℝ) * s ^ m
      = ∑ m ∈ range n', ((coeffs Cp m : ℚ) : ℝ) * ((σ : ℝ) + s) ^ m := by
  obtain ⟨d, rfl⟩ : ∃ d, n' = d + 1 := ⟨n' - 1, by omega⟩
  have h1 : ∀ m ∈ range (d + 1), ((coeffs (shiftL Cp (d + 1) σ) m : ℚ) : ℝ) * s ^ m
      = affCoeffs (fun i => ((coeffs Cp i : ℚ) : ℝ)) d (σ : ℝ) ((1 : ℚ) : ℝ) m * s ^ m := by
    intro m hm
    have hm' : m < d + 1 := Finset.mem_range.1 hm
    have e : coeffs (shiftL Cp (d + 1) σ) m = affCoeffs (coeffs Cp) d σ 1 m := by
      rw [← affK_eq]
      simp [shiftL, coeffs, List.getD_eq_getElem?_getD, hm']
    rw [e, affCoeffs_cast]
  rw [Finset.sum_congr rfl h1]
  have := peval_affCoeffs (fun i => ((coeffs Cp i : ℚ) : ℝ)) d (σ : ℝ) ((1 : ℚ) : ℝ) s
  unfold peval at this
  rw [this]
  simp

theorem sum_extend {C : List ℚ} {n n' : ℕ} (hn : n ≤ n') (hl : C.length ≤ n) (s : ℝ) :
    ∑ m ∈ range n', ((coeffs C m : ℚ) : ℝ) * s ^ m = ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.2 hn)
  intro m _ hm
  have hm' : n ≤ m := by simpa using hm
  have : coeffs C m = 0 := by
    have hge : C.length ≤ m := by omega
    simp [coeffs, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
  simp [this]

theorem childC_toC (Zc dd : CQ) (σ : ℚ) (s : ℝ) :
    Zc.toC + (((σ : ℝ) + s : ℝ) : ℂ) * dd.toC = (childC Zc dd σ).toC + (s : ℂ) * dd.toC := by
  apply Complex.ext <;> simp [childC, CQ.toC] <;> ring

/-- **Soundness of the cached cell.** -/
theorem childOk_sound {n n' : ℕ} {far near : List WP} {Zc dd : CQ} {σ H h W Rtwo cpi lo m' Fs Fp : ℚ}
    {C Cp : List ℚ} {eW eP : ℕ}
    (hp : parOk n' far Zc dd H Cp Fp = true)
    (hm : modAll Rtwo W eW eP (far ++ near) = true)
    (hc : childOk n n' near Zc dd σ H h W cpi lo m' C Fs Cp Fp (modSum Rtwo W eW eP (far ++ near)) = true)
    (s δ : ℝ) (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -((far ++ near).map (fun P => (P.w : ℝ) *
        PhiW P ((childC Zc dd σ).toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |((childC Zc dd σ).toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  unfold parOk at hp
  split at hp
  swap
  · cases hp
  rename_i Cq Fq hpar
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hCq, hFq⟩ := hp
  subst hCq
  unfold childOk at hc
  split at hc
  swap
  · cases hc
  rename_i C0 F0 hag
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hh, hW⟩, hcpi⟩, hn2⟩, hnn⟩, hlen⟩, hσ⟩, hy0⟩, hcl⟩, hF⟩, hbern⟩, hfin⟩ := hc
  have hcl' := hcl.symm
  subst hcl'
  set zc := childC Zc dd σ with hzc
  have hbern := bernLoOk2_imp hbern
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hcp : (0 : ℝ) ≤ cpi := by exact_mod_cast hcpi
  have hsR : |s| ≤ (h : ℝ) := hs
  have hS : |(σ : ℝ) + s| ≤ (H : ℝ) := by
    have h1 : ((|σ| + h : ℚ) : ℝ) ≤ H := by exact_mod_cast hσ
    push_cast at h1
    exact (abs_add_le _ _).trans (by linarith)
  -- the two models
  have hnear := aggEvalMF_sound s hs near hag
  have hfar := aggEvalMF_sound ((σ : ℝ) + s) hS far hpar
  rw [childC_toC, ← hzc] at hfar
  -- Bernstein on the cell polynomial
  have hB : (lo : ℝ) ≤ ∑ m ∈ range n',
      ((coeffs (cellPoly (addL C0 (shiftL Cq n' σ)) cpi zc dd) m : ℚ) : ℝ) * s ^ m := by
    have hw2 : (0 : ℚ) < 2 * h := by linarith
    have := bernLoOk_sound_real (a := coeffs (cellPoly (addL C0 (shiftL Cq n' σ)) cpi zc dd))
      (d := n' - 1) (u := -h) (w := 2 * h) hw2 hbern
      (x := s) (by push_cast; linarith [(abs_le.1 hsR).1]) (by push_cast; linarith [(abs_le.1 hsR).2])
    have e : n' - 1 + 1 = n' := by omega
    unfold peval at this
    rw [e] at this
    exact this
  have hsplit : ∑ m ∈ range n', ((coeffs (cellPoly (addL C0 (shiftL Cq n' σ)) cpi zc dd) m : ℚ) : ℝ) * s ^ m
      = ∑ m ∈ range n, ((coeffs C0 m : ℚ) : ℝ) * s ^ m
        + ∑ m ∈ range n', ((coeffs Cq m : ℚ) : ℝ) * ((σ : ℝ) + s) ^ m
        + (cpi : ℝ) * ((zc.im : ℝ) + s * dd.im) := by
    have h1 : ∀ m ∈ range n', ((coeffs (cellPoly (addL C0 (shiftL Cq n' σ)) cpi zc dd) m : ℚ) : ℝ) * s ^ m
        = ((coeffs C0 m : ℚ) : ℝ) * s ^ m + ((coeffs (shiftL Cq n' σ) m : ℚ) : ℝ) * s ^ m
          + ((coeffs [cpi * zc.im, cpi * dd.im] m : ℚ) : ℝ) * s ^ m := by
      intro m _
      unfold cellPoly
      rw [coeffs_addL, coeffs_addL]; push_cast; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_extend hnn hlen, shiftL_sum Cq (by omega) σ s]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 2 := ⟨n' - 2, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h3 : ∀ m ∈ range k, ((coeffs [cpi * zc.im, cpi * dd.im] (m + 1 + 1) : ℚ) : ℝ) * s ^ (m + 1 + 1) = 0 := by
      intro m _; simp [coeffs]
    rw [Finset.sum_eq_zero h3]
    simp [coeffs]; ring
  -- tube perturbation
  have hz : ‖(zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ))‖ ≤ (W : ℝ) := by
    have : (zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)) = -(δ : ℂ) := by ring
    rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hδ
  have hms := modAll_sum hWR (far ++ near) hm hz
  have him : (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im = (zc.im : ℝ) + s * (dd.im : ℝ) := by
    simp [CQ.toC]
  have hy : 0 ≤ (zc.im : ℝ) + s * dd.im := by
    have h1 : |s * (dd.im : ℝ)| ≤ h * |(dd.im : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    have h2 := (abs_le.1 h1).1
    have h0 : (0 : ℝ) ≤ (zc.im : ℝ) - h * |(dd.im : ℝ)| := by exact_mod_cast hy0
    linarith
  rw [him, abs_of_nonneg hy]
  have hfinR : (m' : ℝ) ≤ lo - Fs - modSum Rtwo W eW eP (far ++ near) := by exact_mod_cast hfin
  have hFR : (F0 : ℝ) + Fp ≤ Fs := by exact_mod_cast hF
  have hFq' : (Fq : ℝ) ≤ Fp := by exact_mod_cast hFq
  rw [hsplit] at hB
  have hA : ((far ++ near).map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum
      = (far.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum
        + (near.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum := by
    rw [List.map_append, List.sum_append]
  rw [hA] at hms
  rw [abs_le] at hnear hfar hms
  nlinarith [hnear.1, hnear.2, hfar.1, hfar.2, hms.1, hms.2, hFR, hFq']


end CatalanCore.Uniform.Decay.NearFast

/-! ## Cached blocks on a line, and the tube with blocks (ledger CK3, M20)

A block caches the far pieces of one macro interval `[plo, phi]` of a line `Z0 + t dd` in a parent
jet (`parOk`, once) and carries the children (`childOk`, near pieces only).  The far set is given by
indices into the piece list (`farOf`), so far and near are a partition of the piece list by
construction.  The modulus data `modAll`, `modSum` of the whole piece list are checked once per
cover and passed as `MS` (the modulus hoist); a block with no far pieces is the plain jet cell with
the modulus hoisted.  `CellKind` is closed and protected, so blocks live in a parallel item type
`TItem` and the tube test `tubeCheckC` repeats `tubeCheck` with items. -/

namespace CatalanCore.Uniform.Decay.PolyWire3

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.NearFast
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyWire2
open CatalanCore.Uniform.Decay.FarField (MPData)

/-- Far pieces of a block: those at the listed indices. -/
def farOf (far : List ℕ) (ps : List WP) : List WP :=
  (ps.zipIdx.filter fun p => far.contains p.2).map Prod.fst

/-- Near pieces of a block: all others. -/
def nearOf (far : List ℕ) (ps : List WP) : List WP :=
  (ps.zipIdx.filter fun p => !far.contains p.2).map Prod.fst

theorem farNear_perm (far : List ℕ) (ps : List WP) : (farOf far ps ++ nearOf far ps).Perm ps := by
  have h := (List.filter_append_perm (fun p : WP × ℕ => far.contains p.2) ps.zipIdx).map Prod.fst
  rw [List.map_append, List.zipIdx_map_fst] at h
  exact h

theorem modSum_eq_sum (Rtwo W : ℚ) (eW eP : ℕ) (ps : List WP) :
    modSum Rtwo W eW eP ps = (ps.map fun P => |P.w| * modQ P W eW eP).sum := by
  induction ps with
  | nil => simp [modSum]
  | cons P ps ih => simp [modSum, ih]

theorem modSum_perm {Rtwo W : ℚ} {eW eP : ℕ} {l l' : List WP} (h : l.Perm l') :
    modSum Rtwo W eW eP l = modSum Rtwo W eW eP l' := by
  rw [modSum_eq_sum, modSum_eq_sum]
  exact (h.map _).sum_eq

theorem modAll_perm {Rtwo W : ℚ} {eW eP : ℕ} {l l' : List WP} (h : l.Perm l') :
    modAll Rtwo W eW eP l = modAll Rtwo W eW eP l' := by
  unfold modAll
  exact h.all_eq

/-- A child cell of a block: the interval, the Bernstein lower bound `lo`, the model `C` and error `Fs`. -/
structure CKid where
  ulo : ℚ
  uhi : ℚ
  lo : ℚ
  C : List ℚ
  Fs : ℚ

/-- A block: child order `n`, parent order `n'`, far indices, macro interval, parent model `Cp`,
parent error `Fp`, children. -/
structure CBlock where
  n : ℕ
  n' : ℕ
  far : List ℕ
  plo : ℚ
  phi : ℚ
  Cp : List ℚ
  Fp : ℚ
  kids : List CKid

/-- The point `Z0 + t dd` of a line. -/
def lineCentre (Z0 dd : CQ) (t : ℚ) : CQ := CQ.add Z0 (CQ.smul t dd)

theorem lineCentre_toC (Z0 dd : CQ) (t : ℚ) :
    (lineCentre Z0 dd t).toC = Z0.toC + (t : ℂ) * dd.toC := by
  unfold lineCentre
  rw [CQ.toC_add, CQ.toC_smul]

/-- The parent centre of a block. -/
def CBlock.centre (Z0 dd : CQ) (b : CBlock) : CQ := lineCentre Z0 dd ((b.plo + b.phi) / 2)

/-- **The block test**: the parent once, then every child on the near pieces. -/
def cblockOk (ps : List WP) (Z0 dd : CQ) (W cpi m' MS : ℚ) (b : CBlock) : Bool :=
  parOk b.n' (farOf b.far ps) (b.centre Z0 dd) dd ((b.phi - b.plo) / 2) b.Cp b.Fp &&
    b.kids.all fun k =>
      childOk b.n b.n' (nearOf b.far ps) (b.centre Z0 dd) dd
        ((k.ulo + k.uhi) / 2 - (b.plo + b.phi) / 2) ((b.phi - b.plo) / 2) ((k.uhi - k.ulo) / 2) W cpi
        k.lo m' k.C k.Fs b.Cp b.Fp MS

/-- **Soundness of a block.**  Under the per-cover modulus test, every child cell satisfies the
usual cell conclusion for the whole piece list at the points `Z0 + t dd + δ`. -/
theorem cblockOk_sound {ps : List WP} {Z0 dd : CQ} {W Rtwo cpi m' MS : ℚ} {eW eP : ℕ} {b : CBlock}
    (hm : modAll Rtwo W eW eP ps = true) (hMS : modSum Rtwo W eW eP ps = MS)
    (hb : cblockOk ps Z0 dd W cpi m' MS b = true) :
    ∀ k ∈ b.kids, ∀ t : ℝ, (k.ulo : ℝ) ≤ t → t ≤ (k.uhi : ℝ) → ∀ δ : ℝ, |δ| ≤ (W : ℝ) →
      (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
          PhiW P (Z0.toC + (t : ℂ) * dd.toC + (δ : ℂ)))).sum
        + (cpi : ℝ) * |(Z0.toC + (t : ℂ) * dd.toC + (δ : ℂ)).im| := by
  intro k hk t ht1 ht2 δ hδ
  unfold cblockOk at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨hp, hall⟩ := hb
  have hc := List.all_eq_true.1 hall k hk
  have hperm := farNear_perm b.far ps
  have hm' : modAll Rtwo W eW eP (farOf b.far ps ++ nearOf b.far ps) = true := by
    rw [modAll_perm hperm]; exact hm
  have hMS' : modSum Rtwo W eW eP (farOf b.far ps ++ nearOf b.far ps) = MS := by
    rw [modSum_perm hperm]; exact hMS
  have hc' : childOk b.n b.n' (nearOf b.far ps) (b.centre Z0 dd) dd
      ((k.ulo + k.uhi) / 2 - (b.plo + b.phi) / 2) ((b.phi - b.plo) / 2) ((k.uhi - k.ulo) / 2) W cpi
      k.lo m' k.C k.Fs b.Cp b.Fp
      (modSum Rtwo W eW eP (farOf b.far ps ++ nearOf b.far ps)) = true := by
    rw [hMS']; exact hc
  have key := childOk_sound (eW := eW) (eP := eP) (Rtwo := Rtwo) hp hm' hc'
    (t - (((k.ulo + k.uhi) / 2 : ℚ) : ℝ)) δ (by
      rw [abs_le]; push_cast; constructor <;> linarith) hδ
  have ez : (childC (b.centre Z0 dd) dd ((k.ulo + k.uhi) / 2 - (b.plo + b.phi) / 2)).toC
      + ((t - (((k.ulo + k.uhi) / 2 : ℚ) : ℝ) : ℝ) : ℂ) * dd.toC + (δ : ℂ)
      = Z0.toC + (t : ℂ) * dd.toC + (δ : ℂ) := by
    have h1 := childC_toC (b.centre Z0 dd) dd ((k.ulo + k.uhi) / 2 - (b.plo + b.phi) / 2)
      (t - (((k.ulo + k.uhi) / 2 : ℚ) : ℝ))
    have h2 : (b.centre Z0 dd).toC = Z0.toC + (((b.plo + b.phi) / 2 : ℚ) : ℂ) * dd.toC := by
      unfold CBlock.centre; rw [lineCentre_toC]
    rw [← h1, h2]
    push_cast
    ring
  rw [ez] at key
  have e2 : ((farOf b.far ps ++ nearOf b.far ps).map (fun P => (P.w : ℝ) *
      PhiW P (Z0.toC + (t : ℂ) * dd.toC + (δ : ℂ)))).sum
      = (ps.map (fun P => (P.w : ℝ) * PhiW P (Z0.toC + (t : ℂ) * dd.toC + (δ : ℂ)))).sum :=
    (hperm.map _).sum_eq
  rw [e2] at key
  exact key

/-! ### Items: plain cells and blocks -/

inductive TItem where
  | cell (c : TCell)
  | blk (b : CBlock)

/-- The intervals an item covers. -/
def TItem.ivs : TItem → List (ℚ × ℚ)
  | .cell c => [(c.ulo, c.uhi)]
  | .blk b => b.kids.map fun k => (k.ulo, k.uhi)

/-- The test of one tube item on the edge `e`. -/
def itemOkT (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (D : SplineData)
    (MS : ℚ) (e : Pt × Pt) : TItem → Bool
  | .cell c => cellOk nu M Rtwo eW eP F D e c
  | .blk b => decide (D.ε < 1) &&
      cblockOk (cellPieces D nu) (cqOf e.1) (CQ.sub (cqOf e.2) (cqOf e.1)) D.W (cpiOf D) D.mprime MS b

theorem itemOkT_sound (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) {F : FarData} {D : SplineData} (hb : D.basicOk = true)
    (H : FarHyp D Vnu F) (hG : globalOk (cellPieces D nu) M = true) {MS : ℚ}
    (hm : modAll Rtwo D.W eW eP (cellPieces D nu) = true)
    (hMS : modSum Rtwo D.W eW eP (cellPieces D nu) = MS) (e : Pt × Pt) (it : TItem)
    (h : itemOkT nu M Rtwo eW eP F D MS e it = true) :
    ∀ p ∈ it.ivs, ∀ t : ℝ, (p.1 : ℝ) ≤ t → t ≤ (p.2 : ℝ) → ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)) := by
  have B := SplineData.basicOk_sound hb
  cases it with
  | cell c =>
    intro p hp t h1 h2 δ hδ
    simp only [TItem.ivs, List.mem_singleton] at hp
    subst hp
    simp only [itemOkT] at h
    rcases Bool.or_eq_true_iff.1 h with hc | hc
    · exact cellFar_sound H B hc t h1 h2 δ
    · exact nearCellT_sound nu M Rtwo eW eP hV D hG e c hc t h1 h2 δ hδ
  | blk b =>
    intro p hp t h1 h2 δ hδ
    simp only [itemOkT, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hε, hbk⟩ := h
    simp only [TItem.ivs, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    have key := cblockOk_sound hm hMS hbk k hk t h1 h2 δ hδ
    have ez : (cqOf e.1).toC + (t : ℂ) * (CQ.sub (cqOf e.2) (cqOf e.1)).toC + (δ : ℂ)
        = segPtC e t + (δ : ℂ) := by
      rw [CQ.toC_sub, cqOf_toC, cqOf_toC]
      unfold segPtC
      ring
    rw [ez] at key
    exact gNu_ge_of D nu hV hε key

/-- An edge: the intervals of the items cover `[0,1]`, every item passes. -/
def edgeItems (ok : Pt × Pt → TItem → Bool) (e : Pt × Pt) (its : List TItem) : Bool :=
  coverOk 0 1 (its.flatMap TItem.ivs) && its.all (ok e)

def tubeItems (ok : Pt × Pt → TItem → Bool) : List (Pt × Pt) → List (List TItem) → Bool
  | [], [] => true
  | e :: es, cs :: css => edgeItems ok e cs && tubeItems ok es css
  | _, _ => false

theorem tubeItems_sound {ok : Pt × Pt → TItem → Bool} {Q : Pt × Pt → ℝ → Prop}
    (hQ : ∀ e (it : TItem), ok e it = true → ∀ p ∈ it.ivs, ∀ t : ℝ, (p.1 : ℝ) ≤ t → t ≤ (p.2 : ℝ) →
      Q e t) :
    ∀ (es : List (Pt × Pt)) (css : List (List TItem)), tubeItems ok es css = true →
      ∀ e ∈ es, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Q e t
  | [], [], _, e, he, _, _, _ => by simp at he
  | [], _ :: _, h, _, _, _, _, _ => by simp [tubeItems] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [tubeItems] at h
  | e0 :: es, cs :: css, h, e, he, t, ht0, ht1 => by
      simp only [tubeItems, edgeItems, Bool.and_eq_true] at h
      obtain ⟨⟨hcov, hall⟩, hrest⟩ := h
      rcases List.mem_cons.1 he with rfl | he
      · obtain ⟨p, hp, h1, h2⟩ := coverOk_sound hcov t (by simpa using ht0) (by simpa using ht1)
        obtain ⟨it, hit, hpit⟩ := List.mem_flatMap.1 hp
        exact hQ _ it (List.all_eq_true.1 hall it hit) p hpit t h1 h2
      · exact tubeItems_sound hQ es css hrest e he t ht0 ht1

/-- **The tube test with blocks.**  `MS` is the modulus sum of the piece list, checked here once. -/
def tubeCheckC (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (tmax MS : ℚ)
    (tube : List (List TItem)) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (0 < tmax) && decide (0 ≤ P.s) &&
    modAll Rtwo D.W eW eP (cellPieces D nu) && decide (modSum Rtwo D.W eW eP (cellPieces D nu) = MS) &&
    tubeItems (itemOkT nu M Rtwo eW eP F D MS) (edgesAll P tmax) tube &&
    farOk D F ((lastPt (basePt P) P.verts).2 + P.s * tmax)

theorem tubeCheckC_sound (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) {F : FarData} {tmax MS : ℚ} {tube : List (List TItem)}
    {D : SplineData} {P : RatPolygon} (hb : D.basicOk = true) (H : FarHyp D Vnu F)
    (hG : globalOk (cellPieces D nu) M = true)
    (h : tubeCheckC nu M Rtwo eW eP F tmax MS tube D P = true) :
    ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + (δ : ℂ)) := by
  simp only [tubeCheckC, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨htm, hs⟩, hmod⟩, hMS⟩, hcells⟩, hfar⟩ := h
  have B := SplineData.basicOk_sound hb
  have key := tubeItems_sound (Q := fun e t => ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)))
    (fun e it hit p hp t h1 h2 δ hδ =>
      itemOkT_sound nu M Rtwo eW eP hV hb H hG hmod hMS e it hit p hp t h1 h2 δ hδ) _ _ hcells
  intro w hw δ hδ
  rcases hw with hw | hw
  · rw [base_eq] at hw
    obtain ⟨e, he, t, h0, h1, rfl⟩ := chainSet_edges P.verts (basePt P) hw
    exact key e (List.mem_append_left _ he) t h0 h1 δ hδ
  · obtain ⟨t, ht0, rfl⟩ := hw
    have hL := getLast_map_vertC P.verts _ (basePt P) (base_eq P) (List.cons_ne_nil _ _)
    rw [hL]
    by_cases hle : t ≤ tmax
    · rw [tail_seg htm]
      have htm' : (0 : ℝ) < tmax := by exact_mod_cast htm
      refine key _ (List.mem_append_right _ (List.mem_singleton_self _)) _
        (div_nonneg ht0 htm'.le) ((div_le_one htm').2 hle) δ hδ
    · push Not at hle
      refine far_g_ge H B hfar _ ?_
      have him : (vertC (lastPt (basePt P) P.verts) + (t : ℂ) * P.tailDir + (δ : ℂ)).im
          = ((lastPt (basePt P) P.verts).2 : ℝ) + t * (P.s : ℝ) := by
        simp [vertC, RatPolygon.tailDir]
      rw [him]
      have hs' : (0 : ℝ) ≤ P.s := by exact_mod_cast hs
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hle.le hs']

/-! ### Plain tubes are tubes with items -/

/-- A plain cell list as items. -/
def TItem.ofCells (cs : List TCell) : List TItem := cs.map TItem.cell

/-- A plain cell test as an item test (blocks fail). -/
def TItem.ofOk (ok : Pt × Pt → TCell → Bool) : Pt × Pt → TItem → Bool := fun e it =>
  match it with
  | .cell c => ok e c
  | .blk _ => false

theorem flatMap_ivs_ofCells (cs : List TCell) :
    (TItem.ofCells cs).flatMap TItem.ivs = cs.map fun c => (c.ulo, c.uhi) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa [TItem.ofCells, TItem.ivs] using ih

theorem all_ofCells (ok : Pt × Pt → TCell → Bool) (e : Pt × Pt) (cs : List TCell) :
    (TItem.ofCells cs).all (TItem.ofOk ok e) = cs.all (ok e) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have h : (TItem.ofCells (c :: cs)).all (TItem.ofOk ok e)
        = (ok e c && (TItem.ofCells cs).all (TItem.ofOk ok e)) := rfl
    rw [h, ih]; rfl

/-- A plain edge is an edge of items. -/
theorem edgeItems_ofCells (ok : Pt × Pt → TCell → Bool) (e : Pt × Pt) (cs : List TCell) :
    edgeItems (TItem.ofOk ok) e (TItem.ofCells cs) = edgeCells ok e cs := by
  unfold edgeItems edgeCells
  rw [flatMap_ivs_ofCells, all_ofCells]

end CatalanCore.Uniform.Decay.PolyWire3

#print axioms CatalanCore.Uniform.Decay.NearFast.childOk_sound
#print axioms CatalanCore.Uniform.Decay.PolyWire3.cblockOk_sound
#print axioms CatalanCore.Uniform.Decay.PolyWire3.tubeCheckC_sound
