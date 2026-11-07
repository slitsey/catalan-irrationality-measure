module

public import CatalanCore.Uniform.Decay.PolyWire2.Energy2
public import CatalanCore.Uniform.Decay.PolyWire3.Kinds

@[expose] public section
set_option Elab.async false

/-!
# Conjugation and exchange folds of the decay checker (lane H, wave H2; ledger CK1, CK2)

Two folds that make the finite checker smaller without changing what it proves.

* **Energy fold (CK1).**  The pair energy `pairE D i j` is invariant under exchange `i ↔ j`
  (at any pair that passes `pairOk`) and under conjugation `i ↦ τ i, j ↦ τ j`.  A table entry that is
  not its own class representative is only checked to point at its representative (`cn`, with values in
  `ℕ × ℕ`, so that the table does not depend on `D.n` as a type).  `energyFoldOk_sound` is stated for
  every `D` with `D.basicOkP`, the test being run at `D.noRay` as every other polygon rule is.
* **Line fold (CK2).**  On the real axis a piece and its conjugate have one potential, so line and cap
  cells may run on a list with one piece of each conjugate pair at double weight.  One `foldOk` test
  per cover replaces the doubled list.

Both are generic: any `SplineData`, any piece list, any cells.
-/

namespace CatalanCore.Uniform.Decay.PolyWire3

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.NearFast
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyWire2 CatalanCore.Uniform.Decay.PairEnergy
open CatalanCore.Uniform.Decay.FarField (MPData cellOkFL cellOkFL_sound PLCell plLine)

/-! ### Energy fold -/

section EnergyFold

variable {D : SplineData}

theorem pt_tau (B : SplineData.BasicFacts D) (i : Fin D.n) (t : ℝ) :
    pt D.A D.B (D.tauF i) t = (starRingEnd ℂ) (pt D.A D.B i t) := by
  simp [pt, B.hAτ i, B.hBτ i, map_add, map_mul, map_sub, Complex.conj_ofReal]

theorem f_tau (B : SplineData.BasicFacts D) (i : Fin D.n) : D.f (D.tauF i) = D.f i := by
  unfold SplineData.f; rw [B.hlτ i]

theorem segU_tau (B : SplineData.BasicFacts D) (j : Fin D.n) (z : ℂ) :
    segU D (D.tauF j) ((starRingEnd ℂ) z) = segU D j z := by
  unfold segU
  rw [f_tau B]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [pt_tau B, ← map_sub, Complex.norm_conj]

/-- **Conjugation invariance of the pair energy.** -/
theorem pairE_tau (B : SplineData.BasicFacts D) (i j : Fin D.n) :
    pairE D (D.tauF i) (D.tauF j) = pairE D i j := by
  unfold pairE
  rw [f_tau B]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [pt_tau B, segU_tau B]

end EnergyFold

/-- The same pair with the two segments exchanged. -/
def swapPair (P : PairData) : PairData := ⟨P.A2, P.B2, P.A1, P.B1, P.b, P.a, P.t0, P.s0⟩

theorem swapPair_cw (P : PairData) : (swapPair P).cw = P.dw := by
  funext e l
  simp only [PairData.cw, PairData.dw, swapPair, PairData.al, PairData.be]
  congr 1
  simp only [sumR_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm (k : ℚ) (l : ℚ)]

theorem swapPair_dw (P : PairData) : (swapPair P).dw = P.cw := by
  funext e k
  simp only [PairData.cw, PairData.dw, swapPair, PairData.al, PairData.be]
  congr 1
  simp only [sumR_eq]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [add_comm (l : ℚ) (k : ℚ)]

theorem swapPair_qc (P : PairData) : (swapPair P).qc = P.qc := by
  simp only [PairData.qc, swapPair, PairData.al, PairData.be, sumR_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [add_comm (l : ℚ) (k : ℚ)]
  ring

/-- **The closed form is symmetric**: no Fubini is needed. -/
theorem swapPair_val (P : PairData) : (swapPair P).pairLF.val = P.pairLF.val := by
  have h1 := swapPair_cw P
  have h2 := swapPair_dw P
  have h3 := swapPair_qc P
  unfold PairData.pairLF
  rw [h1, h2, h3]
  simp only [LF.val_smul, LF.val_add, LF.val_const]
  simp only [swapPair, PairData.al, PairData.be]
  ring

theorem swapPair_rel (P : PairData) (h : P.rel = QC.zero) : (swapPair P).rel = QC.zero := by
  have hre := congrArg QC.re h
  have him := congrArg QC.im h
  simp only [PairData.rel, QC.sub, QC.add, QC.qmul, QC.zero] at hre him
  simp only [PairData.rel, swapPair, QC.sub, QC.add, QC.qmul, QC.zero]
  congr 1 <;> linarith

section EnergyFold

variable {D : SplineData}

/-- **Exchange symmetry of the pair energy**, at any pair that passes `pairOk`. -/
theorem pairE_swap_of_ok (i j : Fin D.n) {E : ℚ} (h : pairOk D i.1 j.1 E = true) :
    pairE D j i = pairE D i j := by
  unfold pairOk at h
  rw [List.getElem?_eq_getElem i.2, List.getElem?_eq_getElem j.2] at h
  simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hrel, hu⟩, hv⟩, -⟩ := h
  rw [pairE_eq, pairE_eq]
  have hsi : D.seg i = D.segs[i.1]'i.2 := rfl
  have hsj : D.seg j = D.segs[j.1]'j.2 := rfl
  rw [hsi, hsj]
  generalize D.segs[i.1]'i.2 = s1 at *
  generalize D.segs[j.1]'j.2 = s2 at *
  set P := mkPair s1 s2 with hP
  have hA1 : P.A1 = segA s1 := by simp [hP, mkPair]; split_ifs <;> rfl
  have hB1 : P.B1 = segB s1 := by simp [hP, mkPair]; split_ifs <;> rfl
  have hA2 : P.A2 = segA s2 := by simp [hP, mkPair]; split_ifs <;> rfl
  have hB2 : P.B2 = segB s2 := by simp [hP, mkPair]; split_ifs <;> rfl
  have ha : P.a = s1.coef := by simp [hP, mkPair]; split_ifs <;> rfl
  have hb : P.b = s2.coef := by simp [hP, mkPair]; split_ifs <;> rfl
  have hu' : (QC.sub P.B1 P.A1).toC ≠ 0 := fun h0 => hu (QC.toC_eq_zero' h0)
  have hv' : (QC.sub P.B2 P.A2).toC ≠ 0 := fun h0 => hv (QC.toC_eq_zero' h0)
  have e1 := pairLF_val P hu' hv' hrel
  have e2 := pairLF_val (swapPair P) hv' hu' (swapPair_rel P hrel)
  rw [swapPair_val] at e2
  simp only [swapPair] at e2
  rw [hA1, hB1, hA2, hB2, ha, hb] at e1 e2
  rw [← e1, ← e2]

/-- Table entry. -/
def eOf (E : List (List ℚ)) (i j : ℕ) : ℚ := (E.getD i []).getD j 0

/-- Conjugation on indices, extended by the identity beyond `D.n`. -/
def tauN (D : SplineData) (i : ℕ) : ℕ := if h : i < D.n then (D.tauF ⟨i, h⟩).1 else i

theorem tauN_fin (i : Fin D.n) : tauN D i.1 = (D.tauF i).1 := by simp [tauN, i.2]

/-- `(a, b)` is one of the four images of `(i, j)` under exchange and conjugation. -/
def isImgN (D : SplineData) (i j a b : ℕ) : Bool :=
  decide (a = i ∧ b = j) || decide (a = j ∧ b = i) || decide (a = tauN D i ∧ b = tauN D j) ||
    decide (a = tauN D j ∧ b = tauN D i)

/-- One entry: a representative is computed, any other entry only points at its representative. -/
def foldEntry (D : SplineData) (E : List (List ℚ)) (cn : ℕ → ℕ → ℕ × ℕ) (i j : ℕ) : Bool :=
  if cn i j = (i, j) then pairOk D i j (eOf E i j)
  else isImgN D i j (cn i j).1 (cn i j).2 &&
    decide (eOf E i j = eOf E (cn i j).1 (cn i j).2) &&
    decide (cn (cn i j).1 (cn i j).2 = cn i j)

/-- **The folded energy test.**  `cn i j` is the class representative of `(i, j)`; the table `E` is
the full table, with equal entries on a class. -/
def energyFoldOk (D : SplineData) (cn : ℕ → ℕ → ℕ × ℕ) (E : List (List ℚ)) : Bool :=
  (List.range D.n).all (fun i => (List.range D.n).all fun j => foldEntry D E cn i j) &&
    decide (tabSum D E ≤ D.Ibound)

theorem pairE_le_img (B : SplineData.BasicFacts D) {i j : Fin D.n} {a b : ℕ} {e : ℚ}
    (hi : isImgN D i.1 j.1 a b = true) (hok : pairOk D a b e = true) : pairE D i j ≤ (e : ℝ) := by
  simp only [isImgN, Bool.or_eq_true, decide_eq_true_eq] at hi
  rcases hi with ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩
  · exact pairOk_sound D i j _ hok
  · rw [pairE_swap_of_ok j i hok]; exact pairOk_sound D j i _ hok
  · rw [tauN_fin] at ha hb
    subst ha hb
    rw [← pairE_tau B i j]; exact pairOk_sound D _ _ _ hok
  · rw [tauN_fin] at ha hb
    subst ha hb
    rw [← pairE_tau B i j, pairE_swap_of_ok (D.tauF j) (D.tauF i) hok]
    exact pairOk_sound D _ _ _ hok

/-- Core form, at a `D` that passes the full `basicOk`. -/
theorem energyFoldOk_sound_basic (hb : D.basicOk = true) (cn : ℕ → ℕ → ℕ × ℕ)
    (E : List (List ℚ)) (h : energyFoldOk D cn E = true) : I0 D.A D.B D.f ≤ D.Ibound := by
  simp only [energyFoldOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hall, hsum⟩ := h
  have B := SplineData.basicOk_sound hb
  have ent : ∀ i j : ℕ, i < D.n → j < D.n → foldEntry D E cn i j = true := fun i j hi hj =>
    List.all_eq_true.1 (List.all_eq_true.1 hall i (List.mem_range.2 hi)) j (List.mem_range.2 hj)
  have hpair : ∀ i j : Fin D.n, pairE D i j ≤ ((eOf E i.1 j.1 : ℚ) : ℝ) := by
    intro i j
    have hij := ent i.1 j.1 i.2 j.2
    unfold foldEntry at hij
    split_ifs at hij with hc
    · exact pairOk_sound D i j _ hij
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hij
      obtain ⟨⟨himg, hE⟩, hidem⟩ := hij
      have hlt : (cn i.1 j.1).1 < D.n ∧ (cn i.1 j.1).2 < D.n := by
        have himg' := himg
        simp only [isImgN, Bool.or_eq_true, decide_eq_true_eq] at himg'
        rcases himg' with ((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩
        · rw [ha, hb]; exact ⟨i.2, j.2⟩
        · rw [ha, hb]; exact ⟨j.2, i.2⟩
        · rw [ha, hb, tauN_fin, tauN_fin]; exact ⟨(D.tauF i).2, (D.tauF j).2⟩
        · rw [ha, hb, tauN_fin, tauN_fin]; exact ⟨(D.tauF j).2, (D.tauF i).2⟩
      have hrep := ent _ _ hlt.1 hlt.2
      unfold foldEntry at hrep
      have hc' : cn (cn i.1 j.1).1 (cn i.1 j.1).2 = ((cn i.1 j.1).1, (cn i.1 j.1).2) := by
        simpa using hidem
      simp only [hc', ↓reduceIte] at hrep
      rw [hE]
      exact pairE_le_img B himg hrep
  rw [I0_eq_sum_pairE B]
  calc ∑ i, ∑ j, pairE D i j ≤ ∑ i : Fin D.n, ∑ j : Fin D.n, ((eOf E i.1 j.1 : ℚ) : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ((tabSum D E : ℚ) : ℝ) := by unfold tabSum eOf; push_cast; rfl
    _ ≤ D.Ibound := by exact_mod_cast hsum

/-- **Folded energy test is sound** (ledger CK1).  For `D` with `D.basicOkP`, the folded test run at
`D.noRay`, as every polygon rule is, bounds the energy `I0` by `D.Ibound`. -/
theorem energyFoldOk_sound (hb : D.basicOkP = true) (cn : ℕ → ℕ → ℕ × ℕ)
    (E : List (List ℚ)) (h : energyFoldOk D.noRay cn E = true) : I0 D.A D.B D.f ≤ D.Ibound :=
  energyFoldOk_sound_basic (D := D.noRay) (basicOk_noRay hb) cn E h

end EnergyFold

/-! ### Line fold -/

deriving instance DecidableEq for CQ
deriving instance DecidableEq for WP

def conjQ (z : CQ) : CQ := ⟨z.re, -z.im⟩
def conjWP (P : WP) : WP := { P with A := conjQ P.A, B := conjQ P.B }
def dblW (P : WP) : WP := { P with w := 2 * P.w }

theorem toC_conjQ (z : CQ) : (conjQ z).toC = (starRingEnd ℂ) z.toC := by
  apply Complex.ext <;> simp [conjQ, CQ.toC]

theorem PhiW_conj (P : WP) (x : ℝ) : PhiW (conjWP P) ⟨x, 0⟩ = PhiW P ⟨x, 0⟩ := by
  unfold PhiW
  refine intervalIntegral.integral_congr fun t _ => ?_
  have e : ((⟨x, 0⟩ : ℂ) - ((conjWP P).A.toC + (t : ℂ) * ((conjWP P).B.toC - (conjWP P).A.toC)))
      = (starRingEnd ℂ) ((⟨x, 0⟩ : ℂ) - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))) := by
    simp only [conjWP, toC_conjQ]
    apply Complex.ext <;> simp
  simp only [e, Complex.norm_conj]
  rfl

/-- potential sum on a list at a real point -/
noncomputable def rS (l : List WP) (x : ℝ) : ℝ := (l.map (fun P => (P.w : ℝ) * PhiW P ⟨x, 0⟩)).sum

theorem rS_append (a b : List WP) (x : ℝ) : rS (a ++ b) x = rS a x + rS b x := by
  simp [rS]

theorem rS_conj (U : List WP) (x : ℝ) : rS (U.map conjWP) x = rS U x := by
  induction U with
  | nil => rfl
  | cons P U ih =>
    have e1 : rS ((P :: U).map conjWP) x
        = ((conjWP P).w : ℝ) * PhiW (conjWP P) ⟨x, 0⟩ + rS (U.map conjWP) x := by
      simp only [rS, List.map_cons, List.sum_cons]
    have e2 : rS (P :: U) x = (P.w : ℝ) * PhiW P ⟨x, 0⟩ + rS U x := by
      simp only [rS, List.map_cons, List.sum_cons]
    rw [e1, e2, ih, PhiW_conj]
    rfl

theorem rS_dbl (U : List WP) (x : ℝ) : rS (U.map dblW) x = 2 * rS U x := by
  induction U with
  | nil => simp [rS]
  | cons P U ih =>
    have e1 : rS ((P :: U).map dblW) x
        = ((dblW P).w : ℝ) * PhiW (dblW P) ⟨x, 0⟩ + rS (U.map dblW) x := by
      simp only [rS, List.map_cons, List.sum_cons]
    have e2 : rS (P :: U) x = (P.w : ℝ) * PhiW P ⟨x, 0⟩ + rS U x := by
      simp only [rS, List.map_cons, List.sum_cons]
    have e3 : PhiW (dblW P) ⟨x, 0⟩ = PhiW P ⟨x, 0⟩ := rfl
    rw [e1, e2, ih, e3]
    simp only [dblW]
    push_cast
    ring

/-- The once-per-cover test: `ps` is `R`, `U` and the conjugates of `U`, up to order. -/
def foldOk (R U ps : List WP) : Bool := decide (ps.Perm (R ++ U ++ U.map conjWP))

/-- the folded list -/
def foldL (R U : List WP) : List WP := R ++ U.map dblW

theorem fold_sum {R U ps : List WP} (h : foldOk R U ps = true) (x : ℝ) :
    rS (foldL R U) x = rS ps x := by
  have hp : ps.Perm (R ++ U ++ U.map conjWP) := by simpa [foldOk] using h
  have : rS ps x = rS (R ++ U ++ U.map conjWP) x := (hp.map _).sum_eq
  rw [this, rS_append, rS_append, rS_conj, foldL, rS_append, rS_dbl]
  ring

/-- Line cell on the folded list.  `Wl` is free: the line needs no tube, so `Wl = 0` is allowed. -/
def lineFoldOk (qs : List WP) (M : Option MPData) (Wl Rtwo : ℚ) (eW eP : ℕ) (D : SplineData)
    (c : TCell) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ Wl) &&
    kindOk qs M ⟨(c.ulo + c.uhi) / 2, 0⟩ ⟨1, 0⟩ ((c.uhi - c.ulo) / 2) Wl Rtwo
      (cpiOf D) D.gmin eW eP c.kind

theorem lineFoldOk_sound {R U : List WP} (nu : List Seg) (M : Option MPData) (Wl Rtwo : ℚ) (eW eP : ℕ)
    {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData)
    (hf : foldOk R U (cellPieces D nu) = true) (hG : globalOk (foldL R U) M = true)
    (c : TCell) (h : lineFoldOk (foldL R U) M Wl Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.ulo : ℝ) ≤ x → x ≤ c.uhi →
      (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold lineFoldOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  have key := realCell_sound hG hW hm x hx1 hx2
  have e := fold_sum hf x
  simp only [rS] at e
  rw [e] at key
  exact gNu_ge_of D nu hV hε key

/-- Upper-bound cap cell on the folded list. -/
def ubFoldOk (qs : List WP) (M' : Option MPData) (Wl Rtwo : ℚ) (eW eP : ℕ) (D : SplineData)
    (c : TCell × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ Wl) &&
    kindOk (qs.map negW) M' ⟨(c.1.ulo + c.1.uhi) / 2, 0⟩ ⟨1, 0⟩
      ((c.1.uhi - c.1.ulo) / 2) Wl Rtwo 0 (-c.2) eW eP c.1.kind

theorem ubFoldOk_sound {R U : List WP} (nu : List Seg) (M' : Option MPData) (Wl Rtwo : ℚ) (eW eP : ℕ)
    {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData)
    (hf : foldOk R U (cellPieces D nu) = true) (hG : globalOk ((foldL R U).map negW) M' = true)
    (c : TCell × ℚ) (h : ubFoldOk (foldL R U) M' Wl Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.1.ulo : ℝ) ≤ x → x ≤ c.1.uhi →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ (c.2 : ℝ) := by
  intro x hx1 hx2
  unfold ubFoldOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  have key := realCell_sound hG hW hm x hx1 hx2
  rw [negW_sum] at key
  have e := fold_sum hf x
  simp only [rS] at e
  rw [e] at key
  rw [gNu_eq D nu hV]
  have him : (⟨x, 0⟩ : ℂ).im = 0 := rfl
  rw [him] at key ⊢
  simp only [abs_zero, mul_zero, add_zero, neg_neg, Rat.cast_neg, Rat.cast_zero] at key ⊢
  linarith

/-- Chord cap cell on the folded list. -/
def linFoldOk (qs : List WP) (Wl Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (n : ℕ) (lo : ℚ)
    (C : List ℚ) (Fs : ℚ) (a b ua ub : ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ Wl) && decide (a < b) &&
    cellOkFL n (qs.map negW) ⟨(a + b) / 2, 0⟩ ⟨1, 0⟩ ((b - a) / 2) Wl Rtwo 0 lo 0 C Fs eW eP
      ((ua + ub) / 2) ((ub - ua) / (b - a))

theorem linFoldOk_sound {R U : List WP} (nu : List Seg) (Wl Rtwo : ℚ) (eW eP : ℕ)
    {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData)
    (hf : foldOk R U (cellPieces D nu) = true) {n : ℕ} {lo : ℚ} {C : List ℚ} {Fs a b ua ub : ℚ}
    (h : linFoldOk (foldL R U) Wl Rtwo eW eP D n lo C Fs a b ua ub = true) :
    ∀ y : ℝ, (a : ℝ) ≤ y → y ≤ b →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨y, 0⟩ ≤ plLine (a, b, ua, ub) y := by
  intro y hy1 hy2
  unfold linFoldOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hε, hW⟩, hab⟩, hc⟩ := h
  have hWR : (0 : ℝ) ≤ Wl := by exact_mod_cast hW
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have key := cellOkFL_sound hc (y - (((a + b) / 2 : ℚ) : ℝ)) 0 (by
    rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hWR)
  have hz : (⟨((a + b) / 2 : ℚ), 0⟩ : CQ).toC + ((y - (((a + b) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
      (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨y, 0⟩ := by
    apply Complex.ext <;> simp [CQ.toC]
  rw [hz, negW_sum] at key
  have e := fold_sum hf y
  simp only [rS] at e
  rw [e] at key
  rw [gNu_eq D nu hV]
  have him : (⟨y, 0⟩ : ℂ).im = 0 := rfl
  rw [him] at key ⊢
  simp only [abs_zero, mul_zero, add_zero, Rat.cast_zero, zero_mul, zero_add] at key ⊢
  unfold plLine
  simp only
  have hba : (b : ℝ) - a ≠ 0 := by linarith
  have e2 : (((ua + ub) / 2 : ℚ) : ℝ) + (((ub - ua) / (b - a) : ℚ) : ℝ) * (y - (((a + b) / 2 : ℚ) : ℝ))
      = (ua : ℝ) + ((ub : ℝ) - ua) * (y - a) / ((b : ℝ) - a) := by
    push_cast
    field_simp
    ring
  rw [e2] at key
  linarith

end CatalanCore.Uniform.Decay.PolyWire3
