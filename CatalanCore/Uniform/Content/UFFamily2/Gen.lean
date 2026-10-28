module

public import CatalanCore.Uniform.Content.UFFamily2.Kill
public import CatalanCore.Uniform.Content.UFFamily.SevELayer

@[expose] public section

/-!
# UF families: the generic window cell and its layer (lane H, H11)

ONE parametric cell for every family whose cell has the shape of families E and H:
J-window `[r, k - 1]` at `t₀ = r`, top-extension window `[lo, r - 1]` (`δ₁ = 1`, `δ₂ = r - lo`), and
kills of every border node `v ≥ k`.  A family supplies

* the affine functions `N, k, lo, m` of `(r, p)` and the arithmetic `Win` (all by `omega`);
* the facts `hsq`, `hnorm`, `hnorm0` and `hsing` (no singular index in `(lo, k - 1]`);
* the kill certificates `kill` of the nodes `v ≥ k` against `t₀ = r`, as produced by `KillCert.ofLu`.

`cellGen` / `cellGen_bound` / `layerGen` do everything else; the price is
`baseGen m r p k lo = 2 (r + m) - (m + σ + (σ - (p - u)))`, `σ = (k - r) - m`,
`u = (k - lo) + (m - (k - r)/2) + (m - (k - r + 1)/2)`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE

namespace CatalanCore.Uniform.Content.UFFamily2

/-- Counting lemma for the number of residues (generalises `SevE.hu_gen`). -/
theorem hu_gen2 {k p lo hi t0 tv d1 d2 : ℕ} [Fact p.Prime] (xs ys : Fin k → ℕ)
    (TC TR : Finset (Fin k)) (hxinj : Function.Injective xs) (hyinj : Function.Injective ys)
    (hxp : ∀ i ∈ TR, xs i < lo + p) (hyp : ∀ i ∈ TC, ys i < lo + p)
    (hTC : ∀ j ∈ TC, hi + 1 ≤ ys j) (hTR : ∀ i ∈ TR, hi + 1 ≤ xs i)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p)) (hlh : lo ≤ hi + 1)
    (hhi : hi < lo + p)
    (hU : Finset.Icc t0 tv ∪ Finset.Icc (t0 - d2) (t0 - d1) = Finset.Icc lo hi) :
    (hi + 1 - lo) + TC.card + TR.card ≤ (((Finset.Icc t0 tv ∪ Finset.Icc (t0 - d2) (t0 - d1)).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
      ((TC.image fun t => (((ys t : ℕ)) : ZMod p)) ∪
        (TR.image fun t => (((xs t : ℕ)) : ZMod p)))).card := by
  classical
  have hinj : ∀ a b : ℕ, lo ≤ a → a < lo + p → lo ≤ b → b < lo + p →
      ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) → a = b := by
    intro a b ha1 ha2 hb1 hb2 hab
    have h1 := (ZMod.natCast_eq_natCast_iff' a b p).1 hab
    rcases le_total a b with hle | hle
    · have hd := (Nat.modEq_iff_dvd' hle).1 h1
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    · have hd := (Nat.modEq_iff_dvd' hle).1 h1.symm
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
  rw [hU]
  have hA : ((Finset.Icc lo hi).image (fun t : ℕ => ((t : ℕ) : ZMod p))).card = hi + 1 - lo := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    exact hinj a b (by omega) (by omega) (by omega) (by omega) hab
  have hB : (TC.image fun t => (((ys t : ℕ)) : ZMod p)).card = TC.card := by
    rw [Finset.card_image_of_injOn]
    intro a ha b hb hab
    have := hTC a ha
    have := hTC b hb
    have := hyp a ha
    have := hyp b hb
    exact hyinj (hinj _ _ (by omega) (by omega) (by omega) (by omega) hab)
  have hC : (TR.image fun t => (((xs t : ℕ)) : ZMod p)).card = TR.card := by
    rw [Finset.card_image_of_injOn]
    intro a ha b hb hab
    have := hTR a ha
    have := hTR b hb
    have := hxp a ha
    have := hxp b hb
    exact hxinj (hinj _ _ (by omega) (by omega) (by omega) (by omega) hab)
  have hBC : Disjoint (TC.image fun t => (((ys t : ℕ)) : ZMod p))
      (TR.image fun t => (((xs t : ℕ)) : ZMod p)) := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hxB
    obtain ⟨i, _, hi'⟩ := Finset.mem_image.1 hxC
    exact hdist i j hi'
  have hAB : Disjoint ((Finset.Icc lo hi).image (fun t : ℕ => ((t : ℕ) : ZMod p)))
      ((TC.image fun t => (((ys t : ℕ)) : ZMod p)) ∪ (TR.image fun t => (((xs t : ℕ)) : ZMod p))) := by
    rw [Finset.disjoint_left]
    intro x hxA hxBC
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hxA
    rw [Finset.mem_Icc] at hn
    rcases Finset.mem_union.1 hxBC with hx | hx
    · obtain ⟨j, hj, hjn⟩ := Finset.mem_image.1 hx
      have := hinj _ _ (by have := hTC j hj; omega) (hyp j hj) (by omega) (by omega) hjn
      have := hTC j hj
      omega
    · obtain ⟨i, hi', hin⟩ := Finset.mem_image.1 hx
      have := hinj _ _ (by have := hTR i hi'; omega) (hxp i hi') (by omega) (by omega) hin
      have := hTR i hi'
      omega
  rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hBC, hA, hB, hC]
  omega

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ}

/-- The core of the alternating geometry covers `range r`. -/
theorem alt_hcov (c : ℚ) (hc : 0 < c) (r : ℕ) :
    ∀ x, x < r → ∃ a : ((altGeom c hc).geometry r).C, (a : ℕ) = x := fun x hx =>
  ⟨⟨x, by rw [altGeom_C c hc r]; exact Finset.mem_range.2 hx⟩, rfl⟩

/-- The arithmetic of a window cell: `m` is the border size, `N` the node bound, `k` the kill
threshold, `lo` the bottom of the top-extension window. -/
structure Win (c : ℚ) (hc : 0 < c) (q o r p N k lo m : ℕ) : Prop where
  hr2 : r % 2 = 0
  hr0 : 0 < r
  hbs : (altGeom c hc).borderSize r = m
  hrN : r + 2 * m ≤ N
  hNp : N < p * p
  hpm : 2 * m ≤ p
  hp2 : 2 < p
  hq0 : 0 < q
  hqp : q < p
  ho0 : 0 < o
  hop : o < p
  hk1 : r + 2 ≤ k
  hk2 : k ≤ r + 2 * m
  hkN : k ≤ N
  hkp : k ≤ r + p
  hdiv : (k - 1) / p = r / p
  hlo1 : lo + 1 ≤ r
  hr3 : r ≤ lo + p
  hqd : lo / p = r / p
  hNl : N ≤ lo + p

set_option maxHeartbeats 1600000 in
/-- **The generic window cell.** -/
noncomputable def cellGen (T : TwoTermData Fr q o) {r p N k lo m : ℕ} [Fact p.Prime]
    (W : Win c hc q o r p N k lo m)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0)
    (hsing : ∀ a Δ : ℕ, lo ≤ a → a + Δ < k →
      NoSingWin (twoTermPoleData T W.hNp.le hsq hnorm hnorm0) a Δ)
    (kill : ∀ v, k ≤ v → v < N →
      AltKill c hc W.hr2 T W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN) r v) :
    UFCellW c hc Fr q o T r p :=
  have hrN : r + 2 * (altGeom c hc).borderSize r ≤ N := W.hbs ▸ W.hrN
  { hr := W.hr2
    N := N
    hNp := W.hNp
    hsq := hsq
    hnorm := hnorm
    hnorm0 := hnorm0
    hrN := hrN
    hp := by have := W.hpm; have := W.hbs; omega
    hp2 := by have := W.hp2; omega
    ho := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => by have := Nat.le_of_dvd W.ho0 hd; have := W.hop; omega
    hq := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => by have := Nat.le_of_dvd W.hq0 hd; have := W.hqp; omega
    t0 := r
    tmax := k - 1
    ht0N := by have := W.hrN; have := W.hk1; have := W.hkN; omega
    hrt := le_rfl
    htm := by have := W.hkp; have := W.hk1; omega
    hdiv := W.hdiv
    hw := hsing r (k - 1 - r) (by have := W.hlo1; omega) (by have := W.hk1; omega)
    TC := Finset.univ.filter fun j => k ≤ ((altGeom c hc).geometry r).ys j
    TR := Finset.univ.filter fun j => k ≤ ((altGeom c hc).geometry r).xs j
    kC := fun t ht => kill _ (by simpa using ht) (alt_hy' c hc W.hr2 hrN t)
    kR := fun t ht => kill _ (by simpa using ht) (alt_hx' c hc W.hr2 hrN t)
    tv := k - 1
    htv0 := by have := W.hk1; omega
    htv := by have := W.hkp; have := W.hk1; omega
    htvN := by have := W.hkN; have := W.hk1; omega
    htvd := W.hdiv
    hwv := hsing r (k - 1 - r) (by have := W.hlo1; omega) (by have := W.hk1; omega)
    δ₁ := 1
    δ₂ := r - lo
    hδ12 := by have := W.hlo1; omega
    hδ2 := by omega
    hlt := by have := W.hr0; omega
    hr3 := by have := W.hr3; have := W.hlo1; omega
    hqd := by rw [show r - (r - lo) = lo by have := W.hlo1; omega]; exact W.hqd
    hwd := hsing (r - (r - lo)) (r - lo) (by have := W.hlo1; omega)
      (by have := W.hk1; have := W.hlo1; omega)
    u := (k - 1 + 1 - lo) +
      (Finset.univ.filter fun j => k ≤ ((altGeom c hc).geometry r).ys j).card +
      (Finset.univ.filter fun j => k ≤ ((altGeom c hc).geometry r).xs j).card
    hu := hu_gen2 (lo := lo) (hi := k - 1) ((altGeom c hc).geometry r).xs
      ((altGeom c hc).geometry r).ys _ _
      (fun a b hab => (((altGeom c hc).geometry r).X'.orderEmbOfFin rfl).injective hab)
      (fun a b hab => (((altGeom c hc).geometry r).Y'.orderEmbOfFin
        ((altGeom c hc).geometry r).card_eq.symm).injective hab)
      (fun i _ => by have := alt_hx' c hc W.hr2 hrN i; have := W.hNl; omega)
      (fun i _ => by have := alt_hy' c hc W.hr2 hrN i; have := W.hNl; omega)
      (fun j hj => by have := (Finset.mem_filter.1 hj).2; have := W.hk1; omega)
      (fun j hj => by have := (Finset.mem_filter.1 hj).2; have := W.hk1; omega)
      (alt_hdist c hc W.hr2 (by have := W.hpm; have := W.hbs; omega))
      (by have := W.hlo1; have := W.hk1; omega)
      (by have := W.hkN; have := W.hNl; have := W.hk1; omega)
      (by have := W.hlo1; have := W.hk1; ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega) }

/-- Explicit price of a window cell. -/
def baseGen (m r p k lo : ℕ) : ℕ :=
  2 * (r + m) - (m + ((k - r) - m) +
    (((k - r) - m) - (p - ((k - 1 + 1 - lo) + (m - (k - r) / 2) + (m - (k - r + 1) / 2)))))

theorem cellGen_bound (T : TwoTermData Fr q o) {r p N k lo m : ℕ} [Fact p.Prime]
    (W : Win c hc q o r p N k lo m) (hsq) (hnorm) (hnorm0) (hsing) (kill) :
    (cellGen T W hsq hnorm hnorm0 hsing kill).toF.bound = baseGen m r p k lo := by
  have hr2 := W.hr2
  have hk1 := W.hk1
  have hkm := W.hk2
  have hs := altGeom_hybShape c hc hr2
  have hbs := W.hbs
  have hk : ((altGeom c hc).geometry r).k = m := by
    show ((altGeom c hc).geometry r).X'.card = _
    rw [altGeom_X c hc hr2, Finset.card_image_of_injective _ (fun a b hab => by simp at hab; omega),
      Finset.card_range, hbs]
  have hC : Fintype.card ((altGeom c hc).geometry r).C = r := by
    rw [Fintype.card_coe, hs.C_eq, Finset.card_range]
  have hRows : (winRows (r := r) c hc r (k - 1)).card = (k - r + 1) / 2 := by
    unfold winRows
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom c hc).geometry r).k =>
      2 * (i : ℕ) < k - r) (fun i _ => by rw [hs.xs_eq]; exact win_iff i hk1),
      card_fin_filter _ (fun n => 2 * n < k - r), card_lt, hk, (cnt_arith hk1 hkm).1]
  have hCols : (winCols (r := r) c hc r (k - 1)).card = (k - r) / 2 := by
    unfold winCols
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom c hc).geometry r).k =>
      2 * (i : ℕ) < k - r - 1) (fun i _ => by rw [hs.ys_eq]; exact wincol_iff i hk1),
      card_fin_filter _ (fun n => 2 * n < k - r - 1), card_lt, hk, (cnt_arith hk1 hkm).2]
  have hTR : (Finset.univ.filter fun j : Fin ((altGeom c hc).geometry r).k =>
      k ≤ ((altGeom c hc).geometry r).xs j).card = m - (k - r + 1) / 2 := by
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom c hc).geometry r).k =>
      ¬ 2 * (i : ℕ) < k - r) (fun i _ => by rw [hs.xs_eq]; exact ge_iff i),
      card_fin_filter _ (fun n => ¬ 2 * n < k - r), card_ge, hk, (cnt_arith hk1 hkm).1]
  have hTC : (Finset.univ.filter fun j : Fin ((altGeom c hc).geometry r).k =>
      k ≤ ((altGeom c hc).geometry r).ys j).card = m - (k - r) / 2 := by
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom c hc).geometry r).k =>
      ¬ 2 * (i : ℕ) < k - r - 1) (fun i _ => by rw [hs.ys_eq]; exact gec_iff i),
      card_fin_filter _ (fun n => ¬ 2 * n < k - r - 1), card_ge, hk, (cnt_arith hk1 hkm).2]
  unfold UFCellF.bound UFCellF.sigma
  have e1 : (cellGen T W hsq hnorm hnorm0 hsing kill).toF.t0 = r := rfl
  have e2 : (cellGen T W hsq hnorm hnorm0 hsing kill).toF.tmax = k - 1 := rfl
  have e3 : (cellGen T W hsq hnorm hnorm0 hsing kill).toF.u = (k - 1 + 1 - lo) +
      (Finset.univ.filter fun j : Fin ((altGeom c hc).geometry r).k =>
        k ≤ ((altGeom c hc).geometry r).ys j).card +
      (Finset.univ.filter fun j : Fin ((altGeom c hc).geometry r).k =>
        k ≤ ((altGeom c hc).geometry r).xs j).card := rfl
  rw [e1, e2, e3, hRows, hCols, hTC, hTR, hk, Fintype.card_sum, hC, Fintype.card_fin, baseGen]
  clear hRows hCols hTR hTC hs hbs hk hC e1 e2 e3
  omega

/-- **The UF debit layer of a window family.**  `valid` selects the `(r, p)` of the family, and the
affine data `N k lo m` and the witnesses are given per valid `(r, p)`. -/
noncomputable def layerGen (T : TwoTermData Fr q o) {depth : ℕ} (valid : ℕ → ℕ → Prop)
    (N k lo m : ℕ → ℕ → ℕ)
    (W : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → Win c hc q o r p (N r p) (k r p) (lo r p) (m r p))
    (hsq : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → ∀ t, 1 ≤ t → t < N r p → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → Fr.norm ∈ S p)
    (hnorm0 : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → red p Fr.norm ≠ 0)
    (hsing : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, ∀ a Δ : ℕ, lo r p ≤ a → a + Δ < k r p →
      NoSingWin (twoTermPoleData T (W r p h).hNp.le (hsq r p h) (hnorm r p h) (hnorm0 r p h)) a Δ)
    (kill : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, ∀ v, k r p ≤ v → v < N r p →
      AltKill c hc (W r p h).hr2 T (W r p h).hNp (hsq r p h) (hnorm r p h) (hnorm0 r p h)
        ((W r p h).hbs ▸ (W r p h).hrN) r v) :
    DebitLayer (altGeom c hc) Fr depth :=
  ufLayerW (T := T) valid (fun r p => baseGen (m r p) r p (k r p) (lo r p))
    (fun r p _ h => cellGen T (W r p h) (hsq r p h) (hnorm r p h) (hnorm0 r p h) (hsing r p h)
      (kill r p h))
    (fun r p _ h => (cellGen_bound T (W r p h) _ _ _ _ _).le)

end CatalanCore.Uniform.Content.UFFamily2

