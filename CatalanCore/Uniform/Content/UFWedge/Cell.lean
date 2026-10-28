module

public import CatalanCore.Uniform.Content.UFWire.CellFree
public import CatalanCore.Uniform.Content.UFWedge.Kill

@[expose] public section

/-!
# UF cells with wedge certificates (lane H9)

`UFCellW` is `UFCellF` with the raw wedge hypotheses `hwC`, `hwR` replaced by one
`KillCert` per killed node (`kC`, `kR`): a run start `ts`, a shift (W2), an evaluation point `u₀`,
integer data realising the fibers of the representative `t₀` and of `ts` (supplied per family), and a
nonzero integer cross wedge modulo `p` (W3).  `UFCellW.toF` recovers a `UFCellF`, so the debit layer
`ufLayerF` applies verbatim (`ufLayerW`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.UFWire

namespace CatalanCore.Uniform.Content.UFWedge

set_option maxHeartbeats 1600000 in
/-- The wedge certificate type of the alternating geometry at `(r, p)`. -/
abbrev AltKill (c : ℚ) (hc : 0 < c) {r : ℕ} (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ} [Fact p.Prime]
    (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N) (t0 tv : ℕ) :=
  KillCert (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp
    (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
    ((altGeom c hc).geometry r).ys (alt_hc' c hc hrN) (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN)
    t0 tv

set_option maxHeartbeats 1600000 in
/-- UF input of one `(r, p)` with wedge certificates (instead of raw wedge hypotheses). -/
structure UFCellW (c : ℚ) (hc : 0 < c) (Fr : Frame) (q o : ℕ) (T : TwoTermData Fr q o)
    (r p : ℕ) [Fact p.Prime] where
  hr : r % 2 = 0
  N : ℕ
  hNp : N < p * p
  hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o
  hnorm : Fr.norm ∈ S p
  hnorm0 : red p Fr.norm ≠ 0
  hrN : r + 2 * (altGeom c hc).borderSize r ≤ N
  hp : 2 * (altGeom c hc).borderSize r ≤ p
  hp2 : p ≠ 2
  ho : (o : ZMod p) ≠ 0
  hq : (q : ZMod p) ≠ 0
  t0 : ℕ
  tmax : ℕ
  ht0N : t0 < N
  hrt : r ≤ t0
  htm : tmax < r + p
  hdiv : tmax / p = t0 / p
  hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tmax - t0)
  TC : Finset (Fin ((altGeom c hc).geometry r).k)
  TR : Finset (Fin ((altGeom c hc).geometry r).k)
  kC : ∀ t ∈ TC, AltKill c hc hr T hNp hsq hnorm hnorm0 hrN t0 (((altGeom c hc).geometry r).ys t)
  kR : ∀ t ∈ TR, AltKill c hc hr T hNp hsq hnorm hnorm0 hrN t0 (((altGeom c hc).geometry r).xs t)
  tv : ℕ
  htv0 : t0 ≤ tv
  htv : tv < r + p
  htvN : tv < N
  htvd : tv / p = t0 / p
  hwv : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tv - t0)
  δ₁ : ℕ
  δ₂ : ℕ
  hδ12 : δ₁ ≤ δ₂
  hδ2 : δ₂ ≤ t0
  hlt : t0 - δ₁ < r
  hr3 : r ≤ t0 - δ₂ + p
  hqd : (t0 - δ₂) / p = t0 / p
  hwd : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) (t0 - δ₂) δ₂
  /-- A lower bound for the number of residues of `I_J ∪ K` (all of `TR` counted). -/
  u : ℕ
  hu : u ≤ (((Finset.Icc t0 tv ∪ Finset.Icc (t0 - δ₂) (t0 - δ₁)).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
    ((TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
      (TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card


variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ} {T : TwoTermData Fr q o} {r p : ℕ}
  [Fact p.Prime]

/-- The raw `UFCellF` of a certified cell. -/
noncomputable def UFCellW.toF (X : UFCellW c hc Fr q o T r p) : UFCellF c hc Fr q o T r p where
  hr := X.hr
  N := X.N
  hNp := X.hNp
  hsq := X.hsq
  hnorm := X.hnorm
  hnorm0 := X.hnorm0
  hrN := X.hrN
  hp := X.hp
  hp2 := X.hp2
  ho := X.ho
  hq := X.hq
  t0 := X.t0
  tmax := X.tmax
  ht0N := X.ht0N
  hrt := X.hrt
  htm := X.htm
  hdiv := X.hdiv
  hw := X.hw
  TC := X.TC
  TR := X.TR
  hwC := fun t ht => (X.kC t ht).wedgeC_ne t
    (tt_regRed (p := p) T X.hNp.le X.hsq X.hnorm X.hnorm0) X.ht0N
  hwR := fun t ht => (X.kR t ht).wedgeR_ne t
    (tt_regRed (p := p) T X.hNp.le X.hsq X.hnorm X.hnorm0) X.ht0N
  tv := X.tv
  htv0 := X.htv0
  htv := X.htv
  htvN := X.htvN
  htvd := X.htvd
  hwv := X.hwv
  δ₁ := X.δ₁
  δ₂ := X.δ₂
  hδ12 := X.hδ12
  hδ2 := X.hδ2
  hlt := X.hlt
  hr3 := X.hr3
  hqd := X.hqd
  hwd := X.hwd
  u := X.u
  hu := X.hu

/-- The price bound of a certified cell. -/
theorem UFCellW.price_le (X : UFCellW c hc Fr q o T r p) : X.toF.datum.price ≤ X.toF.bound :=
  X.toF.price_le

/-- **The UF debit layer from certified cells.** -/
noncomputable def ufLayerW {depth : ℕ} (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (cell : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → UFCellW c hc Fr q o T r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (cell r p h).toF.bound ≤ base r p) :
    DebitLayer (altGeom c hc) Fr depth :=
  ufLayerF valid base (fun r p _ h => (cell r p h).toF) hbase

end CatalanCore.Uniform.Content.UFWedge
