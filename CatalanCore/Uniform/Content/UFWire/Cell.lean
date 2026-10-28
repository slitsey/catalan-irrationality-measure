module

public import CatalanCore.Uniform.Content.UFMoments.AltK

@[expose] public section

/-!
# UF cells and the UF debit layer of the alternating geometry (lane H8)

A `UFCell` is the complete per-`(r, p)` input of `altSmithJKDatum_UFK`: the window arithmetic
(`t₀, t_max, t_v, δ₁, δ₂`, nonsingular windows, arcs), the cell inequalities, and the
wedge-nonvanishing certificates for the killed outside border columns/rows `TC`, `TR`.
Everything about matrices is already proved in `UFMoments`; a cell contains only arithmetic and
exact-evaluation facts.

* `UFCell.datum`: the `SmithJKDatum` (J-block of the window `[t₀, t_max]` with wedge kills).
* `UFCell.bound`: the price `2(|C|+m) - (m + σ + (σ - (p - u)))`, `u ≤ |I_J ∪ K|` a lower bound of the
  retained-complement count (transport window + top-extension window + killed residues).
* `UFCell.price_le`: the datum's price is at most `bound`.
* `ufLayer`: a `DebitLayer` (debit 1) from a family of cells on a validity window.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.UFWire

set_option maxHeartbeats 1600000 in
/-- The full UF input of one `(r, p)`: frame data of `p`, window arithmetic and wedge certificates. -/
structure UFCell (c : ℚ) (hc : 0 < c) (Fr : Frame) (q o : ℕ) (T : TwoTermData Fr q o)
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
  hwC : ∀ t ∈ TC, wedgeC (altLift c hc hr T hNp hsq hnorm hnorm0 hrN) Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).ys
      (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
        (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0
  hwR : ∀ t ∈ TR, wedgeR (altLift c hc hr T hNp hsq hnorm hnorm0 hrN) Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
      (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
        (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0
  hvR : ∀ t ∈ TR, vS7 p q o Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
      (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
      ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p) ≠ 0
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
  /-- A lower bound for the number of residues of `I_J ∪ K`. -/
  u : ℕ
  hu : u ≤ (((Finset.Icc t0 tv ∪ Finset.Icc (t0 - δ₂) (t0 - δ₁)).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
    ((TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
      (TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ} {T : TwoTermData Fr q o} {r p : ℕ}
  [Fact p.Prime]

/-- The `SmithJKDatum` of a cell. -/
noncomputable def UFCell.datum (X : UFCell c hc Fr q o T r p) : SmithJKDatum (altGeom c hc) Fr r p :=
  altSmithJKDatum_UFK c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN X.hp X.hp2 X.ho X.hq X.t0
    X.tmax X.ht0N X.hrt X.htm X.hdiv X.hw X.TC X.TR X.hwC X.hwR X.hvR

/-- `σ = |Jr| + |Jc| - m`: the number of border nodes in the J-window, counted with multiplicity. -/
noncomputable def UFCell.sigma (X : UFCell c hc Fr q o T r p) : ℕ :=
  (winRows (r := r) c hc X.t0 X.tmax).card + (winCols (r := r) c hc X.t0 X.tmax).card -
    Fintype.card (Fin ((altGeom c hc).geometry r).k)

/-- The Smith price of a cell: `2(|C|+m) - (m + σ + (σ - (p - u)))`. -/
noncomputable def UFCell.bound (X : UFCell c hc Fr q o T r p) : ℕ :=
  2 * Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) -
    (Fintype.card (Fin ((altGeom c hc).geometry r).k) + (X.sigma + (X.sigma - (p - X.u))))

theorem UFCell.price_le (X : UFCell c hc Fr q o T r p) : X.datum.price ≤ X.bound := by
  have h := altSmithJKDatum_UFK_price c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN X.hp X.hp2
    X.ho X.hq X.t0 X.tmax X.ht0N X.hrt X.htm X.hdiv X.hw X.TC X.TR X.hwC X.hwR X.hvR X.tv X.htv0
    X.htv X.htvN X.htvd X.hwv X.δ₁ X.δ₂ X.hδ12 X.hδ2 X.hlt X.hr3 X.hqd X.hwd
  unfold UFCell.bound UFCell.sigma
  have hu := X.hu
  generalize (((Finset.Icc X.t0 X.tv ∪ Finset.Icc (X.t0 - X.δ₂) (X.t0 - X.δ₁)).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
    ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
      (X.TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card = U at h hu
  show X.datum.price ≤ _
  have h' : X.datum.price ≤
      2 * Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) -
        (Fintype.card (Fin ((altGeom c hc).geometry r).k) +
          ((((winRows (r := r) c hc X.t0 X.tmax).card + (winCols (r := r) c hc X.t0 X.tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k))) +
            ((((winRows (r := r) c hc X.t0 X.tmax).card + (winCols (r := r) c hc X.t0 X.tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k))) - (p - U)))) := h
  generalize ((winRows (r := r) c hc X.t0 X.tmax).card + (winCols (r := r) c hc X.t0 X.tmax).card -
    Fintype.card (Fin ((altGeom c hc).geometry r).k)) = s at h' ⊢
  omega

end CatalanCore.Uniform.Content.UFWire
