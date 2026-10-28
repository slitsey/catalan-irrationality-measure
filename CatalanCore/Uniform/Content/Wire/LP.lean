module

public import CatalanCore.Uniform.Content.Wire.Shape
public import CatalanCore.Uniform.Content.Smith.LP1
public import CatalanCore.Uniform.Content.Smith.LP2

@[expose] public section

/-!
# `LPDatum` from LP1 / LP2 (lane H6, task 1)

The H5 interface `DebitLayer.LPDatum Fr G r p` (potentials, integral lift, rank bound of the
reduction of the FULL matrix of the geometry at scale `r`) is discharged for two-term frames
from the rank witnesses `LP1Hyp.gleAt` / `LP2Hyp.gleAt` (lane H3), by relabelling the geometry
matrix onto `Fin r ⊕ Fin m` (`HybShape`).  Deletion members are then priced by the H5 theorem
`lpd_member_debit` (the `gle_sub` mechanism: a member reduction is a submatrix of the full one).
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.Wire

variable {G : BlockGeom} {Fr : Frame} {depth : ℕ} {r : ℕ} {p : ℕ} [Fact p.Prime]

theorem exists_lift (hs : HybShape G r)
    {u v : Fin r ⊕ Fin (G.geometry r).k → ℕ} {c : ℕ}
    (h : HasRankWit Fr p r (G.geometry r).k u v c) :
    ∃ Bl : Matrix ((G.geometry r).C ⊕ Fin (G.geometry r).k)
        ((G.geometry r).C ⊕ Fin (G.geometry r).k) (LocRing p)[X],
      (∀ i j, toQ p (Bl i j) = C ((p : ℚ) ^ (u (hs.lab i) + v (hs.lab j))) *
        FullN Fr (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs (G.geometry r).ys
          (X : ℚ[X]) i j) ∧
      (Bl.map (phiP p)).rank + c ≤ Fintype.card ((G.geometry r).C ⊕ Fin (G.geometry r).k) := by
  obtain ⟨Bbar, hB, hrk⟩ := h
  choose g hg1 hg2 using hB
  refine ⟨Matrix.of fun a b => g (hs.lab a) (hs.lab b), ?_, ?_⟩
  · intro a b
    rw [hs.fullN_apply]
    exact hg1 (hs.lab a) (hs.lab b)
  · have hmap : (Matrix.of fun a b => g (hs.lab a) (hs.lab b)).map (phiP p) =
        Bbar.submatrix hs.lab hs.lab := by
      ext a b
      simp [hg2]
    rw [hmap]
    have h1 := Matrix.rank_submatrix_le Bbar hs.lab hs.lab
    have hc : Fintype.card ((G.geometry r).C ⊕ Fin (G.geometry r).k) =
        r + (G.geometry r).k := by
      rw [Fintype.card_congr hs.lab]; simp
    omega

/-- A rank witness for the standard hybrid matrix gives an `LPDatum` of a hybrid-shaped geometry. -/
noncomputable def lpDatumOfWit (hs : HybShape G r)
    {u v : Fin r ⊕ Fin (G.geometry r).k → ℕ} {c : ℕ}
    (h : HasRankWit Fr p r (G.geometry r).k u v c) : DebitLayer.LPDatum Fr G r p where
  u := fun a => u (hs.lab a)
  v := fun a => v (hs.lab a)
  Bl := (exists_lift hs h).choose
  c := c
  hB := (exists_lift hs h).choose_spec.1
  hrk := (exists_lift hs h).choose_spec.2

theorem lpDatumOfWit_u (hs : HybShape G r)
    {u v : Fin r ⊕ Fin (G.geometry r).k → ℕ} {c : ℕ}
    (h : HasRankWit Fr p r (G.geometry r).k u v c) :
    ∑ a, (lpDatumOfWit hs h).u a = ∑ a, u a :=
  Equiv.sum_comp hs.lab u

theorem lpDatumOfWit_v (hs : HybShape G r)
    {u v : Fin r ⊕ Fin (G.geometry r).k → ℕ} {c : ℕ}
    (h : HasRankWit Fr p r (G.geometry r).k u v c) :
    ∑ a, (lpDatumOfWit hs h).v a = ∑ a, v a :=
  Equiv.sum_comp hs.lab v

/-- Full-member price of LP2: `Σ(u+v) - (m - (p - r))` with the D4 potentials. -/
def lp2Base (G : BlockGeom) (kf : ℕ → ℕ → ℕ) (r p : ℕ) : ℕ :=
  ∑ a : Fin r ⊕ Fin (G.geometry r).k, uPot p r (kf r p) (Frame.hybRow r (G.geometry r).k a) +
    ∑ a : Fin r ⊕ Fin (G.geometry r).k, uPot p r (kf r p) (Frame.hybCol r (G.geometry r).k a) -
      ((G.geometry r).k - (p - r))

/-- Window of LP2: hybrid shape, and the two-term configuration with `p < r + m`. -/
def lp2Valid (G : BlockGeom) (Fr : Frame) (q o : ℕ) (kf jf : ℕ → ℕ → ℕ) (r p : ℕ) : Prop :=
  HybShape G r ∧ ∀ [Fact p.Prime],
    LP2Hyp Fr p q o r (G.geometry r).k (kf r p) (jf r p) ∧ p < r + (G.geometry r).k

/-- **LP2 layer (debit 1)** for hybrid-shaped two-term block geometries. -/
noncomputable def lp2Layer (G : BlockGeom) (Fr : Frame) (depth : ℕ) (q o : ℕ)
    (kf jf : ℕ → ℕ → ℕ) : DebitLayer G Fr depth :=
  DebitLayer.lpd (lp2Valid G Fr q o kf jf) (lp2Base G kf)
    (fun r p _ h => lpDatumOfWit h.1 ((h.2.1).gleAt h.2.2))
    (fun r p _ h => by
      rw [lpDatumOfWit_u, lpDatumOfWit_v]
      rfl)

/-- Full-member price of LP1: `Σ(w+w) - (min(p+k-r, 2m) - m)`. -/
def lp1Base (G : BlockGeom) (kf : ℕ → ℕ → ℕ) (r p : ℕ) : ℕ :=
  ∑ a : Fin r ⊕ Fin (G.geometry r).k, wC p r (kf r p) (Frame.hybRow r (G.geometry r).k a) +
    ∑ a : Fin r ⊕ Fin (G.geometry r).k, wC p r (kf r p) (Frame.hybCol r (G.geometry r).k a) -
      (min (p + kf r p - r) (2 * (G.geometry r).k) - (G.geometry r).k)

def lp1Valid (G : BlockGeom) (Fr : Frame) (q o : ℕ) (kf jf : ℕ → ℕ → ℕ) (r p : ℕ) : Prop :=
  HybShape G r ∧ ∀ [Fact p.Prime], LP1Hyp Fr p q o r (G.geometry r).k (kf r p) (jf r p)

/-- **LP1 layer (debit 1).** -/
noncomputable def lp1Layer (G : BlockGeom) (Fr : Frame) (depth : ℕ) (q o : ℕ)
    (kf jf : ℕ → ℕ → ℕ) : DebitLayer G Fr depth :=
  DebitLayer.lpd (lp1Valid G Fr q o kf jf) (lp1Base G kf)
    (fun r p _ h => lpDatumOfWit h.1 (h.2.gleAt))
    (fun r p _ h => by
      rw [lpDatumOfWit_u, lpDatumOfWit_v]
      rfl)

end CatalanCore.Uniform.Content.Wire
