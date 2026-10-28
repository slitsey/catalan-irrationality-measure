module

public import CatalanCore.Uniform.Content.UFMoments.HB0

@[expose] public section

/-!
# The UF Smith datum of the alternating geometry (two-term frames), all matrix hypotheses discharged

`altSmithJKDatum_UF`: the `SmithJKDatum` with `J` = (S7) block of the window `[t₀, t_max]`; the only
hypotheses are frame data, the cell inequalities and the window arithmetic (one arc, one chain length).
`altSmithJKDatum_UF_price`: its price bound with any transport window `[t₀, t_v]`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.Content.UFMoments

variable (c : ℚ) (hc : 0 < c) {r : ℕ}

/-- **The UF Smith datum of the alternating geometry.** -/
noncomputable def altSmithJKDatum_UF (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ} [Fact p.Prime]
    (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0)
    (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (hp : 2 * (altGeom c hc).borderSize r ≤ p) (hp2 : p ≠ 2)
    (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (t0 tmax : ℕ) (ht0N : t0 < N) (hrt : r ≤ t0) (htm : tmax < r + p)
    (hdiv : tmax / p = t0 / p)
    (hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tmax - t0)) :
    SmithJKDatum (altGeom c hc) Fr r p :=
  altSmithJKDatum_S7 c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax hrt htm hdiv hw
    (hB0_auto (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp _ _ _ (alt_hc' c hc hrN)
      (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 ht0N)

theorem altSmithJKDatum_UF_price (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ} [Fact p.Prime]
    (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0)
    (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (hp : 2 * (altGeom c hc).borderSize r ≤ p) (hp2 : p ≠ 2)
    (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (t0 tmax : ℕ) (ht0N : t0 < N) (hrt : r ≤ t0) (htm : tmax < r + p)
    (hdiv : tmax / p = t0 / p)
    (hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tmax - t0))
    (tv : ℕ) (htv0 : t0 ≤ tv) (htv : tv < r + p) (htvN : tv < N) (htvd : tv / p = t0 / p)
    (htvp : tv - t0 < p)
    (hwv : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tv - t0)) :
    (altSmithJKDatum_UF c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax ht0N hrt htm hdiv
        hw).price ≤
      2 * Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) -
        (Fintype.card (Fin ((altGeom c hc).geometry r).k) +
          (((winRows (r := r) c hc t0 tmax).card + (winCols (r := r) c hc t0 tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k)) +
            (((winRows (r := r) c hc t0 tmax).card + (winCols (r := r) c hc t0 tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k)) - (p - (tv + 1 - t0))))) :=
  altSmithJKDatum_S7_price c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax hrt htm hdiv hw
    (hB0_auto (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp _ _ _ (alt_hc' c hc hrN)
      (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 ht0N) tv htv0 htv htvN htvd htvp hwv

end CatalanCore.Uniform.Content.UFMoments
