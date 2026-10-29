import CatalanCore.Uniform.Content.BankShared.Check.Cover
set_option Elab.async false

/-! # The generic branch catalogue (lane C1L; C1/PAPER.md Theorem A)

The branches of Theorem A as `𝔈`-expressions with their validity conditions, for every two-term bank (the root class
enters only through `κ = j/q` in the profile):

* table T: `brD1 = 2(r+m)`, `brD1x = 2r + 2m - δ_p(m)`, `brD2`, `brD3 = 2r + m`, `brD45`, `brD6 = 2m - (k - r)`
  (`tableT`, in this order; `brD6` gives the tail);
* `brLP1`, `brLP2` (strict), debit 1 (the closed forms of `lp1_gle_tt`/`lp2_gle_tt`);
* `brWin n0 n1`: the M3D window between the multiples `n0 p`, `(n0+1) p` and the pole cuts `k + (n1-1) p`, `k + n1 p`
  (`n1 = 0`: below `k`), price `2r + (2m - (b - a))` (`m3_gap_tt`);
* `brRank`: C2's closed rank price `Π_R` (3.1), without the `(0,0), (1,0)` exclusion.

Conditions are named as in C1's `layers.conditions`. -/

namespace CatalanCore.Uniform.Content.BankShared.Check

open Expr

namespace Cat

/-- `p ≤ r` -/
def cPler : Cond := ⟨1, -1, 0, 0, 0, false⟩
/-- `r < p` -/
def cRltp : Cond := ⟨-1, 1, 0, 0, 0, true⟩
/-- `2m < p` -/
def c2mltp : Cond := ⟨0, 1, -2, 0, 0, true⟩
/-- `2m ≤ p` -/
def c2mlep : Cond := ⟨0, 1, -2, 0, 0, false⟩
/-- `k ≤ r` -/
def cKler : Cond := ⟨1, 0, 0, -1, 0, false⟩
/-- `r ≤ k` -/
def cRlek : Cond := ⟨-1, 0, 0, 1, 0, false⟩
/-- `N ≤ p` -/
def cNlep : Cond := ⟨-1, 1, -2, 0, 0, false⟩
/-- `N ≤ 2p` -/
def cNle2p : Cond := ⟨-1, 2, -2, 0, 0, false⟩
/-- `r < p + k` -/
def cRltpk : Cond := ⟨-1, 1, 0, 1, 0, true⟩
/-- `N ≤ p + k` -/
def cNlepk : Cond := ⟨-1, 1, -2, 1, 0, false⟩
/-- `p < r + m` -/
def cPltrm : Cond := ⟨1, -1, 1, 0, 0, true⟩
/-- `m < p` -/
def cMltp : Cond := ⟨0, 1, -1, 0, 0, true⟩

/-- `N = r + 2m`. -/
def eN : Expr := add vr (smul 2 vm)

def tD1 : Expr := smul 2 (add vr vm)
def tD1x : Expr := tsub (add (smul 2 vr) (smul 2 vm)) (dist vm)
def u0 : Expr := tsub (add vk vp) vr
def tD2 : Expr := add (add (smul 2 (tsub vr u0)) (smul 2 vm)) (mn u0 (smul 2 vm))
def tD3 : Expr := add (smul 2 vr) vm
def tD45 : Expr := add (add (smul 2 (tsub vr vk)) (smul 2 vm)) (tsub (smul 2 vm) (tsub vp vr))
def tD6 : Expr := tsub (smul 2 vm) (tsub vk vr)
def wLP : Expr := tsub (add vp vk) vr
def tLP1 : Expr :=
  tsub (add (add (smul 2 (tsub vr (tsub vk (tsub vr vp)))) (smul 2 vm)) (mn (smul 2 vm) wLP))
    (tsub (mn wLP (smul 2 vm)) vm)
def tLP2 : Expr :=
  tsub (add (add (smul 2 (tsub vr vk)) (smul 2 vm)) (tsub (smul 2 vm) (tsub vp vr))) (tsub vm (tsub vp vr))

/-- The M3D window `[a, b)`. -/
def winLo (n0 n1 : ℕ) : Expr :=
  mx (mx (tsub eN vp) vr) (mx (smul n0 vp) (if n1 = 0 then vr else add vk (smul (n1 - 1) vp)))
def winHi (n0 n1 : ℕ) : Expr :=
  mn (mn eN (add vr vp)) (mn (smul (n0 + 1) vp) (add vk (smul n1 vp)))
def tWin (n0 n1 : ℕ) : Expr := add (smul 2 vr) (tsub (smul 2 vm) (tsub (winHi n0 n1) (winLo n0 n1)))

/-- C2's window counts `W(k, z)` and the rank price `Π_R`. -/
def nsq : Expr := tsub (mn vr vk) (tsub eN vp)
def w00 : Expr := tsub (mn eN vk) vr
def w10 : Expr := tsub (mn eN (add vp vk)) (mx vr vp)
def wh0 : Expr := tsub (mn eN (add ap vk)) (mx vr ap)
def wh1 : Expr := tsub (mn eN (add ap vp)) (mx vr (add ap vk))
def ap1 : Expr := add ap vp
def wh10 : Expr := tsub (mn eN (add ap1 vk)) (mx vr ap1)
def wh11 : Expr := tsub (mn eN (add ap1 vp)) (mx vr (add ap1 vk))
def tRank : Expr :=
  tsub (smul 2 (add vr vm))
    (mx (mx (add vm nsq) (add (add w00 w10) (smul 2 nsq))) (mx (mx wh0 wh1) (mx wh10 wh11)))

end Cat

open Cat

def brD1 : Branch := ⟨tD1, [], 0⟩
def brD1x : Branch := ⟨tD1x, [], 0⟩
def brD2 : Branch := ⟨tD2, [c2mltp, cPler, cKler], 0⟩
def brD3 : Branch := ⟨tD3, [c2mltp, cPler], 0⟩
def brD45 : Branch := ⟨tD45, [cRltp], 0⟩
def brD6 : Branch := ⟨tD6, [cNlep, cRlek], 0⟩
def brLP1 : Branch := ⟨tLP1, [cNle2p, cPler, cRltpk, cKler], 1⟩
def brLP2 : Branch := ⟨tLP2, [cRltp, cKler, cNlepk, cPltrm], 1⟩
def brWin (n0 n1 : ℕ) : Branch := ⟨tWin n0 n1, [cMltp], 0⟩
def brRank : Branch := ⟨tRank, [c2mltp], 0⟩

/-- Table T (indices 0-5 of every catalogue). -/
def tableT : List Branch := [brD1, brD1x, brD2, brD3, brD45, brD6]

theorem brD6_mem (extra : List Branch) : brD6 ∈ tableT ++ extra := by simp [tableT]

theorem evalN_tD6 (r p m k : ℕ) : tD6.evalN r p m k = 2 * m - (k - r) := rfl
theorem evalN_tLP1 (r p m k : ℕ) : tLP1.evalN r p m k =
    2 * (r - (k - (r - p))) + 2 * m + min (2 * m) (p + k - r) - (min (p + k - r) (2 * m) - m) := rfl
theorem evalN_tLP2 (r p m k : ℕ) : tLP2.evalN r p m k =
    2 * (r - k) + 2 * m + (2 * m - (p - r)) - (m - (p - r)) := rfl
theorem evalN_tD1 (r p m k : ℕ) : tD1.evalN r p m k = 2 * (r + m) := rfl
theorem evalN_tD1x (r p m k : ℕ) : tD1x.evalN r p m k = 2 * r + 2 * m - min (m % p) (p - m % p) := rfl
theorem evalN_tD2 (r p m k : ℕ) : tD2.evalN r p m k =
    2 * (r - (k + p - r)) + 2 * m + min (k + p - r) (2 * m) := rfl
theorem evalN_tD3 (r p m k : ℕ) : tD3.evalN r p m k = 2 * r + m := rfl
theorem evalN_tD45 (r p m k : ℕ) : tD45.evalN r p m k = 2 * (r - k) + 2 * m + (2 * m - (p - r)) := rfl

end CatalanCore.Uniform.Content.BankShared.Check
