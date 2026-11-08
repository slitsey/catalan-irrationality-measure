module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Expr

@[expose] public section
set_option Elab.async false

/-!
# Plane 2 content: the branch catalogue at `α = 3/41` (lane H, wave P210; ledger P210, P213)

Branches `KBranch` over `(r, p, m, k₀)` with the single shift `(2, 1, 1)`, `k₀ = (p+1)/2` (`vk 0`).  Cells of a node
`t`, relative to `a = p ⌊r/p⌋`, are cut at `x = t - a`: `[0,h)`, `[h,p)`, `[p,p+h)`, `[p+h,2p)`, `h = vk 0`.
A *vector* `W = (w₀,w₁,w₂,w₃)` of symmetric weights gives the price `∑_c w_c len_c` of a window `[lo,hi)`
(positions relative to `a`), `len_c = (min(hi, end_c) ∸ max(lo, start_c))`.

* `brBand par W k`: row `P₁` on the band `k p ≤ 2m < (k+1) p`, `par = k mod 2`
  (`3(r+m) ∸ 3‖m‖ + ∑_c w_c len_c`, window `E`).
* `brPlain`: row `P₁` with the unit dual, `3(r+m) ∸ ‖m‖`, for `p ≤ 2m`.
* `brE1 W`, `brE2 W`: rows `E₁` (`p > 2m`), `E₂` (`p ≤ r`, `N ≤ 2p`) with the window `[sp, sp + 2m)`.
* `brP4 .. brP7`, `brTail`: rows `P₄ .. P₇` and the tail `p > 2N` (price 0).
Every branch carries the guard `400 p - r ≥ 0` (`p ≥ r/400`), except the tail/P7 which already imply it... all carry it
for uniformity of the validity proofs.  Debit `0` everywhere.
-/

namespace CatalanCore.Uniform.Bank.Plane2.Content

open CatalanCore.Uniform.Content.BankShared.KTerm KExpr

/-- A symmetric weight vector on the four cells. -/
abbrev Vec := ℕ × ℕ × ℕ × ℕ

/-- The five symmetric duals of the cell weight on four cells. -/
def vecs : List Vec := [(2, 2, 0, 1), (2, 2, 1, 0), (0, 1, 2, 2), (1, 0, 2, 2), (1, 1, 1, 1)]

/-- `h = (p + 1) / 2`. -/
def hk : KExpr := .vk 0
/-- `N = r + 2 m`. -/
def Nx : KExpr := .add .vr (.smul 2 .vm)

/-- Start of cell `c` (relative to `p ⌊r/p⌋`). -/
def cstart : ℕ → KExpr
  | 0 => .cst 0
  | 1 => hk
  | 2 => .vp
  | _ => .add .vp hk
/-- End of cell `c`. -/
def cend : ℕ → KExpr
  | 0 => hk
  | 1 => .vp
  | 2 => .add .vp hk
  | _ => .smul 2 .vp

/-- Length of the intersection of the window `[lo, hi)` with cell `c`. -/
def clen (c : ℕ) (lo hi : KExpr) : KExpr := .tsub (.mn hi (cend c)) (.mx lo (cstart c))

/-- `∑_c w_c len_c`. -/
def wsum (W : Vec) (lo hi : KExpr) : KExpr :=
  .add (.add (.add (.smul W.1 (clen 0 lo hi)) (.smul W.2.1 (clen 1 lo hi)))
    (.smul W.2.2.1 (clen 2 lo hi))) (.smul W.2.2.2 (clen 3 lo hi))

/-- Window of the row `P₁`: `[sp, sp + 2‖m‖)` for even `k`, `[sp + p ∸ 2‖m‖, sp + p)` for odd `k`. -/
def winLo (par : ℕ) : KExpr := if par % 2 = 0 then .sp else .tsub (.add .sp .vp) (.smul 2 (.dist .vm))
def winHi (par : ℕ) : KExpr := if par % 2 = 0 then .add .sp (.smul 2 (.dist .vm)) else .add .sp .vp

/-- The guard `400 p - r ≥ 0`. -/
def gGuard : KCond := ⟨-1, 400, 0, [], 0, false⟩

/-- Row `P₁` on the band `k`. -/
def brBand (par : ℕ) (W : Vec) (k : ℕ) : KBranch :=
  ⟨.add (.tsub (.smul 3 (.add .vr .vm)) (.smul 3 (.dist .vm))) (wsum W (winLo par) (winHi par)),
    [⟨0, -(k : ℤ), 2, [], 0, false⟩, ⟨0, (k : ℤ) + 1, -2, [], 0, true⟩, gGuard], 0⟩

/-- Row `P₁` with the unit dual: `3(r+m) ∸ ‖m‖`, `p ≤ 2m`. -/
def brPlain : KBranch :=
  ⟨.tsub (.smul 3 (.add .vr .vm)) (.dist .vm), [⟨0, -1, 2, [], 0, false⟩, gGuard], 0⟩

/-- Row `E₁` (`p > 2m`): `3 r + ∑_c w_c len_c` on the window `[sp, sp + 2m)`. -/
def brE1 (W : Vec) : KBranch :=
  ⟨.add (.smul 3 .vr) (wsum W .sp (.add .sp (.smul 2 .vm))), [⟨0, 1, -2, [], 0, true⟩, gGuard], 0⟩

/-- Row `E₂` (`p ≤ r`, `N ≤ 2p`): `4r - 2p + 2m + ∑_c w_c len_c`. -/
def brE2 (W : Vec) : KBranch :=
  ⟨.add (.tsub (.add (.smul 4 .vr) (.smul 2 .vm)) (.smul 2 .vp)) (wsum W .sp (.add .sp (.smul 2 .vm))),
    [⟨1, -1, 0, [], 0, false⟩, ⟨-1, 2, -2, [], 0, false⟩, gGuard], 0⟩

/-- Row `P₄` (`p ≤ r`): `6(r+m) ∸ 5p`. -/
def brP4 : KBranch := ⟨.tsub (.smul 6 (.add .vr .vm)) (.smul 5 .vp), [⟨1, -1, 0, [], 0, false⟩, gGuard], 0⟩
/-- Row `P₅` (`r ≤ p ≤ N`): `r + 3N ∸ 3p`. -/
def brP5 : KBranch :=
  ⟨.tsub (.add .vr (.smul 3 Nx)) (.smul 3 .vp), [⟨-1, 1, 0, [], 0, false⟩, ⟨1, -1, 2, [], 0, false⟩, gGuard], 0⟩
/-- Row `P₆` (`N ≤ p ≤ 2r`): `2r + 2m + 1 ∸ p`. -/
def brP6 : KBranch :=
  ⟨.tsub (.add (.add (.smul 2 .vr) (.smul 2 .vm)) (.cst 1)) .vp,
    [⟨-1, 1, -2, [], 0, false⟩, ⟨2, -1, 0, [], 0, false⟩, gGuard], 0⟩
/-- Row `P₇` (`p ≥ 2r`): `N + 1 ∸ (p+1)/2`, i.e. `N ∸ (p-1)/2`. -/
def brP7 : KBranch := ⟨.tsub (.add Nx (.cst 1)) hk, [⟨-2, 1, 0, [], 0, false⟩, gGuard], 0⟩
/-- The tail `p > 2N`: price `0`. -/
def brTail : KBranch := ⟨.cst 0, [⟨-2, 1, -4, [], 0, true⟩], 0⟩

/-- The head rows (`θ ≥ 2α`). -/
def headList : List KBranch :=
  [brP4, brP5, brP6, brP7, brTail] ++ vecs.map brE1 ++ vecs.map brE2

/-- The band rows of the bands `k₀ + 1 .. k₀ + n` (both parities, five vectors) and the plain row. -/
def bandList (k0 n : ℕ) : List KBranch :=
  brPlain :: ((List.range n).flatMap fun i => vecs.map (fun W => brBand (k0 + 1 + i) W (k0 + 1 + i)))

end CatalanCore.Uniform.Bank.Plane2.Content
