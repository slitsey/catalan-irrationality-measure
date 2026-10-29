import CatalanCore.Uniform.Content.BankShared.KTerm.Expr
set_option Elab.async false

/-! # Window and prefix branches of a k-shift catalogue (lane K)

Two families of conditionless-in-`k` branches written for any number of pole lattices (`vk 0, vk 1, …`):

* `kbrWin ns`: the M3D window of `Chi3Content.M3` between the multiples `(n₀ - 1) p, n₀ p` and the pole cuts
  `k_i + (n_i - 1) p, k_i + n_i p` (`ns = [n₀, n₁, …]`; `n_i = 0`: below `k_i`), price `2r + (2m - (hi - lo))`,
  condition `m < p`;
* `kbrPre n j0 js`: the prefix window of `TwoTerm.Prefix` (Theorem 1 of the prefix rule) at the strip `n` (border
  `N_n = r + 2(m - n p)`), between `ap + j0 p, ap + (j0 + 1) p` and the cuts `ap + k_i + (j_i - 1) p,
  ap + k_i + j_i p`, intersected with `[max(r, N_n - p), min(N_n, r + p))`; no conditions.

`kMx`/`kMn` fold a list of expressions into a left-nested `mx`/`mn`; `kMx_ge`, `kMn_le` give the inequalities
with every member. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open KExpr

/-- `max` of a list (left-nested). -/
def kMx : KExpr → List KExpr → KExpr
  | a, [] => a
  | a, x :: l => kMx (.mx a x) l

/-- `min` of a list (left-nested). -/
def kMn : KExpr → List KExpr → KExpr
  | a, [] => a
  | a, x :: l => kMn (.mn a x) l

theorem kMx_ge (r p m : ℕ) (k : ℕ → ℕ) : ∀ (l : List KExpr) (a : KExpr),
    a.evalN r p m k ≤ (kMx a l).evalN r p m k ∧ ∀ x ∈ l, x.evalN r p m k ≤ (kMx a l).evalN r p m k
  | [], a => ⟨le_refl _, fun x hx => absurd hx List.not_mem_nil⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := kMx_ge r p m k l (.mx a y)
    refine ⟨le_trans (le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_trans (le_max_right (a.evalN r p m k) _) h1
    · exact h2 x hx

theorem kMn_le (r p m : ℕ) (k : ℕ → ℕ) : ∀ (l : List KExpr) (a : KExpr),
    (kMn a l).evalN r p m k ≤ a.evalN r p m k ∧ ∀ x ∈ l, (kMn a l).evalN r p m k ≤ x.evalN r p m k
  | [], a => ⟨le_refl _, fun x hx => absurd hx List.not_mem_nil⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := kMn_le r p m k l (.mn a y)
    refine ⟨le_trans h1 (min_le_left _ _), fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_trans h1 (min_le_right (a.evalN r p m k) _)
    · exact h2 x hx

/-- `N = r + 2 m`. -/
def kN : KExpr := .add .vr (.smul 2 .vm)

/-- The point `k_{l-1} + n p` of the pole lattice `l ≥ 1`, or `n p` for `l = 0`. -/
def kLatPt (l n : ℕ) : KExpr := if l = 0 then .smul n .vp else .add (.vk (l - 1)) (.smul n .vp)

/-- Lower cuts of a window: the point `(n_l - 1)` of every lattice `l` with `n_l ≥ 1`. -/
def kWinLos : ℕ → List ℕ → List KExpr
  | _, [] => []
  | l, n :: ns => (if 1 ≤ n then [kLatPt l (n - 1)] else []) ++ kWinLos (l + 1) ns

/-- Upper cuts of a window: the point `n_l` of every lattice `l`. -/
def kWinHis : ℕ → List ℕ → List KExpr
  | _, [] => []
  | l, n :: ns => kLatPt l n :: kWinHis (l + 1) ns

def kWinLo (ns : List ℕ) : KExpr := kMx (.tsub kN .vp) (.vr :: kWinLos 0 ns)
def kWinHi (ns : List ℕ) : KExpr := kMn kN (.add .vr .vp :: kWinHis 0 ns)

/-- The M3D window branch (`ns.length - 1` pole lattices). -/
def kbrWin (ns : List ℕ) : KBranch :=
  ⟨.add (.smul 2 .vr) (.tsub (.smul 2 .vm) (.tsub (kWinHi ns) (kWinLo ns))),
    [⟨0, 1, -1, List.replicate (ns.length - 1) 0, 0, true⟩], 0⟩

/-- `N_n = r + 2 (m - n p)`. -/
def kNn (n : ℕ) : KExpr := .add .vr (.smul 2 (.tsub .vm (.smul n .vp)))

def kPoleLos : ℕ → List ℕ → List KExpr
  | _, [] => []
  | i, j :: js => (if j = 0 then .vr else .add .ap (.add (.vk i) (.smul (j - 1) .vp))) :: kPoleLos (i + 1) js

def kPoleHis : ℕ → List ℕ → List KExpr
  | _, [] => []
  | i, j :: js => .add .ap (.add (.vk i) (.smul j .vp)) :: kPoleHis (i + 1) js

def kPreLo (n j0 : ℕ) (js : List ℕ) : KExpr :=
  kMx (.tsub (kNn n) .vp) (.vr :: .add .ap (.smul j0 .vp) :: kPoleLos 0 js)
def kPreHi (n j0 : ℕ) (js : List ℕ) : KExpr :=
  kMn (kNn n) (.add .vr .vp :: .add .ap (.smul (j0 + 1) .vp) :: kPoleHis 0 js)

/-- The prefix branch (no conditions, debit 0). -/
def kbrPre (n j0 : ℕ) (js : List ℕ) : KBranch :=
  ⟨.add (.smul 2 .vr) (.tsub (.smul 2 .vm) (.tsub (kPreHi n j0 js) (kPreLo n j0 js))), [], 0⟩

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.kMx_ge
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.kMn_le
