module

public import CatalanCore.Uniform.Decay.NearCells.Cell

@[expose] public section
set_option Elab.async false

/-!
# Endpoint-merged jet remainders: data structures (lane D, package D6d)

A *term* `⟨q, P⟩` stands for the remainder `rem_n(P, q)(s) = (∑_{j<n} P_j s^j) Log(1 - q s) - jet_n(P, q)(s)`.
Terms with the same `q` are added before taking norms (`mergeAll`); `tmErr` is the resulting bound.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools

structure Tm where
  q : CQ
  P : List CQ

def czero : CQ := ⟨0, 0⟩

/-- Coefficient `j` of a `CQ` list (zero beyond the end). -/
def ccoef (l : List CQ) (j : ℕ) : CQ := l.getD j czero

def addC : List CQ → List CQ → List CQ
  | [], l => l
  | l, [] => l
  | x :: xs, y :: ys => CQ.add x y :: addC xs ys

def scaleC (w : ℚ) (l : List CQ) : List CQ := l.map (CQ.smul w)

def cqEq (a b : CQ) : Bool := decide (a.re = b.re) && decide (a.im = b.im)

/-- Insert a term, adding polynomials when the keys agree. -/
def insTm (t : Tm) : List Tm → List Tm
  | [] => [t]
  | u :: us => if cqEq t.q u.q then ⟨u.q, addC t.P u.P⟩ :: us else u :: insTm t us

def mergeAll : List Tm → List Tm
  | [] => []
  | t :: ts => insTm t (mergeAll ts)

/-- `‖q‖ h` bound (rational, `< 1` is checked). -/
def rOf (q : CQ) (h : ℚ) : ℚ := sqrtUp (q.nsq * h ^ 2)

def tmErr (n : ℕ) (h : ℚ) (T : List Tm) : ℚ :=
  (T.map fun t => jbQ (ccoef t.P) n (rOf t.q h) h).sum

def tmOk (h : ℚ) (T : List Tm) : Bool :=
  decide (0 ≤ h) && T.all fun t => decide (rOf t.q h < 1)


/-- `sideOk`, plus the point case: `h = 0` and `ζ₀` real (field point on the support line). -/
def sideOk2 (z0 e : CQ) (h : ℚ) : Bool :=
  sideOk z0 e h || (decide (z0.im = 0) && decide (h = 0))

theorem sideOk2_sound {z0 e : CQ} {h : ℚ} (hs : sideOk2 z0 e h = true) (s : ℝ) (hs' : |s| ≤ h) :
    0 < (z0.im : ℝ) * (z0.toC + e.toC * (s : ℂ)).im ∨
      ((z0.im : ℝ) = 0 ∧ (z0.toC + e.toC * (s : ℂ)).im = 0) := by
  simp only [sideOk2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
  rcases hs with hs | ⟨h0, hh⟩
  · exact sideOk_sound hs s hs'
  · right
    have hs0 : s = 0 := by
      have : |s| ≤ 0 := by simpa [hh] using hs'
      exact abs_nonpos_iff.1 this
    have h0' : (z0.im : ℝ) = 0 := by exact_mod_cast h0
    refine ⟨h0', ?_⟩
    simp [hs0, CQ.toC, h0']

/-- `sideOk2`, or `Re ζ₀ < 0` (then `Re (-ζ₀) > 0` and `Re (1 - ζ₀) > 0`: the principal logarithm of
the product splits for every `b` with `Re b > 0`, whatever the sign of `Im ζ`). -/
def sideOk3 (z0 e : CQ) (h : ℚ) : Bool :=
  sideOk2 z0 e h || decide (z0.re < 0)

theorem sideOk3_sound {z0 e : CQ} {h : ℚ} (hs : sideOk3 z0 e h = true) (s : ℝ) (hs' : |s| ≤ h) :
    (0 < (z0.im : ℝ) * (z0.toC + e.toC * (s : ℂ)).im ∨
      ((z0.im : ℝ) = 0 ∧ (z0.toC + e.toC * (s : ℂ)).im = 0)) ∨ z0.re < 0 := by
  simp only [sideOk3, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
  rcases hs with hs | hs
  · exact Or.inl (sideOk2_sound hs s hs')
  · exact Or.inr hs

end CatalanCore.Uniform.Decay.NearCells
