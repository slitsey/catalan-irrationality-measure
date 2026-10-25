module
public import CatalanCore.Cert.QuarterContour.TableLog
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.BinaryLog
/-- Bounded binary search in exponent space; no linear recursion through the bits of N. -/
def search (N a : ℕ) : ℕ → ℕ
  | 0 => a
  | k+1 => if N < 2^(a+2^k) then search N a k else search N (a+2^k) k

lemma search_bounds (k : ℕ) : ∀ N a, 2^a ≤ N → N < 2^(a+2^k) →
    2^(search N a k) ≤ N ∧ N < 2^(search N a k+1) := by
  induction k with
  | zero => intro N a hl hu; simpa only [search, pow_zero] using And.intro hl hu
  | succ k ih =>
    intro N a hl hu
    simp only [search]
    split
    next h => exact ih N a hl h
    next h =>
      have he : a+2^(k+1) = (a+2^k)+2^k := by rw [pow_succ]; omega
      exact ih N (a+2^k) (by omega) (by rwa [← he])

def eval (N : ℕ) : ℕ :=
  if N = 0 then 0 else if N < 2^128 then search N 0 7 else N.log2
lemma eval_eq (N : ℕ) : eval N = N.log2 := by
  unfold eval
  split
  next h => subst N; rfl
  next hn =>
    split
    next h =>
      have hb := search_bounds 7 N 0 (by simpa using Nat.one_le_iff_ne_zero.mpr hn)
        (by simpa using h)
      exact ((Nat.log2_eq_iff hn).mpr hb).symm
    next => rfl

def lo (N : ℕ) : ℤ := TableLog.lo N (eval N)
lemma lo_eq (N : ℕ) : lo N = CatalanLambda.Cert.logLoS N := by
  simp only [lo, TableLog.lo, eval_eq, CatalanLambda.Cert.logLoS,
    TableLog.tabLoD, TableLog.tabUpD, FastTables.lo_eq, FastTables.up_eq,
    CatalanLambda.Cert.tabLo, CatalanLambda.Cert.tabUp,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
open CatalanCore.Cert.SigmaP6
def row (p : Pt) : List Pt → ℤ
  | [] => 0
  | q::qs => (q.2.2 : ℤ)*lo (qII p q)+row p qs
lemma row_eq (p : Pt) (qs : List Pt) : row p qs = iRow p qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [row, iRow, lo_eq, ih]
end CatalanCore.Cert.QuarterContour.BinaryLog
#print axioms CatalanCore.Cert.QuarterContour.BinaryLog.row_eq