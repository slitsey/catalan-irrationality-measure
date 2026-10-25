module
public import CatalanCore.Cert.QuarterContour.Energy
public import CatalanCore.Cert.QuarterContour.FastTables
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.TableLog
open CatalanLambda.Cert CatalanCore.Cert.SigmaP6

def exponentOK (N L : ℕ) : Bool := decide (2^L ≤ N ∧ N < 2^(L+1))
def tabLoD (j : ℕ) : ℕ := FastTables.lo j
def tabUpD (j : ℕ) : ℕ := FastTables.up j

def lo (N L : ℕ) : ℤ :=
  let m := N * 2^8 / 2^L
  let e : ℤ := ((L : ℤ)-80) * (if 80 ≤ L then (tabLoD 256 : ℤ) else (tabUpD 256 : ℤ))
  let c : ℤ := (((m+1)*2^(L+56)+N-1)/N : ℕ)
  e + (tabLoD (m-256+1) : ℤ) + 2^64 - c

def up (N L : ℕ) : ℤ :=
  let m := N * 2^8 / 2^L
  let e : ℤ := ((L : ℤ)-80) * (if 80 ≤ L then (tabUpD 256 : ℤ) else (tabLoD 256 : ℤ))
  let c : ℤ := ((N*2^72+m*2^L-1)/(m*2^L) : ℕ)
  e + (tabUpD (m-256) : ℤ) + c - 2^64

lemma exponent_eq {N L : ℕ} (h : exponentOK N L = true) : N.log2 = L := by
  have hb : 2^L ≤ N ∧ N < 2^(L+1) := by simpa only [exponentOK, decide_eq_true_eq] using h
  exact (Nat.log2_eq_iff (by have : 0 < N := lt_of_lt_of_le (by positivity : 0 < 2^L) hb.1; omega)).mpr hb

lemma lo_eq {N L : ℕ} (h : exponentOK N L = true) : lo N L = logLoS N := by
  simp only [lo, logLoS, exponent_eq h, tabLoD, tabUpD, FastTables.lo_eq, FastTables.up_eq, tabLo, tabUp,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
lemma up_eq {N L : ℕ} (h : exponentOK N L = true) : up N L = logUpS N := by
  simp only [up, logUpS, exponent_eq h, tabLoD, tabUpD, FastTables.lo_eq, FastTables.up_eq, tabLo, tabUp,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

/-- One pass, with checked exponent witnesses and primitive integer operations. -/
def row (p : Pt) : List Pt → List ℕ → Option ℤ
  | [], [] => some 0
  | q::qs, L::ls =>
      if exponentOK (qII p q) L then
        match row p qs ls with
        | some v => some ((q.2.2 : ℤ) * lo (qII p q) L + v)
        | none => none
      else none
  | _, _ => none

lemma row_sound (p : Pt) : ∀ qs ls v, row p qs ls = some v → iRow p qs = v := by
  intro qs
  induction qs with
  | nil => intro ls v h; cases ls <;> simp_all [row, iRow]
  | cons q qs ih =>
    intro ls v h
    cases ls with
    | nil => simp [row] at h
    | cons L ls =>
      simp only [row] at h
      split at h
      next he =>
        cases ht : row p qs ls with
        | none => simp [ht] at h
        | some w =>
          simp only [ht, Option.some.injEq] at h
          rw [iRow, ih ls w ht, ← lo_eq he]
          exact h
      next => simp at h
end CatalanCore.Cert.QuarterContour.TableLog
#print axioms CatalanCore.Cert.QuarterContour.TableLog.row_sound
#print axioms CatalanCore.Cert.QuarterContour.TableLog.up_eq