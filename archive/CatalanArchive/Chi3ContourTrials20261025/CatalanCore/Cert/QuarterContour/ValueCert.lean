module
public import CatalanCore.Cert.QuarterContour.TableLog
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ValueCert
open CatalanCore.Cert.SigmaP6 CatalanLambda.Cert
structure Entry where
  n : ℕ
  l : ℕ
  m : ℕ
  c : ℕ
  t : ℕ

def value (a : Entry) : ℤ :=
  ((a.l : ℤ)-80) * (if 80 ≤ a.l then (TableLog.tabLoD 256 : ℤ) else (TableLog.tabUpD 256 : ℤ))
    + (a.t : ℤ) + 2^64 - (a.c : ℤ)

def valid (N : ℕ) (a : Entry) : Bool :=
  decide (N = a.n) && TableLog.exponentOK a.n a.l &&
  decide (a.n * 2^8 / 2^a.l = a.m) &&
  decide (((a.m+1)*2^(a.l+56)+a.n-1)/a.n = a.c) &&
  decide (TableLog.tabLoD (a.m-256+1) = a.t)

lemma valid_sound {N : ℕ} {a : Entry} (h : valid N a = true) : logLoS N = value a := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hn, he⟩, hm⟩, hc⟩, ht⟩ := h
  rw [hn, ← TableLog.lo_eq he]
  simp only [TableLog.lo, hm, hc, ht, value]

def row (p : Pt) : List Pt → List Entry → Option ℤ
  | [], [] => some 0
  | q::qs, a::cs =>
      if valid (qII p q) a then
        match row p qs cs with
        | some v => some ((q.2.2 : ℤ)*value a+v)
        | none => none
      else none
  | _, _ => none

lemma row_sound (p : Pt) : ∀ qs cs v, row p qs cs = some v → iRow p qs = v := by
  intro qs
  induction qs with
  | nil => intro cs v h; cases cs <;> simp_all [row, iRow]
  | cons q qs ih =>
    intro cs v h
    cases cs with
    | nil => simp [row] at h
    | cons a cs =>
      simp only [row] at h
      split at h
      next he =>
        cases ht : row p qs cs with
        | none => simp [ht] at h
        | some w =>
          simp only [ht, Option.some.injEq] at h
          rw [iRow, ih cs w ht, valid_sound he]
          exact h
      next => simp at h
end CatalanCore.Cert.QuarterContour.ValueCert
#print axioms CatalanCore.Cert.QuarterContour.ValueCert.row_sound