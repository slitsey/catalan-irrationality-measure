module

public import CatalanCore.Cert.SigmaThirds.LogBits
public import CatalanCore.Cert.SigmaThirds.IBoundDef

@[expose] public section

/-!
# Exact triangular energy evaluation with checked packed binary exponents

The tape stores one exponent per byte, least significant byte first. Every
exponent is checked against the original positive integer argument. The final
Boolean also checks that no unused bytes remain. Only the logarithm's exponent
search is replaced; successful evaluation equals the original energy row.
-/
namespace CatalanCore.Cert.SigmaThirds

open CatalanCore.Cert.SigmaHybS

/-- One structural pass over the remaining points and an exponent-byte tape. -/
def iRowPackedBits (p : Pt) (qs : List Pt) (tape : ℕ) : ℤ × Bool :=
  match qs with
  | [] => (0, decide (tape = 0))
  | q :: rest =>
      let exponent := tape % 256
      let N := qII p q
      let tail := iRowPackedBits p rest (tape >>> 8)
      ((q.2.2 : ℤ) * logLoBits N exponent + tail.1,
        logBitsOK N exponent && tail.2)
termination_by structural qs

/-- The structural packed evaluator equals the original sum whenever its checks pass. -/
theorem iRowPackedBits_eq (p : Pt) : ∀ qs tape,
    (iRowPackedBits p qs tape).2 = true →
      (iRowPackedBits p qs tape).1 = iRow p qs := by
  intro qs
  induction qs with
  | nil =>
      intro tape _
      rfl
  | cons q qs ih =>
      intro tape h
      have hs : logBitsOK (qII p q) (tape % 256) = true ∧
          (iRowPackedBits p qs (tape >>> 8)).2 = true := by
        simpa only [iRowPackedBits, Bool.and_eq_true] using h
      simp only [iRowPackedBits, iRow]
      rw [logLoBits_eq hs.1, ih (tape >>> 8) hs.2]

/-- The first byte certifies the diagonal; subsequent bytes certify the off-diagonal row. -/
def rowTPackedBits (L : List Pt) (r tape : ℕ) : ℤ × Bool :=
  let p := L.getD r (0, 0, 0)
  let exponent := tape % 256
  let tail := iRowPackedBits p (L.drop (r + 1)) (tape >>> 8)
  ((p.2.2 : ℤ) * ((p.2.2 : ℤ) * logLoBits (qII p p) exponent + 2 * tail.1),
    logBitsOK (qII p p) exponent && tail.2)

/-- Successful packed evaluation is exactly the old triangular energy row. -/
theorem rowTPackedBits_eq (L : List Pt) (r tape : ℕ)
    (h : (rowTPackedBits L r tape).2 = true) :
    (rowTPackedBits L r tape).1 = rowT L r := by
  have hs : logBitsOK (qII (L.getD r (0, 0, 0)) (L.getD r (0, 0, 0)))
        (tape % 256) = true ∧
      (iRowPackedBits (L.getD r (0, 0, 0)) (L.drop (r + 1)) (tape >>> 8)).2 = true := by
    simpa only [rowTPackedBits, Bool.and_eq_true] using h
  simp only [rowTPackedBits, rowT]
  rw [logLoBits_eq hs.1, iRowPackedBits_eq _ _ _ hs.2]

/-- Transfer a literal kernel check to the unchanged public row statement. -/
theorem rowT_of_packedBits_check (L : List Pt) (r tape : ℕ) (v : ℤ)
    (h : rowTPackedBits L r tape = (v, true)) : rowT L r = v := by
  have hok : (rowTPackedBits L r tape).2 = true := congrArg Prod.snd h
  have hv : (rowTPackedBits L r tape).1 = v := congrArg Prod.fst h
  exact (rowTPackedBits_eq L r tape hok).symm.trans hv

end CatalanCore.Cert.SigmaThirds

#print axioms CatalanCore.Cert.SigmaThirds.iRowPackedBits_eq
#print axioms CatalanCore.Cert.SigmaThirds.rowT_of_packedBits_check