module

public import CatalanCore.Cert.SigmaThirds.LogBits
public import CatalanCore.Cert.SigmaThirds.IBoundDef

@[expose] public section

/-!
# Checked energy exponents with position-masked byte tapes

Byte i encodes (L+i)%256. Decoding and bounds are checked independently of the
encoder: successful evaluation still equals the original energy row. The mask
avoids long identical low-byte patterns when consecutive exponents are equal.
-/
namespace CatalanCore.Cert.SigmaThirds

open CatalanCore.Cert.SigmaHybS

/-- Decode one position-masked exponent byte. -/
def maskedEnergyExponent (tape position : ℕ) : ℕ :=
  (tape % 256 + 256 - position % 256) % 256

/-- Structural energy sum with checked, position-masked exponent bytes. -/
def iRowPackedBitsMasked (p : Pt) (qs : List Pt) (tape position : ℕ) : ℤ × Bool :=
  match qs with
  | [] => (0, decide (tape = 0))
  | q :: rest =>
      let exponent := maskedEnergyExponent tape position
      let N := qII p q
      let tail := iRowPackedBitsMasked p rest (tape >>> 8) (position + 1)
      ((q.2.2 : ℤ) * logLoBits N exponent + tail.1,
        logBitsOK N exponent && tail.2)
termination_by structural qs

/-- Every decoded exponent is checked, so the mask cannot change a successful sum. -/
theorem iRowPackedBitsMasked_eq (p : Pt) : ∀ qs tape position,
    (iRowPackedBitsMasked p qs tape position).2 = true →
      (iRowPackedBitsMasked p qs tape position).1 = iRow p qs := by
  intro qs
  induction qs with
  | nil =>
      intro tape position _
      rfl
  | cons q qs ih =>
      intro tape position h
      have hs : logBitsOK (qII p q) (maskedEnergyExponent tape position) = true ∧
          (iRowPackedBitsMasked p qs (tape >>> 8) (position + 1)).2 = true := by
        simpa only [iRowPackedBitsMasked, Bool.and_eq_true] using h
      simp only [iRowPackedBitsMasked, iRow]
      rw [logLoBits_eq hs.1, ih (tape >>> 8) (position + 1) hs.2]

/-- The diagonal consumes byte0; the remaining row starts at byte position1. -/
def rowTPackedBitsMasked (L : List Pt) (r tape : ℕ) : ℤ × Bool :=
  let p := L.getD r (0, 0, 0)
  let exponent := maskedEnergyExponent tape 0
  let tail := iRowPackedBitsMasked p (L.drop (r + 1)) (tape >>> 8) 1
  ((p.2.2 : ℤ) * ((p.2.2 : ℤ) * logLoBits (qII p p) exponent + 2 * tail.1),
    logBitsOK (qII p p) exponent && tail.2)

/-- Successful masked evaluation equals the old triangular energy row exactly. -/
theorem rowTPackedBitsMasked_eq (L : List Pt) (r tape : ℕ)
    (h : (rowTPackedBitsMasked L r tape).2 = true) :
    (rowTPackedBitsMasked L r tape).1 = rowT L r := by
  have hs : logBitsOK (qII (L.getD r (0, 0, 0)) (L.getD r (0, 0, 0)))
        (maskedEnergyExponent tape 0) = true ∧
      (iRowPackedBitsMasked (L.getD r (0, 0, 0)) (L.drop (r + 1)) (tape >>> 8) 1).2 = true := by
    simpa only [rowTPackedBitsMasked, Bool.and_eq_true] using h
  simp only [rowTPackedBitsMasked, rowT]
  rw [logLoBits_eq hs.1, iRowPackedBitsMasked_eq _ _ _ _ hs.2]

/-- Transfer one literal masked kernel check to the unchanged public row statement. -/
theorem rowT_of_packedBitsMasked_check (L : List Pt) (r tape : ℕ) (v : ℤ)
    (h : rowTPackedBitsMasked L r tape = (v, true)) : rowT L r = v := by
  have hok : (rowTPackedBitsMasked L r tape).2 = true := congrArg Prod.snd h
  have hv : (rowTPackedBitsMasked L r tape).1 = v := congrArg Prod.fst h
  exact (rowTPackedBitsMasked_eq L r tape hok).symm.trans hv

end CatalanCore.Cert.SigmaThirds

#print axioms CatalanCore.Cert.SigmaThirds.iRowPackedBitsMasked_eq
#print axioms CatalanCore.Cert.SigmaThirds.rowT_of_packedBitsMasked_check