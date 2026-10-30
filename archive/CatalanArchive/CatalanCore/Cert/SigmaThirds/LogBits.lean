module

public import CatalanCore.Cert.SigmaThirds.MacroCache

@[expose] public section

/-!
# Exact logarithm evaluation with checked binary exponents

The supplied exponent is checked by two natural-number inequalities. This replaces
only the computation of `Nat.log2`; every subsequent integer operation is unchanged.
-/

namespace CatalanCore.Cert.SigmaThirds

open CatalanCore.Cert.SigmaHybS
open CatalanLambda.Cert

/-- Exact binary-exponent certificate for a positive natural number. -/
def logBitsOK (N L : ℕ) : Bool := decide (2 ^ L ≤ N ∧ N < 2 ^ (L + 1))

/-- The original upper-log formula with an explicitly supplied exponent. -/
def logUpBits (N L : ℕ) : ℤ :=
  let m := (N <<< 8) >>> L
  let e : ℤ := ((L : ℤ) - 80) * (if 80 ≤ L then (tabUp 256 : ℤ) else (tabLo 256 : ℤ))
  let R : ℤ := (((N <<< 72) + (m <<< L) - 1) / (m <<< L) : ℕ)
  e + (tabUp (m - 256) : ℤ) + R - 2 ^ 64

/-- The original lower-log formula with an explicitly supplied exponent. -/
def logLoBits (N L : ℕ) : ℤ :=
  let m := (N <<< 8) >>> L
  let e : ℤ := ((L : ℤ) - 80) * (if 80 ≤ L then (tabLo 256 : ℤ) else (tabUp 256 : ℤ))
  let c : ℤ := ((((m + 1) <<< (L + 56)) + N - 1) / N : ℕ)
  e + (tabLo (m - 256 + 1) : ℤ) + 2 ^ 64 - c

theorem log2_eq_of_bits {N L : ℕ} (h : logBitsOK N L = true) : N.log2 = L := by
  have hb : 2 ^ L ≤ N ∧ N < 2 ^ (L + 1) := by
    simpa only [logBitsOK, decide_eq_true_eq] using h
  have hp : 0 < N := lt_of_lt_of_le (by positivity : 0 < 2 ^ L) hb.1
  exact (Nat.log2_eq_iff hp.ne').mpr hb

theorem logUpBits_eq {N L : ℕ} (h : logBitsOK N L = true) : logUpBits N L = logUpS N := by
  simp only [logUpBits, logUpS, log2_eq_of_bits h]

theorem logLoBits_eq {N L : ℕ} (h : logBitsOK N L = true) : logLoBits N L = logLoS N := by
  simp only [logLoBits, logLoS, log2_eq_of_bits h]

/-- Near-point weighted sum and all exponent checks in one structural pass. -/
def sigSumBits (xlo xhi ylo yhi : ℤ) (ps : List Pt) (ls : List ℕ) : ℤ × Bool :=
  match ps with
  | [] =>
      match ls with
      | [] => (0, true)
      | _ :: _ => (0, false)
  | p :: ps' =>
      match ls with
      | [] => (0, false)
      | L :: ls' =>
          let N := qplusN xlo xhi ylo yhi p
          let rest := sigSumBits xlo xhi ylo yhi ps' ls'
          ((p.2.2 : ℤ) * logUpBits N L + rest.1, logBitsOK N L && rest.2)
termination_by structural ps

theorem sigSumBits_eq (xlo xhi ylo yhi : ℤ) : ∀ ps ls,
    (sigSumBits xlo xhi ylo yhi ps ls).2 = true →
      (sigSumBits xlo xhi ylo yhi ps ls).1 = sigSum xlo xhi ylo yhi ps := by
  intro ps
  induction ps with
  | nil =>
      intro ls h
      cases ls with
      | nil => rfl
      | cons L ls => simp only [sigSumBits, Bool.false_eq_true] at h
  | cons p ps ih =>
      intro ls h
      cases ls with
      | nil => simp only [sigSumBits, Bool.false_eq_true] at h
      | cons L ls =>
          have hs : logBitsOK (qplusN xlo xhi ylo yhi p) L = true ∧
              (sigSumBits xlo xhi ylo yhi ps ls).2 = true := by
            simpa only [sigSumBits, Bool.and_eq_true] using h
          simp only [sigSumBits, sigSum]
          rw [logUpBits_eq hs.1, ih ls hs.2]

theorem sigSum_of_bits_check (xlo xhi ylo yhi : ℤ) (ps : List Pt) (ls : List ℕ) (v : ℤ)
    (h : sigSumBits xlo xhi ylo yhi ps ls = (v, true)) :
    sigSum xlo xhi ylo yhi ps = v := by
  have hok : (sigSumBits xlo xhi ylo yhi ps ls).2 = true := congrArg Prod.snd h
  have hv : (sigSumBits xlo xhi ylo yhi ps ls).1 = v := congrArg Prod.fst h
  exact (sigSumBits_eq xlo xhi ylo yhi ps ls hok).symm.trans hv

/-- Ray-cell checker after an independently verified near sum has been supplied. -/
def cachedRayNearOK (mp : ℚ) (M P j c : ℕ) (fd : FD) (ns : ℤ) : Bool :=
  let b := j * (4 + 4 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let a := b + 4 + 4 * c
  let xlo := slot P a
  let xhi := slot P (a + 1)
  let ylo := slot P (a + 2)
  let yhi := slot P (a + 3)
  decide (xhi < 0 ∧ xlo ≤ xhi ∧ 0 ≤ ylo) &&
    decide (mp ≤ boxLBH (sigTL x0 y0 fd xlo xhi ylo yhi ns) xlo xhi ylo yhi)

theorem cachedRayCellOK_eq_near (L : List Pt) (mp : ℚ) (M P j c : ℕ) (fd : FD) (ns : ℤ)
    (hns : sigSum (slot P (j * (4 + 4 * M) + 4 + 4 * c))
      (slot P (j * (4 + 4 * M) + 4 + 4 * c + 1))
      (slot P (j * (4 + 4 * M) + 4 + 4 * c + 2))
      (slot P (j * (4 + 4 * M) + 4 + 4 * c + 3))
      ((L.drop (slot P (j * (4 + 4 * M) + 2)).toNat).take
        ((slot P (j * (4 + 4 * M) + 3)).toNat - (slot P (j * (4 + 4 * M) + 2)).toNat)) = ns) :
    cachedRayCellOK L mp M P j c fd = cachedRayNearOK mp M P j c fd ns := by
  simp only [cachedRayCellOK, cachedRayNearOK, hns]

end CatalanCore.Cert.SigmaThirds

#print axioms CatalanCore.Cert.SigmaThirds.logUpBits_eq
#print axioms CatalanCore.Cert.SigmaThirds.sigSum_of_bits_check
#print axioms CatalanCore.Cert.SigmaThirds.cachedRayCellOK_eq_near