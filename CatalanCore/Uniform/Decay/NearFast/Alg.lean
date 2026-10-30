module

public import CatalanCore.Uniform.Decay.NearCells2.Mix

@[expose] public section
set_option Elab.async false

/-!
# Gaussian-integer evaluation of the segment model (lane D, package D12)

Exact, gcd-free evaluation of the order-`n` coefficient model of `NearCells.pieceCoef`:
`z₀ = Z/D`, `e = E/D` with Gaussian integers `Z, E`, every coefficient is a Gaussian integer over a
known denominator, and only the outputs are rounded down to the grid `1/GG`.
-/

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

/-- Output grid `10^36 + 39` (odd). -/
def GG : ℤ := 1000000000000000000000000000000000039

structure GZ where
  re : ℤ
  im : ℤ

namespace GZ
def mul (a b : GZ) : GZ := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def add (a b : GZ) : GZ := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : GZ) : GZ := ⟨a.re - b.re, a.im - b.im⟩
def smul (c : ℤ) (a : GZ) : GZ := ⟨c * a.re, c * a.im⟩
def conj (a : GZ) : GZ := ⟨a.re, -a.im⟩
def nsq (a : GZ) : ℤ := a.re * a.re + a.im * a.im
def zero : GZ := ⟨0, 0⟩
def one : GZ := ⟨1, 0⟩
def toC (g : GZ) : ℂ := ⟨(g.re : ℝ), (g.im : ℝ)⟩
end GZ

/-- Powers table `[cur, cur z, cur z², …]` (length `N`). -/
def ptabAux (z : GZ) : GZ → ℕ → List GZ
  | _, 0 => []
  | cur, k + 1 => cur :: ptabAux z (cur.mul z) k
def gtab (z : GZ) (N : ℕ) : List GZ := ptabAux z GZ.one N
def gget (l : List GZ) (i : ℕ) : GZ := l.getD i GZ.zero

def itabAux (D : ℤ) : ℤ → ℕ → List ℤ
  | _, 0 => []
  | cur, k + 1 => cur :: itabAux D (cur * D) k
def itab (D : ℤ) (N : ℕ) : List ℤ := itabAux D 1 N
def iget (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def sumG (f : ℕ → GZ) : ℕ → GZ
  | 0 => GZ.zero
  | n + 1 => (sumG f n).add (f n)
def sumI (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumI f n + f n

/-- Product of the denominators of `a 0, …, a (N-1)`. -/
def prodDen (a : ℕ → ℚ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => prodDen a k * (a k).den

/-- Numerator of `q` over the common denominator `D` (`q.den ∣ D`). -/
def sc (q : ℚ) (D : ℕ) : ℤ := q.num * ((D / q.den : ℕ) : ℤ)

/-- Floor division onto the grid. -/
def fl (x : ℤ) (den : ℤ) : ℤ := (x * GG) / den

/-! ### Data of one piece -/

def fD (z0 e : CQ) : ℕ := Nat.lcm (Nat.lcm z0.re.den z0.im.den) (Nat.lcm e.re.den e.im.den)
def fZ (z0 e : CQ) : GZ := ⟨sc z0.re (fD z0 e), sc z0.im (fD z0 e)⟩
def fE (z0 e : CQ) : GZ := ⟨sc e.re (fD z0 e), sc e.im (fD z0 e)⟩
def fDw (a : ℕ → ℚ) (d : ℕ) : ℕ := prodDen (wq a) (d + 1)
def fwI (a : ℕ → ℚ) (d k : ℕ) : ℤ := sc (wq a k) (fDw a d)

/-- `PB_m` numerator over `Dw D^{d+1}`, from the tables `Dp` (powers of `D`), `Zp`, `Ep`. -/
def fPBm (a : ℕ → ℚ) (d : ℕ) (Dp : List ℤ) (Zp Ep : List GZ) (m : ℕ) : GZ :=
  (gget Ep m).mul (sumG (fun k => (gget Zp (k + 1 - m)).smul
    (fwI a d k * (chooseFast (k + 1) m : ℤ) * iget Dp (d - k))) (d + 1))

def fPB (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) : List GZ :=
  let Dp := itab (fD z0 e : ℤ) (d + 2)
  let Zp := gtab (fZ z0 e) (d + 2)
  let Ep := gtab (fE z0 e) n
  (List.range n).map (fPBm a d Dp Zp Ep)

def fmassI (a : ℕ → ℚ) (d : ℕ) (Dp : List ℤ) : ℤ := sumI (fwI a d) (d + 1) * iget Dp (d + 1)

/-- Numerators of `PA_m` over `Dw D^{d+1}`. -/
def fPA (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) : List GZ :=
  let Dp := itab (fD z0 e : ℤ) (d + 2)
  (List.range n).map fun m =>
    (GZ.zero.sub (gget (fPB n a d z0 e) m)).add ⟨if m = 0 then fmassI a d Dp else 0, 0⟩

def frI (a : ℕ → ℚ) (d j : ℕ) : ℤ :=
  sumI (fun k => if j ≤ k then fwI a d k * (((d + 1).factorial / (k - j + 1) : ℕ) : ℤ) else 0) (d + 1)

/-- `-R_m` numerator over `Dw (d+1)! D^d`. -/
def fRRm (d : ℕ) (rIt : List ℤ) (Dp : List ℤ) (Zp Ep : List GZ) (m : ℕ) : GZ :=
  (gget Ep m).mul (sumG (fun j => (gget Zp (j - m)).smul
    (iget rIt j * (chooseFast j m : ℤ) * iget Dp (d - j))) (d + 1))

def fRR (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) : List GZ :=
  let Dp := itab (fD z0 e : ℤ) (d + 2)
  let Zp := gtab (fZ z0 e) (d + 2)
  let Ep := gtab (fE z0 e) n
  let rIt := (List.range (d + 1)).map (frI a d)
  (List.range n).map (fRRm d rIt Dp Zp Ep)

def jetRe (n : ℕ) (PIQ QNp : List GZ) (m : ℕ) : ℤ :=
  sumI (fun j => (((n - 1).factorial / (m - j) : ℕ) : ℤ) *
    ((gget PIQ j).mul (gget QNp (m - j))).re) m

/-- `q₁ = E conj(D - Z) / nsq(D - Z)`. -/
def fDZ (z0 e : CQ) : GZ := GZ.sub ⟨(fD z0 e : ℤ), 0⟩ (fZ z0 e)
def fQN1 (z0 e : CQ) : GZ := (fE z0 e).mul (fDZ z0 e).conj
def fQD1 (z0 e : CQ) : ℤ := (fDZ z0 e).nsq
/-- `q₀ = -E conj Z / nsq Z`. -/
def fQN0 (z0 e : CQ) : GZ := GZ.zero.sub ((fE z0 e).mul (fZ z0 e).conj)
def fQD0 (z0 e : CQ) : ℤ := (fZ z0 e).nsq

/-- One rounded coefficient `⌊GG c_m⌋` (six floors), from the shared tables. -/
def fCm (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (lv : ℚ) (DP : ℤ) (Dp : List ℤ) (DL0 DL1 : ℕ)
    (L0g L1g : GZ) (PA PB RR QN1p QN0p : List GZ) (QD1p QD0p : List ℤ) (PAQ PBQ : List GZ)
    (m : ℕ) : ℤ :=
  fl ((gget PA m).mul L1g).re (DP * DL1) + fl ((gget PB m).mul L0g).re (DP * DL0)
    - fl (gget RR m).re ((fDw a d : ℤ) * ((d + 1).factorial : ℤ) * iget Dp d)
    - fl (jetRe n PAQ QN1p m) (DP * ((n - 1).factorial : ℤ) * iget QD1p m)
    - fl (jetRe n PBQ QN0p m) (DP * ((n - 1).factorial : ℤ) * iget QD0p m)
    + (if m = 0 then ⌊massQ a d * lv * (GG : ℚ)⌋ else 0)

/-- Common denominator of the parts of `w`. -/
def fDL (w : CQ) : ℕ := Nat.lcm w.re.den w.im.den

/-- Gaussian integer numerator of `w` over `fDL w`. -/
def fG (w : CQ) : GZ := ⟨sc w.re (fDL w), sc w.im (fDL w)⟩

/-- The rounded coefficients. -/
def fC (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (z0 e L0 L1 : CQ) (lv : ℚ) : List ℤ :=
  let Dp := itab (fD z0 e : ℤ) (d + 2)
  let DP : ℤ := (fDw a d : ℤ) * iget Dp (d + 1)
  let PB := fPB n a d z0 e
  let PA := fPA n a d z0 e
  let QD1p := itab (fQD1 z0 e) n
  let QD0p := itab (fQD0 z0 e) n
  let PAQ := (List.range n).map fun j => (gget PA j).smul (iget QD1p j)
  let PBQ := (List.range n).map fun j => (gget PB j).smul (iget QD0p j)
  (List.range n).map (fCm n a d lv DP Dp (fDL L0) (fDL L1)
    (fG L0) (fG L1) PA PB (fRR n a d z0 e) (gtab (fQN1 z0 e) n) (gtab (fQN0 z0 e) n)
    QD1p QD0p PAQ PBQ)

end CatalanCore.Uniform.Decay.NearFast
