module

public import CatalanCore.Uniform.Decay.PilotArithmetic

@[expose] public section
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.SeriesStop
open CatalanCore.Uniform.Decay.SignedPilot

def fullLoop (S : Nat) (alt : Bool) (a2 b2 : Nat) : Nat → Nat → Nat → Nat → Int → Int
  | 0, _, _, _, acc => acc
  | n+1, p, q, k, acc =>
    let t : Nat := S * p / (q * (2*k+1))
    fullLoop S alt a2 b2 n (p*a2) (q*b2) (k+1)
      (acc + if alt && k % 2 == 1 then -(t : Int) else (t : Int))

def stoppedLoop (S : Nat) (alt : Bool) (a2 b2 : Nat) : Nat → Nat → Nat → Nat → Int → Int
  | 0, _, _, _, acc => acc
  | n+1, p, q, k, acc =>
    let t : Nat := S * p / (q * (2*k+1))
    if t = 0 then acc else
      stoppedLoop S alt a2 b2 n (p*a2) (q*b2) (k+1)
        (acc + if alt && k % 2 == 1 then -(t : Int) else (t : Int))

/-- Once a floored term vanishes, the next one vanishes. Includes zero denominators. -/
theorem zero_step (S a2 b2 p q k : Nat) (hab : a2 ≤ b2)
    (ht : S*p / (q*(2*k+1)) = 0) :
    S*(p*a2) / ((q*b2)*(2*(k+1)+1)) = 0 := by
  by_cases hq : q = 0
  · simp [hq]
  by_cases hb : b2 = 0
  · simp [hb]
  have hqp : 0 < q := Nat.pos_of_ne_zero hq
  have hbp : 0 < b2 := Nat.pos_of_ne_zero hb
  have hden : 0 < q*(2*k+1) := Nat.mul_pos hqp (by omega)
  have hz := Nat.lt_of_div_eq_zero hden ht
  apply Nat.div_eq_of_lt
  calc
    S*(p*a2) = (S*p)*a2 := (Nat.mul_assoc S p a2).symm
    _ ≤ (S*p)*b2 := Nat.mul_le_mul_left _ hab
    _ < (q*(2*k+1))*b2 := Nat.mul_lt_mul_of_pos_right hz hbp
    _ = (q*b2)*(2*k+1) := by
      rw [Nat.mul_assoc, Nat.mul_comm (2*k+1) b2, ← Nat.mul_assoc]
    _ ≤ (q*b2)*(2*(k+1)+1) := Nat.mul_le_mul_left _ (by omega)

theorem zero_tail (S : Nat) (alt : Bool) (a2 b2 : Nat) (hab : a2 ≤ b2)
    (n p q k : Nat) (acc : Int)
    (ht : S*p / (q*(2*k+1)) = 0) :
    fullLoop S alt a2 b2 n p q k acc = acc := by
  induction n generalizing p q k acc with
  | zero => rfl
  | succ n ih =>
    have hn := zero_step S a2 b2 p q k hab ht
    simpa [fullLoop, ht] using ih (p*a2) (q*b2) (k+1) acc hn

/-- Exact loop equality, with no positivity or domain assumptions beyond monotonicity. -/
theorem stoppedLoop_eq (S : Nat) (alt : Bool) (a2 b2 : Nat) (hab : a2 ≤ b2)
    (n p q k : Nat) (acc : Int) :
    stoppedLoop S alt a2 b2 n p q k acc = fullLoop S alt a2 b2 n p q k acc := by
  induction n generalizing p q k acc with
  | zero => rfl
  | succ n ih =>
    by_cases ht : S*p / (q*(2*k+1)) = 0
    · rw [stoppedLoop, if_pos ht]
      exact (zero_tail S alt a2 b2 hab (n+1) p q k acc ht).symm
    · simpa only [stoppedLoop, ht, if_false, fullLoop] using
        ih (p*a2) (q*b2) (k+1)
          (acc + if alt && k % 2 == 1 then
            -((S*p / (q*(2*k+1)) : Nat) : Int)
            else ((S*p / (q*(2*k+1)) : Nat) : Int))

theorem fullLoop_scale_eq (alt : Bool) (a2 b2 n p q k : Nat) (acc : Int) :
    fullLoop scale alt a2 b2 n p q k acc = SignedPilot.seriesLoop alt a2 b2 n p q k acc := by
  induction n generalizing p q k acc with
  | zero => rfl
  | succ n ih =>
    simpa only [fullLoop, SignedPilot.seriesLoop] using
      ih (p*a2) (q*b2) (k+1)
        (acc + if alt && k % 2 == 1 then
          -((scale*p / (q*(2*k+1)) : Nat) : Int)
          else ((scale*p / (q*(2*k+1)) : Nat) : Int))

def seriesLoopStop (alt : Bool) (a2 b2 : Nat) : Nat → Nat → Nat → Nat → Int → Int :=
  stoppedLoop scale alt a2 b2

theorem seriesLoopStop_eq (alt : Bool) (a2 b2 : Nat) (hab : a2 ≤ b2)
    (n p q k : Nat) (acc : Int) :
    seriesLoopStop alt a2 b2 n p q k acc = SignedPilot.seriesLoop alt a2 b2 n p q k acc :=
  (stoppedLoop_eq scale alt a2 b2 hab n p q k acc).trans
    (fullLoop_scale_eq alt a2 b2 n p q k acc)

def seriesStop (alt : Bool) (a b : Nat) : Int :=
  if a ≤ b then seriesLoopStop alt (a*a) (b*b) 64 a b 0 0
  else SignedPilot.series alt a b

/-- Universal exact replacement; invalid/unmonotone caller inputs retain the old path. -/
theorem seriesStop_eq (alt : Bool) (a b : Nat) :
    seriesStop alt a b = SignedPilot.series alt a b := by
  by_cases hab : a ≤ b
  · simp only [seriesStop, if_pos hab, SignedPilot.series]
    exact seriesLoopStop_eq alt (a*a) (b*b) (Nat.mul_le_mul hab hab) 64 a b 0 0
  · simp only [seriesStop, if_neg hab]

end CatalanCore.Uniform.Decay.SeriesStop

#print axioms CatalanCore.Uniform.Decay.SeriesStop.seriesStop_eq
