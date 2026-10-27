import CatalanCore.Uniform.Decay.PilotArithmetic
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
namespace CatalanCore.Uniform.Decay.Optimization.Moments
abbrev Z := Int × Int
def za (a b : Z) : Z := (a.1+b.1,a.2+b.2)
def zm (a b : Z) : Z := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
def zsc (a : Int) (z : Z) : Z := (a*z.1,a*z.2)
def zp (a : Z) : Nat → Z
  | 0 => (1,0)
  | n+1 => zm a (zp a n)
def zTape : List Int → List Z
  | a::b::xs => (a,b)::zTape xs
  | _ => []
def linearAux (a v previous : Z) : List Z → List Z
  | [] => [zm v previous]
  | x::xs => za (zm a x) (zm v previous)::linearAux a v x xs
def linearPower (a v : Z) : Nat → List Z
  | 0 => [(1,0)]
  | n+1 => linearAux a v (0,0) (linearPower a v n)
def dotWeights (p : List Z) (ws : List Int) : Z :=
  match p,ws with
  | [],_ => (0,0)
  | _,[] => (0,0)
  | x::xs,w::ws => za (zsc w x) (dotWeights xs ws)
termination_by structural p
def integralWeights (L : Nat) (cs : List Int) : List Int :=
  (List.range 13).map (fun j => cs.zipIdx.foldl (fun acc x => acc+x.1*(L/(j+x.2+1) : Nat)) 0)
def rawMoment (a v : Z) (ws : List Int) (k : Nat) : Z := dotWeights (linearPower a v k) ws
def adjacent : List Nat → List Nat
  | a::b::xs => (a+b)::adjacent (b::xs)
  | _ => []
def chooseRow : Nat → List Nat
  | 0 => [1]
  | n+1 => 1::(adjacent (chooseRow n) ++ [1])
def centeredMoment (c : Z) (k : Nat) (raw : List Z) : Z :=
  (raw.take (k+1)).zipIdx.foldl (fun acc x =>
    za acc (zsc ((chooseRow k).getD x.2 0 : Int) (zm (zp (-c.1,-c.2) (k-x.2)) x.1))) (0,0)
end CatalanCore.Uniform.Decay.Optimization.Moments
