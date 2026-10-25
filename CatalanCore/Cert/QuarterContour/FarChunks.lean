module
public import CatalanCore.Cert.QuarterContour.FastMacros
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.FarChunks
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

def zeroFD : FD := (0,0,0,0,0,0)

lemma fdAdd_assoc (a b c : FD) :
    SigmaP6.fdAdd (SigmaP6.fdAdd a b) c = SigmaP6.fdAdd a (SigmaP6.fdAdd b c) := by
  simp only [SigmaP6.fdAdd,add_assoc]

lemma fdZero_add (a : FD) : SigmaP6.fdAdd zeroFD a = a := by
  simp only [SigmaP6.fdAdd,zeroFD,_root_.zero_add]

lemma farSum_append (x0 y0 : ℤ) (ps qs : List Pt) :
    FastMacros.farSum x0 y0 (ps++qs) =
      SigmaP6.fdAdd (FastMacros.farSum x0 y0 ps) (FastMacros.farSum x0 y0 qs) := by
  induction ps with
  | nil => simp only [List.nil_append,FastMacros.farSum,SigmaP6.fdAdd,_root_.zero_add]
  | cons p ps ih =>
    simp only [List.cons_append,FastMacros.farSum,ih,fdAdd_assoc]

def foldFD : List FD → FD
  | [] => zeroFD
  | x::xs => SigmaP6.fdAdd x (foldFD xs)

lemma farSum_flatten_of_forall₂ (x0 y0 : ℤ) {parts : List (List Pt)} {fds : List FD}
    (h : List.Forall₂ (fun ps fd => FastMacros.farSum x0 y0 ps = fd) parts fds) :
    FastMacros.farSum x0 y0 parts.flatten = foldFD fds := by
  induction h with
  | nil => rfl
  | cons h₁ h₂ ih => simp only [List.flatten_cons,farSum_append,foldFD,h₁,ih]

lemma farOK_of_chunks (pts : List Pt) (m : Macro) (parts : List (List Pt)) (fds : List FD)
    (hparts : parts.flatten = macroFar pts m)
    (hrows : List.Forall₂ (fun ps fd => FastMacros.farSum m.x0 m.y0 ps = fd) parts fds)
    (htotal : foldFD fds = m.fd) : SigmaQuarter.farOK pts m := by
  unfold SigmaQuarter.farOK
  rw [←FastMacros.farSum_eq,←hparts]
  exact (farSum_flatten_of_forall₂ m.x0 m.y0 hrows).trans htotal
end CatalanCore.Cert.QuarterContour.FarChunks
#print axioms CatalanCore.Cert.QuarterContour.FarChunks.farSum_append
#print axioms CatalanCore.Cert.QuarterContour.FarChunks.farOK_of_chunks
