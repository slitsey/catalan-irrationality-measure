module

public import CatalanCore.Uniform.Content.UFFamily4.PieceDemo0
public import CatalanCore.Uniform.Content.UFFamily4.PieceDemo1
public import CatalanCore.Uniform.Content.UFFamily4.PieceDemo2
public import CatalanCore.Uniform.Content.UFFamily4.PieceDemo3
public import CatalanCore.Uniform.Content.UFFamily4.PieceDemo4
public import CatalanCore.Uniform.Content.UFFamily4.PieceDemo5
public import CatalanCore.Uniform.Content.UFFamily4.PieceDemo6

@[expose] public section

/-!
# Axiom audit for lane H13 (thirds UF coverage and content)
-/

open CatalanCore.Uniform.Content.UFFamily4

#print axioms cover_rho1
#print axioms cover_rho2
#print axioms thirds_cover
#print axioms prime_odd_of_ge
#print axioms thirds_valid
#print axioms thirds_eff
#print axioms ufbound_of_nat
#print axioms thirdsUFContent
#print axioms piece_k3
#print axioms piece_k4
#print axioms piece_k5
#print axioms piece_k6
#print axioms piece_k7
#print axioms piece_k8
#print axioms piece_k9
#print axioms piece_k10
#print axioms piece_k11
#print axioms piece_k12
#print axioms piece_k13
#print axioms piece_k14
#print axioms piece_k15
#print axioms piece_k16
#print axioms piece_k17
#print axioms piece_k18
#print axioms piece_k19
#print axioms piece_k20
#print axioms piece_k21
#print axioms piece_k22
#print axioms piece_k23
#print axioms piece_k24
#print axioms piece_k25
#print axioms piece_k26
#print axioms piece_k27
#print axioms piece_k28
#print axioms piece_k29
#print axioms piece_k30
#print axioms piece_k31
#print axioms piece_k32
#print axioms piece_k33
#print axioms piece_k34
#print axioms piece_k35
#print axioms piece_k36
#print axioms piece_k37
#print axioms piece_k38

/-- Non-vacuity of the band: a point of the band covered by a family. -/
example : ∃ i, CatalanCore.Uniform.Content.UFFamily3.RegOf i 1000 1013 :=
  thirds_cover (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
