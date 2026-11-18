module
public import CatalanCore.Li2.NVMod.AtOne
public import CatalanCore.Li2.NVMod.RationalDet
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

def oneOrder (A : TypeKey) : ℤ :=
  (∑ i : Fin A.size,oneR A i)+(∑ j : Fin A.size,oneC A j)
def oneLead (A : TypeKey) : Option ℚ :=
  if h0 A<0 then some (∏ k : Fin A.size,
    (Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+(h0 A).natAbs):ℚ))
  else if Odd (h0 A) then
    if A.size≤oneH1 A then ratDet A.size (regularHankel A A.size)
    else (ratDet (oneH1 A) (regularHankel A (oneH1 A))).map
      (fun q=>q*∏ k : Fin (A.size-oneH1 A),(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+1):ℚ))
  else if A.size≤oneH1 A+1 then ratDet A.size (regularHankel A A.size)
  else (ratDet (oneH1 A+1) (cornerHankel A)).map
    (fun q=>q*∏ k : Fin (A.size-oneH1 A-1),(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+2):ℚ))

theorem ratDet_map_sound (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (f : ℚ→ℚ) (q : ℚ)
    (h : (ratDet n M).map f=some q) : f M.det=q := by
  cases hd : ratDet n M with
  | none => simp [hd] at h
  | some r =>
    simp only [hd,Option.map_some,Option.some.injEq] at h
    rw [ratDet_sound n M r hd]
    exact h

theorem oneLead_sound (A : TypeKey) (hf : FactorialDetChecked A) (q : ℚ)
    (h : oneLead A=some q) : (oneMatrix A).det=q := by
  classical
  rw [one_matrix_det A hf]
  unfold oneLead at h
  split_ifs at h ⊢
  · exact Option.some.inj h
  · exact ratDet_sound _ _ q h
  · exact ratDet_map_sound _ _ _ q h
  · exact ratDet_sound _ _ q h
  · exact ratDet_map_sound _ _ _ q h

theorem hankel_one_lead (A : TypeKey) (hf : FactorialDetChecked A) (q : ℚ)
    (h : oneLead A=some q) :
    Oge (atOne (constantRF A)) (oneOrder A) ∧
      (atOne (constantRF A)).coeff (oneOrder A)=q := by
  have hh := hankel_at_one A
  change Oge (atOne (constantRF A)) (oneOrder A) ∧
    (atOne (constantRF A)).coeff (oneOrder A)=(oneMatrix A).det at hh
  rw [oneLead_sound A hf q h] at hh
  exact hh

#print axioms oneLead_sound
#print axioms hankel_one_lead
end
end CatalanCore.Li2.NVMod

