module
public import CatalanCore.Linalg.Bareiss
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

def matrixDen (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  ∏ i : Fin n,∏ j : Fin n,(M i j).den
def clearMatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j=>((matrixDen n M:ℚ)*M i j).num
def ratDet (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) : Option ℚ :=
  (CatalanCore.Linalg.bareissChecked n (clearMatrix n M)).map
    (fun x=>(x:ℚ)/(matrixDen n M:ℚ)^n)

theorem matrixDen_pos (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) : 0<matrixDen n M := by
  exact Finset.prod_pos (fun i _=>Finset.prod_pos (fun j _=>(M i j).den_pos))

theorem clearMatrix_cast (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (clearMatrix n M i j:ℚ)=(matrixDen n M:ℚ)*M i j := by
  have h1 : (M i j).den∣∏ k : Fin n,(M i k).den :=
    Finset.dvd_prod_of_mem (fun k : Fin n=>(M i k).den) (Finset.mem_univ j)
  have h2 : (∏ k : Fin n,(M i k).den)∣matrixDen n M :=
    Finset.dvd_prod_of_mem (fun k : Fin n=>∏ l : Fin n,(M k l).den) (Finset.mem_univ i)
  have hd := dvd_trans h1 h2
  obtain ⟨k,hk⟩ := hd
  have hq : M i j*((M i j).den:ℚ)=((M i j).num:ℚ) :=
    (eq_div_iff (by exact_mod_cast (M i j).den_ne_zero)).mp (Rat.num_div_den (M i j)).symm
  have he : (matrixDen n M:ℚ)*M i j=(((k:ℤ)*(M i j).num:ℤ):ℚ) := by
    rw [hk,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
    rw [←hq]
    ring
  change (((matrixDen n M:ℚ)*M i j).num:ℚ)=(matrixDen n M:ℚ)*M i j
  apply Rat.coe_int_num_of_den_eq_one
  rw [he]
  exact Rat.den_intCast _

theorem ratDet_sound (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (q : ℚ)
    (h : ratDet n M=some q) : M.det=q := by
  unfold ratDet at h
  cases hb : CatalanCore.Linalg.bareissChecked n (clearMatrix n M) with
  | none => simp [hb] at h
  | some d =>
    simp [hb] at h
    have hd := CatalanCore.Linalg.bareiss_sound n (clearMatrix n M) d hb
    have hM : (clearMatrix n M).map (Int.castRingHom ℚ)=(matrixDen n M:ℚ) • M := by
      apply Matrix.ext
      intro i j
      exact clearMatrix_cast n M i j
    have hdet := congrArg Matrix.det hM
    simp only [Int.coe_castRingHom] at hdet
    rw [←Int.cast_det,←hd,Matrix.det_smul,Fintype.card_fin] at hdet
    have hn : (matrixDen n M:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt (matrixDen_pos n M))
    rw [←h,hdet]
    field_simp

#print axioms clearMatrix_cast
#print axioms ratDet_sound
end
end CatalanCore.Li2.NVMod
