module
public import CatalanCore.Cert.QuarterContour.ModelGeometry
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterCompute.Model

lemma validJet_facts (S : ℕ) (m : Params) (p : Pt) (j : Jet) (h : validJet S m p j = true) :
    0 < q0N m p ∧ j.2.2 = p.2.2 ∧
    j.1*q0N m p ≤ (S : ℤ)*an m p ∧ (S : ℤ)*an m p < (j.1+1)*q0N m p ∧
    j.2.1*q0N m p ≤ (S : ℤ)*bn m ∧ (S : ℤ)*bn m < (j.2.1+1)*q0N m p ∧
    ratioNumerator j < S := by
  simpa only [validJet,ratioNumerator,decide_eq_true_eq] using h

lemma ratioNumerator_cast (j : Jet) :
    (ratioNumerator j : ℝ) = |(j.1 : ℝ)|+|(j.2.1 : ℝ)|+2 := by
  simp only [ratioNumerator,Nat.cast_add,Nat.cast_ofNat,Nat.cast_natAbs,Int.cast_abs]

noncomputable def modelZ (m : Params) (v : ℝ) : ℂ :=
  ⟨((m.X0 : ℝ)+(m.DX : ℝ)*v)/(m.U : ℝ), ((m.Y0 : ℝ)+(m.DY : ℝ)*v)/(m.U : ℝ)⟩
noncomputable def rawQ (m : Params) (p : Pt) (v : ℝ) : ℝ :=
  ((m.X0 : ℝ)+(m.DX : ℝ)*v-(p.1 : ℝ)*(step m : ℝ))^2+
  ((m.Y0 : ℝ)+(m.DY : ℝ)*v-(p.2.1 : ℝ)*(step m : ℝ))^2+((m.U/2048 : ℕ) : ℝ)^2
noncomputable def exactT (m : Params) (p : Pt) (v : ℝ) : ℝ :=
  ((an m p : ℝ)/(q0N m p : ℝ))*v+((bn m : ℝ)/(q0N m p : ℝ))*v^2
noncomputable def roundedT (S : ℕ) (j : Jet) (v : ℝ) : ℝ :=
  ((j.1 : ℝ)*v+(j.2.1 : ℝ)*v^2)/(S : ℝ)
noncomputable def radius (S : ℕ) (j : Jet) : ℝ := (ratioNumerator j : ℝ)/(S : ℝ)

lemma jet_rounding (S : ℕ) (m : Params) (p : Pt) (j : Jet) (h : validJet S m p j = true)
    (v : ℝ) (hv : |v| ≤ 1) :
    0 < (S : ℝ) ∧ radius S j < 1 ∧
    |exactT m p v-roundedT S j v| ≤ 2/(S : ℝ) ∧
    |exactT m p v| ≤ radius S j ∧ |roundedT S j v| ≤ radius S j := by
  obtain ⟨hq,hm,hal,hau,hbl,hbu,hcap⟩ := validJet_facts S m p j h
  have hSN : 0 < S := by unfold ratioNumerator at hcap;omega
  have hS : 0 < (S : ℝ) := by exact_mod_cast hSN
  have hqR : 0 < (q0N m p : ℝ) := by exact_mod_cast hq
  have ha := floor_error (S : ℝ) (q0N m p : ℝ) (an m p : ℝ) (j.1 : ℝ) hS hqR
    (by exact_mod_cast hal) (by exact_mod_cast hau)
  have hb := floor_error (S : ℝ) (q0N m p : ℝ) (bn m : ℝ) (j.2.1 : ℝ) hS hqR
    (by exact_mod_cast hbl) (by exact_mod_cast hbu)
  have hr : radius S j < 1 := (div_lt_one hS).mpr (by exact_mod_cast hcap)
  have hs := rounded_ratio_bounds ((an m p : ℝ)/(q0N m p : ℝ)) ((bn m : ℝ)/(q0N m p : ℝ))
    (j.1 : ℝ) (j.2.1 : ℝ) (S : ℝ) v hS ha hb hv
  rw [← ratioNumerator_cast j] at hs
  exact ⟨hS,hr,hs⟩

lemma jet_log_error (S : ℕ) (m : Params) (p : Pt) (j : Jet) (h : validJet S m p j = true)
    (v : ℝ) (hv : |v| ≤ 1) (n : ℕ) :
    |Real.log (1+exactT m p v)-LogModel.poly n (roundedT S j v)| ≤
      ((radius S j)^(n+1)+2/(S : ℝ))/(1-radius S j) := by
  obtain ⟨hS,hr,hd,ht,ht'⟩ := jet_rounding S m p j h v hv
  exact LogModel.rounded_error ht ht' hr hd n

lemma rawQ_identity (m : Params) (p : Pt) (v : ℝ) :
    rawQ m p v = (q0N m p : ℝ)+(an m p : ℝ)*v+(bn m : ℝ)*v^2 := by
  unfold rawQ q0N an bn
  simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat,Int.cast_ofNat]
  ring

lemma rawQ_factor (m : Params) (p : Pt) (v : ℝ) (hq : q0N m p ≠ 0) :
    rawQ m p v = (q0N m p : ℝ)*(1+exactT m p v) := by
  rw [rawQ_identity]
  unfold exactT
  have hqr : (q0N m p : ℝ) ≠ 0 := by exact_mod_cast hq
  field_simp
  ring
end CatalanCore.Cert.QuarterContour.ModelGeometry
#print axioms CatalanCore.Cert.QuarterContour.ModelGeometry.jet_log_error