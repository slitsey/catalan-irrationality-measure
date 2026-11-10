module
public import CatalanCore.Uniform.Bank.Irrational
@[expose] public section
set_option Elab.async false
namespace TrigammaDifferences


open CatalanCore

theorem lambda_minus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((311973 / 10000 : ℚ) : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48) - (a : ℝ) / b| := by
    have h := Aux.lambda_final false
    have e : CatalanCore.Uniform.Bank.Fourths.lambdaTarget false = (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48 := by
      simp [CatalanCore.Uniform.Bank.Fourths.lambdaTarget, sub_eq_add_neg]
    rw [e] at h
    exact h

theorem lambda_plus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((311973 / 10000 : ℚ) : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48) - (a : ℝ) / b| := by
    have h := Aux.lambda_final true
    have e : CatalanCore.Uniform.Bank.Fourths.lambdaTarget true = (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48 := by
      simp [CatalanCore.Uniform.Bank.Fourths.lambdaTarget]
    rw [e] at h
    exact h

theorem chi3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((136839 / 10000 : ℚ) : ℝ)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - (a : ℝ) / b| := by
  exact Aux.chi3_final

theorem chi3_plus_pi2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((94913 / 10000 : ℚ) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 9) - (a : ℝ) / b| := by
  exact Aux.thirds_plus_final

theorem chi3_minus_pi2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((94913 / 10000 : ℚ) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 9) - (a : ℝ) / b| := by
  exact Aux.thirds_minus_final

theorem fifths1_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((59439 / 2500 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.fifths1_final

theorem fifths2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((59439 / 2500 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.fifths2_final

theorem fifths3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((59439 / 2500 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.fifths3_final

theorem fifths4_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((59439 / 2500 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.fifths4_final

theorem sevenths1_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨0, by decide⟩

theorem sevenths2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨1, by decide⟩

theorem sevenths3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨2, by decide⟩

theorem sevenths4_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨3, by decide⟩

theorem sevenths5_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((5 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨4, by decide⟩

theorem sevenths6_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((6 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨5, by decide⟩

theorem pi2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((32607 / 5000 : ℚ) : ℝ)) <
        |Real.pi ^ 2 - (a : ℝ) / b| := by
  exact Aux.pi2_final

theorem plane1_measure (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-((206622 / 10000 : ℚ) : ℝ)) <
        |((a : ℝ) * (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + (b : ℝ) * Real.pi ^ 2) - (p : ℝ) / q| := by
  exact Aux.plane1_final a b hab

theorem plane2_measure (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-((33520 / 100 : ℚ) : ℝ)) <
        |((a : ℝ) * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) + (b : ℝ) * Real.pi ^ 2) - (p : ℝ) / q| := by
  have h := Aux.plane2_final a b hab
  rw [CatalanCore.Uniform.Bank.Plane2.riemannZeta_three_re] at h
  exact h

theorem dip_2_27_plus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((14 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + 2 * Real.pi ^ 2 / 27) - (a : ℝ) / b| := by
  have h := Aux.dip_2_27_plus_final
  have e : CatalanFrames.P6.chi3L2 + ((2 / 27 : ℚ) : ℝ) * Real.pi ^ 2 = (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + 2 * Real.pi ^ 2 / 27 := by
    show (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + ((2 / 27 : ℚ) : ℝ) * Real.pi ^ 2 = _
    push_cast; ring
  rw [e] at h
  exact h

theorem dip_2_27_minus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((14 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - 2 * Real.pi ^ 2 / 27) - (a : ℝ) / b| := by
  have h := Aux.dip_2_27_minus_final
  have e : CatalanFrames.P6.chi3L2 + ((-2 / 27 : ℚ) : ℝ) * Real.pi ^ 2 = (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - 2 * Real.pi ^ 2 / 27 := by
    show (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + ((-2 / 27 : ℚ) : ℝ) * Real.pi ^ 2 = _
    push_cast; ring
  rw [e] at h
  exact h

theorem dip_1_27_plus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((15359 / 1000 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 27) - (a : ℝ) / b| := by
  have h := Aux.dip_1_27_plus_final
  have e : CatalanFrames.P6.chi3L2 + ((1 / 27 : ℚ) : ℝ) * Real.pi ^ 2 = (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 27 := by
    show (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + ((1 / 27 : ℚ) : ℝ) * Real.pi ^ 2 = _
    push_cast; ring
  rw [e] at h
  exact h

theorem dip_1_27_minus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((15359 / 1000 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 27) - (a : ℝ) / b| := by
  have h := Aux.dip_1_27_minus_final
  have e : CatalanFrames.P6.chi3L2 + ((-1 / 27 : ℚ) : ℝ) * Real.pi ^ 2 = (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 27 := by
    show (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + ((-1 / 27 : ℚ) : ℝ) * Real.pi ^ 2 = _
    push_cast; ring
  rw [e] at h
  exact h

theorem dip_1_18_plus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((4373 / 250 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 18) - (a : ℝ) / b| := by
  have h := Aux.dip_1_18_plus_final
  have e : CatalanFrames.P6.chi3L2 + ((1 / 18 : ℚ) : ℝ) * Real.pi ^ 2 = (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 18 := by
    show (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + ((1 / 18 : ℚ) : ℝ) * Real.pi ^ 2 = _
    push_cast; ring
  rw [e] at h
  exact h

theorem dip_1_18_minus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((4373 / 250 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 18) - (a : ℝ) / b| := by
  have h := Aux.dip_1_18_minus_final
  have e : CatalanFrames.P6.chi3L2 + ((-1 / 18 : ℚ) : ℝ) * Real.pi ^ 2 = (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 18 := by
    show (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + ((-1 / 18 : ℚ) : ℝ) * Real.pi ^ 2 = _
    push_cast; ring
  rw [e] at h
  exact h

theorem zeta3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((60382 / 10000 : ℚ) : ℝ)) <
        |(∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) - (a : ℝ) / b| := by
  have h := Aux.zeta3_final
  rw [CatalanCore.Uniform.Bank.Plane2.riemannZeta_three_re] at h
  exact h

#print axioms lambda_minus_measure
#print axioms lambda_plus_measure
#print axioms chi3_measure
#print axioms chi3_plus_pi2_measure
#print axioms chi3_minus_pi2_measure
#print axioms fifths1_measure
#print axioms fifths2_measure
#print axioms fifths3_measure
#print axioms fifths4_measure
#print axioms sevenths1_measure
#print axioms sevenths2_measure
#print axioms sevenths3_measure
#print axioms sevenths4_measure
#print axioms sevenths5_measure
#print axioms sevenths6_measure
#print axioms pi2_measure
#print axioms plane1_measure
#print axioms plane2_measure
#print axioms dip_2_27_plus_measure
#print axioms dip_2_27_minus_measure
#print axioms dip_1_27_plus_measure
#print axioms dip_1_27_minus_measure
#print axioms dip_1_18_plus_measure
#print axioms dip_1_18_minus_measure
#print axioms zeta3_measure


theorem plane3_measure (a b : ℚ) (hab : a≠0 ∨ b≠0) :
    ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,(q:ℝ)^(-(72.84:ℝ))<
      |((a:ℝ)*(∑' n : ℕ,1/((n:ℝ)+1)^3)+(b:ℝ)*Real.pi^4)-(p:ℝ)/q| := by
  have h := CatalanCore.Uniform.Bank.Plane3.plane3_final a b hab
  rw [CatalanCore.Uniform.Bank.Plane2.riemannZeta_three_re] at h
  exact h
#print axioms plane3_measure
end TrigammaDifferences
