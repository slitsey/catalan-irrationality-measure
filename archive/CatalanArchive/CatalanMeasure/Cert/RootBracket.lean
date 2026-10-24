module
public import CatalanArchive.CatalanMeasure.Cert.RootBudgetCover
@[expose] public section
namespace CatalanMeasure.Cert
open Set
noncomputable section

structure RootBracket where
  lo : ℚ
  hi : ℚ
  a : ℤ
  b : ℤ
  d : ℤ

def RootBracket.signCheck (p : List ℤ) (B : RootBracket) : Bool :=
  ipOppositeCheck p B.a B.b B.d

def RootBracket.aligned (B : RootBracket) : Prop :=
  (B.a:ℚ)/B.d=B.lo ∧ (B.b:ℚ)/B.d=B.hi

instance (B : RootBracket) : Decidable B.aligned :=
  inferInstanceAs (Decidable ((B.a:ℚ)/B.d=B.lo ∧ (B.b:ℚ)/B.d=B.hi))

theorem RootBracket.root_exists {p : List ℤ} {B : RootBracket}
    (ha : B.aligned) (hs : B.signCheck p=true) :
    ∃ x ∈ Ioo (B.lo:ℝ) B.hi, ipEval p x=0 :=
  root_in_rational_bracket ha.1 ha.2 hs

theorem root_coverage_rat_brackets {p : List ℤ} {a b : ℚ} {n : ℕ}
    (B : Fin n → RootBracket) (hb : RootBudget (ipEval p) (a:ℝ) b n)
    (hi : ∀ i, a ≤ (B i).lo ∧ (B i).hi ≤ b)
    (hd : ∀ i j, i≠j → (B i).hi ≤ (B j).lo ∨ (B j).hi ≤ (B i).lo)
    (ha : ∀ i, (B i).aligned) (hs : ∀ i, (B i).signCheck p=true) :
    ∀ x ∈ Ioo (a:ℝ) b, ipEval p x=0 →
      ∃ i, x ∈ Icc ((B i).lo:ℝ) (B i).hi := by
  apply root_coverage_of_budget (fun i => (((B i).lo:ℝ),((B i).hi:ℝ))) hb
  · intro i
    change (a:ℝ) ≤ ((B i).lo:ℝ) ∧ ((B i).hi:ℝ) ≤ (b:ℝ)
    exact ⟨by exact_mod_cast (hi i).1,by exact_mod_cast (hi i).2⟩
  · intro i j hij
    change ((B i).hi:ℝ) ≤ ((B j).lo:ℝ) ∨ ((B j).hi:ℝ) ≤ ((B i).lo:ℝ)
    rcases hd i j hij with h|h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  · intro i
    exact RootBracket.root_exists (ha i) (hs i)

theorem ipHorner_ne_zero {p : List ℤ} {a d : ℤ} (hd : d≠0)
    (hn : (ipHorner a d p).2≠0) : ipEval p ((a:ℝ)/d)≠0 := by
  intro hz
  have hh := (ipHorner_eval p a d hd).2
  rw [hz,mul_zero] at hh
  exact hn (by exact_mod_cast hh)

end
end CatalanMeasure.Cert
