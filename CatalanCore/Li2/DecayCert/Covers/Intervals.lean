module
public import CatalanCore.Li2.DecayCert.Lines
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
structure QInterval where
  left : ℚ
  right : ℚ

def chainCheck : ℚ → ℚ → List QInterval → Bool
  | a,b,[] => decide (a=b)
  | a,b,c::cs => decide (c.left=a ∧ c.left < c.right ∧ c.right ≤ b) && chainCheck c.right b cs

theorem chainCheck_sound (a b : ℚ) (cs : List QInterval) (hc : chainCheck a b cs=true) :
    a ≤ b ∧ cs.Pairwise (fun c d => c.right ≤ d.left) ∧
    (∀ c ∈ cs,a ≤ c.left ∧ c.left < c.right ∧ c.right ≤ b) ∧
    Ioc (a:ℝ) (b:ℝ)=⋃ c ∈ cs,Ioc (c.left:ℝ) (c.right:ℝ) := by
  induction cs generalizing a with
  | nil =>
    have he : a=b := of_decide_eq_true hc
    subst b
    simp
  | cons c cs ih =>
    simp only [chainCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
    obtain ⟨⟨he,hlt,hle⟩,ht⟩ := hc
    rcases ih c.right ht with ⟨hab,hpair,hbounds,hcover⟩
    have hac : a < c.right := by simpa only [he] using hlt
    have hab' : a ≤ b := hac.le.trans hle
    refine ⟨hab',?_,?_,?_⟩
    · rw [List.pairwise_cons]
      exact ⟨fun d hd => (hbounds d hd).1,hpair⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨he.ge,hlt,hle⟩
      · have hb := hbounds d hd
        exact ⟨hac.le.trans hb.1,hb.2.1,hb.2.2⟩
    · have hcons : (⋃ d ∈ c::cs,Ioc (d.left:ℝ) (d.right:ℝ))=
          Ioc (c.left:ℝ) (c.right:ℝ) ∪ (⋃ d ∈ cs,Ioc (d.left:ℝ) (d.right:ℝ)) := by ext x; simp
      rw [hcons,← hcover,he]
      ext x
      simp only [mem_Ioc,mem_union]
      have hacR : (a:ℝ) ≤ (c.right:ℝ) := by exact_mod_cast hac.le
      have hcbR : (c.right:ℝ) ≤ (b:ℝ) := by exact_mod_cast hle
      constructor
      · intro hx
        by_cases hxr : x ≤ (c.right:ℝ)
        · exact Or.inl ⟨hx.1,hxr⟩
        · exact Or.inr ⟨lt_of_not_ge hxr,hx.2⟩
      · rintro (hx | hx)
        · exact ⟨hx.1,hx.2.trans hcbR⟩
        · exact ⟨hacR.trans_lt hx.1,hx.2⟩
#print axioms chainCheck_sound
end CatalanCore.Li2.DecayCert
