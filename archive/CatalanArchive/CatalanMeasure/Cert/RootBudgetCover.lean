module
public import CatalanArchive.CatalanMeasure.Cert.DescartesBudget
public import CatalanArchive.CatalanMeasure.Cert.IntegerHorner
@[expose] public section
namespace CatalanMeasure.Cert
open Set
noncomputable section

def rootGapSeparationOK (ps : List Piece) : Bool :=
  ps.all fun p => p.2.2 || ps.all fun q => !q.2.2 ||
    decide (p.2.1 ≤ q.1 ∨ q.2.1 ≤ p.1)

def rootGapDomainOK (ps : List Piece) (a b : ℚ) (excludeZero : Bool) : Bool :=
  ps.all fun p => p.2.2 ||
    (decide (a ≤ p.1 ∧ p.2.1 ≤ b) &&
      (!excludeZero || decide (p.2.1 ≤ 0 ∨ 0 ≤ p.1)))

theorem noRootGaps_of_root_coverage {A : List ℚ} {Z : List ℤ} {c a b : ℚ}
    {ps : List Piece} {excludeZero : Bool} (hc : c≠0)
    (hA : A=lpSmul c (Z.map (fun z : ℤ => (z:ℚ))))
    (hdomain : rootGapDomainOK ps a b excludeZero=true)
    (hseparate : rootGapSeparationOK ps=true)
    (hcover : ∀ x ∈ Ioo (a:ℝ) b, (excludeZero=true → x≠0) → ipEval Z x=0 →
      ∃ q ∈ ps, q.2.2=true ∧ x ∈ Icc (q.1:ℝ) q.2.1) :
    NoRootGaps A ps := by
  intro p hp hfalse x hx hz
  have hdom := (List.all_eq_true.mp hdomain) p hp
  simp only [rootGapDomainOK,hfalse,Bool.false_or,Bool.and_eq_true,
    Bool.or_eq_true,decide_eq_true_eq] at hdom
  have hxmin : (a:ℝ) ≤ p.1 := by exact_mod_cast hdom.1.1
  have hxmax : (p.2.1:ℝ) ≤ b := by exact_mod_cast hdom.1.2
  have hg : x ∈ Ioo (a:ℝ) b := ⟨lt_of_le_of_lt hxmin hx.1,lt_of_lt_of_le hx.2 hxmax⟩
  have hnzero : excludeZero=true → x≠0 := by
    intro he hz
    have hh := hdom.2
    simp only [he,Bool.not_true,Bool.false_eq_true,false_or] at hh
    rcases hh with hn|hp
    · have hhR : (p.2.1:ℝ) ≤ 0 := by exact_mod_cast hn
      linarith only [hx.2,hhR,hz]
    · have hhR : (0:ℝ) ≤ p.1 := by exact_mod_cast hp
      linarith only [hx.1,hhR,hz]
  rw [hA,lpEval_smul,lpEval_int_cast] at hz
  have hcR : (c:ℝ)≠0 := by exact_mod_cast hc
  obtain ⟨q,hq,htrue,hxq⟩ := hcover x hg hnzero ((mul_eq_zero.mp hz).resolve_left hcR)
  have hsep := (List.all_eq_true.mp hseparate) p hp
  simp only [hfalse,Bool.false_or] at hsep
  have hsepq := (List.all_eq_true.mp hsep) q hq
  simp only [htrue,Bool.not_true,Bool.false_or,decide_eq_true_eq] at hsepq
  rcases hsepq with hlo|hhi
  · have hhR : (p.2.1:ℝ) ≤ q.1 := by exact_mod_cast hlo
    linarith only [hx.2,hxq.1,hhR]
  · have hhR : (q.2.1:ℝ) ≤ p.1 := by exact_mod_cast hhi
    linarith only [hx.1,hxq.2,hhR]

theorem root_in_rational_bracket {p : List ℤ} {l h : ℚ} {a b d : ℤ}
    (hl : (a:ℚ)/d=l) (hr : (b:ℚ)/d=h) (hc : ipOppositeCheck p a b d=true) :
    ∃ x ∈ Ioo (l:ℝ) h, ipEval p x=0 := by
  have hlR : (a:ℝ)/d=(l:ℝ) := by exact_mod_cast hl
  have hrR : (b:ℝ)/d=(h:ℝ) := by exact_mod_cast hr
  simpa only [hlR,hrR] using ipOppositeCheck_spec hc

end
end CatalanMeasure.Cert
