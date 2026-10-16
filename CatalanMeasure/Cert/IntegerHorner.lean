module
public import CatalanMeasure.Cert.DescartesBudget
public import Mathlib.Topology.Order.IntermediateValue
@[expose] public section
namespace CatalanMeasure.Cert
open Set

def ipHorner (a d : ℤ) : List ℤ → ℤ × ℤ
  | [] => (1,0)
  | c::p => let q := ipHorner a d p; (d*q.1,c*d*q.1+a*q.2)

theorem ipHorner_eval (p : List ℤ) (a d : ℤ) (hd : d≠0) :
    ((ipHorner a d p).1:ℝ)=(d:ℝ)^p.length ∧
    ((ipHorner a d p).2:ℝ)=(d:ℝ)^p.length*ipEval p ((a:ℝ)/d) := by
  induction p with
  | nil => simp [ipHorner,ipEval]
  | cons c p ih =>
    simp only [ipHorner,List.length_cons,ipEval,Int.cast_mul,Int.cast_add]
    constructor
    · rw [ih.1,pow_succ];ring
    · rw [ih.1,ih.2,pow_succ]
      have hdR : (d:ℝ)≠0 := by exact_mod_cast hd
      field_simp <;> ring

def ipOppositeCheck (p : List ℤ) (a b d : ℤ) : Bool :=
  decide (0<d ∧ a<b) &&
    ((decide ((ipHorner a d p).2<0) && decide (0<(ipHorner b d p).2)) ||
      (decide ((ipHorner b d p).2<0) && decide (0<(ipHorner a d p).2)))

theorem ipOppositeCheck_spec {p : List ℤ} {a b d : ℤ}
    (h : ipOppositeCheck p a b d=true) :
    ∃ x ∈ Ioo ((a:ℝ)/d) ((b:ℝ)/d), ipEval p x=0 := by
  simp only [ipOppositeCheck,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  have hd : (0:ℝ)<d := by exact_mod_cast h.1.1
  have hab : (a:ℝ)/d<(b:ℝ)/d := (div_lt_div_iff_of_pos_right hd).mpr (by exact_mod_cast h.1.2)
  have ha := (ipHorner_eval p a d h.1.1.ne').2
  have hb := (ipHorner_eval p b d h.1.1.ne').2
  have hdP : (0:ℝ)<(d:ℝ)^p.length := pow_pos hd _
  rcases h.2 with ⟨hl,hr⟩|⟨hl,hr⟩
  · have hlR : ipEval p ((a:ℝ)/d)<0 := by
      have hh : (((ipHorner a d p).2:ℤ):ℝ)<0 := by exact_mod_cast hl
      rw [ha] at hh
      exact neg_of_mul_neg_right hh hdP.le
    have hrR : 0 < ipEval p ((b:ℝ)/d) := by
      have hh : (0:ℝ)<((ipHorner b d p).2:ℤ) := by exact_mod_cast hr
      rw [hb] at hh
      exact (mul_pos_iff_of_pos_left hdP).mp hh
    exact intermediate_value_Ioo hab.le (by
      exact (ipPoly_continuous p).continuousOn) ⟨hlR,hrR⟩
  · have hlR : ipEval p ((b:ℝ)/d)<0 := by
      have hh : (((ipHorner b d p).2:ℤ):ℝ)<0 := by exact_mod_cast hl
      rw [hb] at hh
      exact neg_of_mul_neg_right hh hdP.le
    have hrR : 0 < ipEval p ((a:ℝ)/d) := by
      have hh : (0:ℝ)<((ipHorner a d p).2:ℤ) := by exact_mod_cast hr
      rw [ha] at hh
      exact (mul_pos_iff_of_pos_left hdP).mp hh
    exact intermediate_value_Ioo' hab.le (by
      exact (ipPoly_continuous p).continuousOn) ⟨hlR,hrR⟩

end CatalanMeasure.Cert
