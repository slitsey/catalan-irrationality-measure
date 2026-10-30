module
public import CatalanCore.Cert.QuarterContour.Witness
@[expose] public section
namespace CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaP6 CatalanLambda.Cert

def qII (p q : Pt) : ℕ := (p.1-q.1).natAbs^2 + (p.2.1-q.2.1).natAbs^2 + 2^58
def iRow (p : Pt) : List Pt → ℤ
  | [] => 0
  | q :: qs => (q.2.2 : ℤ) * logLoS (qII p q) + iRow p qs

def energyTotal (all : List Pt) : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * iRow p all + energyTotal all ps
noncomputable def Jr (p q : Pt) : ℝ :=
  -(1 / 2) * ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) * ((logLoS (qII p q) : ℝ) / 2 ^ 64)

lemma row_eq (p : Pt) : ∀ l : List Pt,
    (l.map (Jr p)).sum = -((p.2.2 : ℝ) * (iRow p l : ℝ)) / 2 ^ 129 := by
  intro l
  induction l with
  | nil => simp [iRow]
  | cons q qs ih =>
    simp only [List.map_cons, List.sum_cons, ih, iRow, Jr]
    push_cast
    ring

noncomputable def cpt (p : Pt) : ℂ := ⟨(p.1 : ℝ) / 2 ^ 40, (p.2.1 : ℝ) / 2 ^ 40⟩

lemma qII_cast (p q : Pt) :
    (qII p q : ℝ) = ((p.1 : ℝ) - q.1) ^ 2 + ((p.2.1 : ℝ) - q.2.1) ^ 2 + 2 ^ 58 := by
  unfold qII
  push_cast [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  ring

lemma pair_le (p q : Pt) :
    ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) * CatalanLambda.Decay.krho (1 / 2048 : ℝ) (cpt p) (cpt q)
      ≤ Jr p q := by
  unfold CatalanLambda.Decay.krho cpt
  rw [norm_sq_mk]
  have hN : 0 < qII p q := by unfold qII; positivity
  have hq : ((p.1 : ℝ) / 2 ^ 40 - (q.1 : ℝ) / 2 ^ 40) ^ 2 + ((p.2.1 : ℝ) / 2 ^ 40 - (q.2.1 : ℝ) / 2 ^ 40) ^ 2
      + (1 / 2048 : ℝ) ^ 2 = (qII p q : ℝ) / 2 ^ 80 := by
    rw [qII_cast]; field_simp; ring
  rw [hq]
  have h1 := logLoS_spec hN
  have hn : (0 : ℝ) ≤ ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) := by positivity
  have h2 : -(1 / 2 : ℝ) * Real.log ((qII p q : ℝ) / 2 ^ 80) ≤ -(1 / 2) * ((logLoS (qII p q) : ℝ) / 2 ^ 64) := by
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn
  unfold Jr
  linarith


lemma energyTotal_eq (all : List Pt) : ∀ rows : List Pt,
    (rows.map (fun p => (all.map (Jr p)).sum)).sum = -(energyTotal all rows : ℝ) / 2^129 := by
  intro rows
  induction rows with
  | nil => simp [energyTotal]
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih, row_eq]
    simp only [energyTotal]
    push_cast
    ring

theorem energy_le (pts : List Pt) :
    CatalanLambda.Decay.Irho (1/2048 : ℝ) (positions pts) (masses pts) ≤
      -(energyTotal pts pts : ℝ) / 2^129 := by
  have h1 : CatalanLambda.Decay.Irho (1/2048 : ℝ) (positions pts) (masses pts) ≤
      ∑ k : Fin pts.length, ∑ l : Fin pts.length, Jr (pointAt pts k) (pointAt pts l) := by
    unfold CatalanLambda.Decay.Irho
    refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
    have hh := pair_le (pointAt pts k) (pointAt pts l)
    change _ ≤ _ at hh
    exact hh
  have h2 : (∑ k : Fin pts.length, ∑ l : Fin pts.length, Jr (pointAt pts k) (pointAt pts l)) =
      -(energyTotal pts pts : ℝ) / 2^129 := by
    have e : ∀ k : Fin pts.length, ∑ l : Fin pts.length, Jr (pointAt pts k) (pointAt pts l) =
        (pts.map (Jr (pointAt pts k))).sum := fun k => sum_points pts (Jr (pointAt pts k))
    simp_rw [e]
    rw [sum_points pts (fun p => (pts.map (Jr p)).sum), energyTotal_eq]
  exact h1.trans h2.le
end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.energy_le
