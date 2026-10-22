module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Decay.Rect.CertG
@[expose] public section
open Real
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6 (qmin_cast)
set_option maxRecDepth 100000

noncomputable def gQ (s : ℂ) : ℝ :=
  gAlpha (1/2048) (1/1000) cQ mQ (1/4) (CatalanCore.Decay.Unu (1/4)) s

lemma sum_get_eq {α : Type*} (l : List α) (f : α → ℝ) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  conv_rhs => rw [← List.ofFn_get l, List.map_ofFn, List.sum_ofFn]
  rfl

lemma segCost_cast (b : QBox) : (segCost b : ℝ) =
    (((axisInterval b).2 : ℝ) - (axisInterval b).1) *
      min ((gamma b : ℝ) - (231169/100000 : ℝ)) 0 := by
  unfold segCost
  push_cast
  norm_num

lemma sum_segCost_cast (l : List QBox) :
    ((l.map segCost).sum : ℝ) = (l.map (fun b => (segCost b : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

/-- Assemble the reused continuum certificate interface from finite controls.
The list lengths are parameters and no older witness is rebuilt. -/
noncomputable def assemble {rays segs lines : List Macro} (C : Controls rays segs lines)
    (hI : CatalanLambda.Decay.Irho (1/2048 : ℝ) cQ mQ ≤ (1808029/1000000 : ℝ)) :
    CertCoreG pts.length (1/2048 : ℝ) (1/1000 : ℝ) cQ mQ where
  g := gQ
  r0 := 1/10
  W := 1/2^30
  umax := 3/2
  mprime := 231169/100000
  gmin := -143459/100000
  Sbase := -274719/10000000
  Ibound := 1808029/1000000
  ccert := 93657/12500
  r0_pos := by norm_num
  W_pos := by norm_num
  hρ := by norm_num
  hε0 := by norm_num
  hε1 := by norm_num
  hm := mQ_sum
  g_conj := g_conj_cert
  rayBoxes := rayIntervals rays
  ray_box_ok := by
    intro p hp x y h1 h2 h3 h4
    have h1' : -(1/10 : ℝ) - p.2 - 1/2^30 ≤ x := by
      convert h1 using 1 <;> norm_num
    have h2' : x ≤ -(1/10 : ℝ) - p.1 + 1/2^30 := by
      convert h2 using 1 <;> norm_num
    convert ray_box_bound C p hp x y h1' h2' h3 h4 using 1 <;> norm_num [gQ]
  ray_cover := by
    intro u h0 h1
    exact C.ray_cover u (by simpa using h0) h1
  ray_tail := by
    intro u δ hu hd
    have hu' : (3/2 : ℝ) ≤ u := by convert hu using 1 <;> norm_num
    have hd' : |δ| ≤ (1/2^30 : ℝ) := by convert hd using 1 <;> norm_num
    convert tail_core cQ mQ mQ_nonneg mQ_sum cQ_norm u δ hu' hd' using 1 <;> norm_num [gQ]
  nSeg := (boxes segs).length
  segA := fun i => (axisInterval ((boxes segs).get i)).1
  segB := fun i => (axisInterval ((boxes segs).get i)).2
  segG := fun i => gamma ((boxes segs).get i)
  seg_ab := by
    intro i
    have hs := C.seg_shape _ (List.get_mem _ i)
    dsimp [axisInterval]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hs.1) (by positivity)
  seg_ok := by
    intro i x h1 h2
    exact segment_bound C _ (List.get_mem _ i) x h1 h2
  seg_cover := by
    intro x h0 h1
    have h0' : ((-1/10 : ℚ) : ℝ) ≤ x := by norm_num; norm_num at h0; exact h0
    have h1' : ((0 : ℚ) : ℝ) ≥ x := by simpa using h1
    obtain ⟨p,hp,hp1,hp2⟩ := C.seg_cover x h0' h1'
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
    exact ⟨i, by simpa only [hi] using hp1, by simpa only [hi] using hp2⟩
  Sbase_le := by
    have hh : (-274719/10000000 : ℝ) ≤ (((boxes segs).map segCost).sum : ℝ) := by
      exact_mod_cast C.scost
    rw [sum_segCost_cast, ← sum_get_eq] at hh
    simp only [segCost_cast] at hh
    norm_num at hh ⊢
    exact hh
  lineCells := intervals lines
  line_ok := by
    intro p hp x h1 h2
    have h := line_bound C p hp x h1 h2
    norm_num at h ⊢
    exact h
  line_cover := by
    intro x h0 h1
    exact C.line_cover x (by simpa using h0) (by simpa using h1)
  I_ok := by convert hI using 1 <;> norm_num
  ccert_ge := by norm_num

theorem assemble_ccert {rays segs lines : List Macro} (C : Controls rays segs lines)
    (hI : CatalanLambda.Decay.Irho (1/2048 : ℝ) cQ mQ ≤ (1808029/1000000 : ℝ)) :
    (assemble C hI).ccert = 93657/12500 := rfl

theorem assemble_D_le {rays segs lines : List Macro} (C : Controls rays segs lines)
    (hI : CatalanLambda.Decay.Irho (1/2048 : ℝ) cQ mQ ≤ (1808029/1000000 : ℝ)) :
    (1158407/250000 : ℚ) ≤ (assemble C hI).Dof 3 (1/4) (184428/100000) := by
  unfold CertCoreG.Dof assemble
  norm_num
end CatalanCore.Cert.SigmaQuarter
#print axioms CatalanCore.Cert.SigmaQuarter.assemble
