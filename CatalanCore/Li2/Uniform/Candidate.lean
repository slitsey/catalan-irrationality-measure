module
public import CatalanCore.Li2.Uniform.TableSpec
public import CatalanCore.Li2.Uniform.Structure
public import CatalanCore.Li2.Uniform.Geometry
public import CatalanCore.Li2.Decay.Assembly
@[expose] public section
/-! Generic table candidate semantics and terminal LD29 adapter. No fixed table or certificate data. -/
set_option Elab.async false
open MeasureTheory Set Filter Complex
open scoped Topology
namespace CatalanCore.Li2.Uniform
inductive Candidate (T : NodeTable) : ℤ → ℝ → ℝ → ℝ → Prop
  | interp (i j : Fin T.pairCount) (s : ℤ) (t r l : ℝ)
      (hp : (i, j) ∈ T.interpPairs)
      (hsi : (T.entryNode i).usedFor s) (hsj : (T.entryNode j).usedFor s)
      (hl : l ∈ Icc 0 1)
      (ht : t = l * (T.entryNode i).t + (1 - l) * (T.entryNode j).t)
      (hr : l * ((T.entries i).rho : ℝ) + (1 - l) * ((T.entries j).rho : ℝ) ≤ r) :
      Candidate T s t r (l * ((T.entries i).lower : ℝ) + (1 - l) * ((T.entries j).lower : ℝ))
  | transport (i : Fin T.pairCount) (s : ℤ) (t r : ℝ) (m : ℚ)
      (hs : (T.entryNode i).usedFor s) (ht : (T.entryNode i).t ≤ t)
      (hm : ((T.entryNode i).frame = .lattice ∧ m ∈ T.slopes) ∨ m = 0)
      (hr : ((T.entries i).rho : ℝ) + (4 + (m : ℝ)) * (t - (T.entryNode i).t) ≤ r) :
      Candidate T s t r (((T.entries i).lower : ℝ) +
        (2 * (m : ℝ) - (m : ℝ) ^ 2) * (t - (T.entryNode i).t))

structure TableSound (T : NodeTable) where
  valid : TableValid T
  frames : FrameKey → DualFrame
  geometry : ∀ f, FrameGeometry (frames f)
  pure_frame : (frames .lattice).pure = true
  bent_cut : ∀ f, f ≠ .lattice → frameCut (geometry f) = some 0
  datum : Fin T.pairCount → DualDatum
  level : Fin T.pairCount → ℝ
  admissible : ∀ i, Admissible (frames (T.entryNode i).frame)
    (T.entryNode i).sign (T.entryNode i).t (datum i) (level i)
  bound : ∀ i, ((T.entries i).lower : ℝ) ≤
    dual (frames (T.entryNode i).frame) (T.entryNode i).sign
      (T.entryNode i).t (T.entries i).rho (datum i) (level i)
noncomputable def Dlow (T : NodeTable) (s : ℤ) (t r : ℝ) : EReal :=
  sSup {x : EReal | ∃ D : ℝ, Candidate T s t r D ∧ x=(D:EReal)}
private theorem entry_t_pos (T : NodeTable) (H : TableSound T) (i : Fin T.pairCount) :
    0 < (T.entryNode i).t := by
  have hq := H.valid.1 (T.entries i).node
  have hq0 : 0 < ((T.nodes (T.entries i).node).magnitude:ℝ) := by exact_mod_cast hq.1
  have hq1 : ((T.nodes (T.entries i).node).magnitude:ℝ) < 1 := by exact_mod_cast hq.2
  change 0 < Real.log (1/((T.nodes (T.entries i).node).magnitude:ℝ))
  exact Real.log_pos ((one_lt_div hq0).mpr hq1)
private theorem entry_semantics (T : NodeTable) (H : TableSound T)
    (i : Fin T.pairCount) (s : ℤ) (hs : (T.entryNode i).usedFor s) :
    Admissible (H.frames (T.entryNode i).frame) s (T.entryNode i).t (H.datum i) (H.level i) ∧
    CapIntegrable (H.frames (T.entryNode i).frame) s (T.entryNode i).t (T.entries i).rho (H.datum i) (H.level i) ∧
    ((T.entries i).lower:ℝ) ≤ dual (H.frames (T.entryNode i).frame) s (T.entryNode i).t (T.entries i).rho (H.datum i) (H.level i) := by
  have hh : Admissible (H.frames (T.entryNode i).frame) s (T.entryNode i).t (H.datum i) (H.level i) ∧
      ((T.entries i).lower:ℝ) ≤ dual (H.frames (T.entryNode i).frame) s (T.entryNode i).t (T.entries i).rho (H.datum i) (H.level i) := by
    have ha := H.admissible i
    have hb := H.bound i
    by_cases hf : (T.entryNode i).frame = .lattice
    · have hp : (H.frames (T.entryNode i).frame).pure=true := by rw [hf]; exact H.pure_frame
      have he := lattice_sign_blind (H.frames (T.entryNode i).frame) hp (T.entryNode i).sign s
        (H.datum i) (T.entryNode i).t (T.entries i).rho (H.level i)
      rw [he.1] at ha
      rw [he.2.2] at hb
      exact ⟨ha,hb⟩
    · have hsneg : s = -1 := hs.2.resolve_left hf
      have he : (T.entryNode i).sign=s := by simp only [Node.sign,hf,↓reduceIte,hsneg]
      rw [he] at ha hb
      exact ⟨ha,hb⟩
  exact ⟨hh.1,cap_integrable _ (H.geometry _) s _ _ (entry_t_pos T H i) _ _,hh.2⟩

theorem candidate_has_datum (T : NodeTable) (H : TableSound T)
    (s : ℤ) (t r D : ℝ) (hD : Candidate T s t r D) :
    ∃ f : FrameKey, ∃ d : DualDatum, ∃ θ : ℝ,
      Admissible (H.frames f) s t d θ ∧ CapIntegrable (H.frames f) s t r d θ ∧
        D ≤ dual (H.frames f) s t r d θ := by
  cases hD with
  | interp i j s t r l hp hsi hsj hl ht hr =>
    have hf := ((H.valid.2.2.2.2.2 i j).mp hp).1
    have hi := entry_semantics T H i s hsi
    have hj := entry_semantics T H j s hsj
    rw [← hf] at hj
    subst t
    have hmix := dual_joint_concave (H.frames (T.entryNode i).frame) s
      (H.datum i) (H.datum j) (T.entryNode i).t (T.entryNode j).t
      (T.entries i).rho (T.entries j).rho (H.level i) (H.level j) l hl hi.1 hj.1 hi.2.1 hj.2.1
    have hmono := dual_mono_rho (H.frames (T.entryNode i).frame) s (mixDatum l hl (H.datum i) (H.datum j))
      (l*(T.entryNode i).t+(1-l)*(T.entryNode j).t) (l*H.level i+(1-l)*H.level j)
      (l*((T.entries i).rho:ℝ)+(1-l)*((T.entries j).rho:ℝ)) r hr hmix.2.1
    refine ⟨(T.entryNode i).frame,mixDatum l hl (H.datum i) (H.datum j),l*H.level i+(1-l)*H.level j,
      hmix.1,hmono.1,?_⟩
    have hb0 := mul_le_mul_of_nonneg_left hi.2.2 hl.1
    have hb1 := mul_le_mul_of_nonneg_left hj.2.2 (sub_nonneg.mpr hl.2)
    exact ((add_le_add hb0 hb1).trans hmix.2.2).trans hmono.2
  | transport i s t r m hs ht hm hr =>
    have hi := entry_semantics T H i s hs
    have hmR : (m:ℝ) ∈ Icc 0 1 := by
      rcases hm with ⟨hf,hmem⟩ | rfl
      · rw [H.valid.2.2.2.2.1] at hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num
      · norm_num
    have hfree : ∀ u ∈ (H.frames (T.entryNode i).frame).free s, (m:ℝ) ≤ u.re := by
      rcases hm with ⟨hf,hmem⟩ | hm0
      · rw [hf]
        simp only [(H.frames .lattice).pure_free H.pure_frame,Set.mem_empty_iff_false,false_implies,implies_true]
      · rw [hm0,Rat.cast_zero]
        exact (goodFrame_halfplane _ (H.geometry _) s).1
    let Δ := t-(T.entryNode i).t
    have hΔ : 0 ≤ Δ := sub_nonneg.mpr ht
    have he : (T.entryNode i).t+Δ=t := by dsimp [Δ]; ring
    have hu := dual_transport (H.frames (T.entryNode i).frame) s (H.datum i)
      (T.entryNode i).t (T.entries i).rho (H.level i) (m:ℝ) Δ hmR hΔ hfree hi.1 hi.2.1
    rw [he] at hu
    have hmono := dual_mono_rho (H.frames (T.entryNode i).frame) s (H.datum i) t
      (H.level i-(m:ℝ)*Δ) (((T.entries i).rho:ℝ)+(4+(m:ℝ))*Δ) r hr hu.2.1
    refine ⟨(T.entryNode i).frame,H.datum i,H.level i-(m:ℝ)*Δ,hu.1,hmono.1,?_⟩
    have hh := add_le_add hi.2.2 (le_refl ((2*(m:ℝ)-(m:ℝ)^2)*Δ))
    exact (hh.trans hu.2.2).trans hmono.2

theorem D_ge_of_candidate (T : NodeTable) (H : TableSound T)
    (z : ℚ) (hz0 : z ≠ 0) (hz1 : |(z:ℝ)| < 1)
    (r D : ℝ) (hr : 0 < r)
    (hD : Candidate T (Int.sign z.num) (Real.log (1/|(z:ℝ)|)) r D) :
    CatalanCore.Uniform.HasScaledDecay (CatalanCore.Li2.li2Family z) CatalanCore.Li2.scale D r := by
  obtain ⟨f,d,θ,hadm,hcap,hbound⟩ :=
    candidate_has_datum T H (Int.sign z.num) (Real.log (1/|(z:ℝ)|)) r D hD
  exact CatalanCore.Li2.Decay.li2_family_decay z hz0 hz1 (H.frames f) (H.geometry f) d r θ D hr hadm hcap hbound

end CatalanCore.Li2.Uniform
#print axioms CatalanCore.Li2.Uniform.Candidate
#print axioms CatalanCore.Li2.Uniform.TableSound
#print axioms CatalanCore.Li2.Uniform.candidate_has_datum
#print axioms CatalanCore.Li2.Uniform.Dlow

#print axioms CatalanCore.Li2.Uniform.D_ge_of_candidate
