module
public import CatalanCore.Li2.DecayCert.Source.Sound
public import CatalanCore.Li2.Uniform.Datum
public import CatalanCore.Uniform.Decay.Tools.BernsteinList
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Polynomial
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert

theorem sourceParameter_map (s : QSegment) :
    s.parameterMeasure.map (fun x : ℝ => cqReal s.mid+cqReal s.half*(x:ℂ))=s.measure := by
  unfold QSegment.parameterMeasure QSegment.measure CatalanCore.Tools.Joukowski.segMeasure
  rw [Measure.map_map (by fun_prop) Real.measurable_cos]
  rfl

theorem sourceParameter_atomless (s : QSegment) (x : ℝ) : s.parameterMeasure {x}=0 := by
  unfold QSegment.parameterMeasure
  rw [Measure.map_apply Real.measurable_cos (measurableSet_singleton x)]
  apply withDensity_absolutelyContinuous
  have hm : MeasurableSet (Real.cos ⁻¹' ({x}:Set ℝ)) :=
    Real.measurable_cos (measurableSet_singleton x)
  have hsub : (Real.cos ⁻¹' ({x}:Set ℝ)) ∩ Icc 0 Real.pi ⊆ {Real.arccos x} := by
    intro θ hθ
    have hc : Real.cos θ=x := hθ.1
    have hi := Real.arccos_cos hθ.2.1 hθ.2.2
    rw [hc] at hi
    exact hi.symm
  have hv : volume ((Real.cos ⁻¹' ({x}:Set ℝ)) ∩ Icc 0 Real.pi)=0 :=
    measure_mono_null hsub (measure_singleton _)
  have ha := CatalanCore.Zeta5.Potential.arc_apply_le (Real.cos ⁻¹' ({x}:Set ℝ)) hm
  rw [hv,mul_zero] at ha
  exact le_antisymm ha bot_le

theorem sourceParameter_supported (s : QSegment) : s.parameterMeasure (Icc (-1:ℝ) 1)ᶜ=0 := by
  unfold QSegment.parameterMeasure
  rw [Measure.map_apply Real.measurable_cos measurableSet_Icc.compl]
  have he : Real.cos ⁻¹' (Icc (-1:ℝ) 1)ᶜ=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro θ hθ
    exact hθ ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩
  rw [he,measure_empty]

#print axioms sourceParameter_map
#print axioms sourceParameter_atomless
#print axioms sourceParameter_supported

noncomputable section
inductive BernsteinTree
  | leaf : ℕ → List ℚ → BernsteinTree
  | split : ℚ → BernsteinTree → BernsteinTree → BernsteinTree

def bernCoeff (p : ℚ[X]) (a b : ℚ) (N k : ℕ) : ℚ :=
  CatalanCore.Uniform.Decay.Tools.bernK
    (CatalanCore.Uniform.Decay.Tools.affK p.coeff N a (b-a)) N k

def bernCheck (p : ℚ[X]) : ℚ → ℚ → BernsteinTree → Bool
  | a,b,.leaf N cs => decide (a≤b ∧ p.natDegree≤N ∧ cs.length=N+1 ∧
      cs=(List.range (N+1)).map (bernCoeff p a b N) ∧ ∀ c∈cs,0≤c)
  | a,b,.split mid L R => decide (a<mid ∧ mid<b) && bernCheck p a mid L && bernCheck p mid b R

open CatalanCore.Uniform.Decay.Tools

theorem cast_bernCoeff (p : ℚ[X]) (a b : ℚ) (N k : ℕ) :
    (bernCoeff p a b N k:ℝ)=
      bern (affCoeffs (fun j => (p.coeff j:ℝ)) N (a:ℝ) ((b:ℝ)-a)) N k := by
  simp only [bernCoeff,bernK_eq,affK_eq,bern,affCoeffs]
  push_cast
  rfl

theorem bernLeaf_sound (p : ℚ[X]) (a b : ℚ) (N : ℕ) (cs : List ℚ)
    (hc : bernCheck p a b (.leaf N cs)=true) :
    ∀ x∈Icc (a:ℝ) (b:ℝ),0≤(p.map (Rat.castHom ℝ)).eval x := by
  have hg : a≤b ∧ p.natDegree≤N ∧ cs.length=N+1 ∧
      cs=(List.range (N+1)).map (bernCoeff p a b N) ∧ ∀ c∈cs,0≤c :=
    of_decide_eq_true hc
  rcases hg with ⟨hab,hN,hlen,hcs,hpos⟩
  let upper : ℝ := ∑ k∈Finset.range (N+1), |(bernCoeff p a b N k:ℝ)|
  have hlo : ∀ k≤N,0≤bern (affCoeffs (fun j => (p.coeff j:ℝ)) N (a:ℝ) ((b:ℝ)-a)) N k := by
    intro k hk
    rw [← cast_bernCoeff]
    have hm : bernCoeff p a b N k∈cs := by
      rw [hcs]
      exact List.mem_map.mpr ⟨k,List.mem_range.mpr (by omega),rfl⟩
    exact_mod_cast hpos _ hm
  have hhi : ∀ k≤N,bern (affCoeffs (fun j => (p.coeff j:ℝ)) N (a:ℝ) ((b:ℝ)-a)) N k≤upper := by
    intro k hk
    rw [← cast_bernCoeff]
    refine (le_abs_self ((bernCoeff p a b N k:ℚ):ℝ)).trans ?_
    change |((bernCoeff p a b N k:ℚ):ℝ)| ≤
      ∑ i∈Finset.range (N+1), |((bernCoeff p a b N i:ℚ):ℝ)|
    exact Finset.single_le_sum (s := Finset.range (N+1))
      (f := fun i : ℕ => |((bernCoeff p a b N i:ℚ):ℝ)|) (a := k)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
  intro x hx
  have habR : (a:ℝ)≤(b:ℝ) := Rat.cast_le.mpr hab
  obtain ⟨t,ht0,ht1,he⟩ : ∃ t : ℝ,0≤t ∧ t≤1 ∧ (a:ℝ)+((b:ℝ)-a)*t=x := by
    rcases lt_or_eq_of_le habR with hlt | heq
    · refine ⟨(x-a)/((b:ℝ)-a),div_nonneg (by linarith [hx.1]) (by linarith),?_,?_⟩
      · rw [div_le_one (by linarith : 0<(b:ℝ)-a)]; linarith [hx.2]
      · field_simp; ring
    · refine ⟨0,le_rfl,zero_le_one,?_⟩
      have hxa : x=(a:ℝ) := by linarith [hx.1,hx.2]
      simp only [mul_zero,add_zero,hxa]
  have hb := (bernstein_range _ N hlo hhi ht0 ht1).1
  rw [peval_affCoeffs,he] at hb
  have hev : (p.map (Rat.castHom ℝ)).eval x=peval (fun j => (p.coeff j:ℝ)) N x := by
    rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) (by omega : p.natDegree<N+1)]
    rfl
  rw [hev]
  exact hb

theorem bernCheck_sound (p : ℚ[X]) (a b : ℚ) (w : BernsteinTree)
    (hc : bernCheck p a b w=true) :
    ∀ x∈Icc (a:ℝ) (b:ℝ),0≤(p.map (Rat.castHom ℝ)).eval x := by
  induction w generalizing a b with
  | leaf N cs => exact bernLeaf_sound p a b N cs hc
  | split mid L R ihL ihR =>
    have hh : (a<mid ∧ mid<b) ∧ bernCheck p a mid L=true ∧ bernCheck p mid b R=true := by
      simpa only [bernCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc
    intro x hx
    by_cases hm : x≤(mid:ℝ)
    · exact ihL a mid hh.2.1 x ⟨hx.1,hm⟩
    · exact ihR mid b hh.2.2 x ⟨le_of_not_ge hm,hx.2⟩

theorem dens_pos_bernstein (p : ℝ[X]) (n : ℕ) (b : Fin (n+1) → ℝ)
    (hrep : p=∑ k : Fin (n+1), Polynomial.C (b k*(n.choose k:ℝ))*
      Polynomial.X^k.val*(1-Polynomial.X)^(n-k.val)) (hb : ∀ k,0 ≤ b k) :
    ∀ t ∈ Icc (0:ℝ) 1,0 ≤ p.eval t := by
  intro t ht
  rw [hrep,Polynomial.eval_finsetSum]
  apply Finset.sum_nonneg
  intro k hk
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_sub,Polynomial.eval_one]
  exact mul_nonneg (mul_nonneg (mul_nonneg (hb k) (Nat.cast_nonneg _)) (pow_nonneg ht.1 _))
    (pow_nonneg (sub_nonneg.mpr ht.2) _)

theorem atom_density_cap (g : ℝ[X]) (r c : ℝ) (hr : 0 < r)
    (hc : 0 ≤ c ∧ c ≤ Real.pi*r) (hg : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ g.eval x)
    (hp : ∀ x ∈ Icc (-1:ℝ) 1,(1-x^2)*(g.eval x)^2 ≤ c^2) :
    ∀ x ∈ Icc (-1:ℝ) 1,Real.sqrt (1-x^2)*g.eval x/(Real.pi*r) ≤ 1 := by
  intro x hx
  have hs : 0 ≤ 1-x^2 := by nlinarith [hx.1,hx.2]
  have hsq := Real.sq_sqrt hs
  have hproduct : 0 ≤ Real.sqrt (1-x^2)*g.eval x := mul_nonneg (Real.sqrt_nonneg _) (hg x hx)
  have hbound : Real.sqrt (1-x^2)*g.eval x ≤ c := by
    have hh : (Real.sqrt (1-x^2)*g.eval x)^2 ≤ c^2 := by
      rw [mul_pow,hsq]
      exact hp x hx
    nlinarith
  exact (div_le_one (mul_pos Real.pi_pos hr)).mpr (hbound.trans hc.2)

def scalarUpperCheck (e : SE) (q : ℚ) : Bool :=
  match e.check with | none => false | some b => decide (b.2 ≤ q)

def scalarLowerCheck (q : ℚ) (e : SE) : Bool :=
  match e.check with | none => false | some b => decide (q ≤ b.1)

theorem scalarUpperCheck_sound (e : SE) (q : ℚ) (hc : scalarUpperCheck e q=true) : e.value ≤ (q:ℝ) := by
  unfold scalarUpperCheck at hc
  cases he : e.check with
  | none => simp [he] at hc
  | some b =>
    have hb : b.2 ≤ q := of_decide_eq_true (by simpa only [he] using hc)
    exact (scalarCheck_sound e b he).2.trans (by exact_mod_cast hb)

theorem scalarLowerCheck_sound (q : ℚ) (e : SE) (hc : scalarLowerCheck q e=true) : (q:ℝ) ≤ e.value := by
  unfold scalarLowerCheck at hc
  cases he : e.check with
  | none => simp [he] at hc
  | some b =>
    have hb : q ≤ b.1 := of_decide_eq_true (by simpa only [he] using hc)
    exact (show (q:ℝ) ≤ (b.1:ℝ) by exact_mod_cast hb).trans (scalarCheck_sound e b he).1

structure SegmentDatum where
  segments : List QSegment
  dual : CatalanCore.Li2.Uniform.DualDatum
  measure_eq : dual.σ=(segments.map QSegment.measure).sum
  radius : ℚ
structure DensityWitness where
  trees : List BernsteinTree

def sourceDataCheck (segments : List QSegment) (radius : ℚ) (w : DensityWitness) : Bool :=
  decide (0 ≤ radius ∧ segments.length=w.trees.length ∧ (segments.map (fun s => s.c 0)).sum=2) &&
    ((List.range segments.length).all (fun j => match segments[j]?,w.trees[j]? with
      | some s,some t => decide (cqSq s.half ≠ 0 ∧ 0 < s.coeff.length ∧
          cqSq (cqAdd s.mid s.half) ≤ radius^2 ∧ cqSq (cqSub s.mid s.half) ≤ radius^2) && bernCheck s.density (-1) 1 t
      | _,_ => false))

def datumCheck (d : SegmentDatum) (w : DensityWitness) : Bool := sourceDataCheck d.segments d.radius w

structure AtomCapWitness where
  g : ℚ[X]
  positive : BernsteinTree
  cap : BernsteinTree
  c : ℚ
  terms : ℕ

def atomCapCheck (s : QSegment) (w : AtomCapWitness) : Bool :=
  decide (s.mid.2=0 ∧ s.half.2=0 ∧ s.half.1 ≠ 0 ∧ 0 ≤ w.c ∧ s.density=(1-Polynomial.X^2)*w.g) &&
    bernCheck w.g (-1) 1 w.positive &&
    bernCheck (Polynomial.C (w.c^2)-(1-Polynomial.X^2)*w.g^2) (-1) 1 w.cap &&
    scalarLowerCheck w.c (seScale |s.half.1| .pi)

#print axioms dens_pos_bernstein
#print axioms atom_density_cap
#print axioms scalarUpperCheck_sound
#print axioms scalarLowerCheck_sound

#print axioms bernCheck_sound
end

end CatalanCore.Li2.DecayCert
