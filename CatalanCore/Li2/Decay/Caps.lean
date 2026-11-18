module
public import CatalanCore.Li2.Decay.Kernel
public import CatalanCore.Li2.Decay.Tail
public import CatalanCore.Tools.CappedDual
public import CatalanCore.Tools.RiemannSampling
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators Polynomial
namespace CatalanCore.Li2.Decay
open CatalanCore.Tools.Jets
attribute [local instance] Classical.propDecidable
inductive Particle
  | lattice : ℕ → Particle
  | contour : ℂ → Particle
  | ray : ℝ → Particle
  | atom : ℕ → Particle
noncomputable def Particle.point : Particle → ℂ
  | .lattice x => (x:ℂ)
  | .contour u => u
  | .ray x => (x:ℂ)
  | .atom j => -(j:ℂ)
def isLattice : Particle → Bool | .lattice _ => true | _ => false
def isAtom : Particle → Bool | .atom _ => true | _ => false
structure AdmissibleConfig (F : CatalanCore.Li2.Uniform.DualFrame) (g : CatalanCore.Li2.Uniform.FrameGeometry F) (z : ℝ) (n : ℕ) where
  particle : Fin (2*n) → Particle
  lattice_sites : ∀ i x, particle i=.lattice x →
    1 ≤ x ∧ ((x:ℝ)/(n:ℝ) ∈ F.lattice)
  contour_points : ∀ i u, particle i=.contour u → u ∈ CatalanCore.Li2.Uniform.gammaN g n
  ray_points : ∀ i x, particle i=.ray x →
    0 < z ∧ ∃ c : ℝ, CatalanCore.Li2.Uniform.frameCut g=some c ∧ (Nat.floor (c*n):ℝ)+1/2 ≤ x
  atom_sites : ∀ i j, particle i=.atom j → j ∈ Finset.Icc (n+1) (4*n)
  atom_cap : ∀ j : ℕ, (Finset.univ.filter (fun i => particle i=.atom j)).card ≤ 1
  confluence : ConfluentConfig (2*n)
  positions : ∀ i, confluence.x i=(particle i).point/(n:ℂ)
  paired_lattice : ∀ i j, confluence.paired i j →
    ∃ x, particle i=.lattice x ∧ particle j=.lattice x

def AdmissibleConfig.Jlat {F g z n} (c : AdmissibleConfig F g z n) : Finset (Fin (2*n)) :=
  Finset.univ.filter (fun i => isLattice (c.particle i))
noncomputable def configWeight {F g} (z : ℝ) (n : ℕ) (t : ℝ)
    (c : AdmissibleConfig F g z n) : ℂ :=
  mixedJet c.Jlat
    (fun i => match c.particle i with | .lattice x => latticeA z n x | _ => 0)
    (fun i => match c.particle i with | .lattice x => latticeB z n x | _ => 0)
    (fun i => (c.particle i).point) (vandSq (2*n)) *
    ∏ i : Fin (2*n), match c.particle i with
      | .lattice _ => 1
      | .contour u => contourDensity z n 1 u
      | .ray x => rayDensity z n x
      | .atom j => (t*atomWeight z n j:ℂ)
noncomputable def tailEnvelope {F g} (z : ℝ) (d : CatalanCore.Li2.Uniform.DualDatum) (θ : ℝ)
    (K n : ℕ) (c : AdmissibleConfig F g z n) : ℝ :=
  ∏ i : Fin (2*n), if isAtom (c.particle i) then 1 else
    (1+‖(c.particle i).point/(n:ℂ)‖)^K *
      Real.exp (W z d.σ ((c.particle i).point/(n:ℂ))-θ)

theorem occupancy_pos_le {S J : Type*} [Fintype S] [Fintype J]
    [DecidableEq S] (site : J → S) (cap : S → ℕ) (f : S → ℝ)
    (hc : ∀ s, (Finset.univ.filter (fun j => site j=s)).card ≤ cap s) :
    (∑ j, pos (f (site j))) ≤ ∑ s, (cap s:ℝ)*pos (f s) := by
  exact CatalanCore.Tools.CappedDual.occupancy_le site cap (fun s => pos (f s))
    (fun s => le_max_right _ _) hc
theorem continuous_phi0_neg : Continuous (fun x : ℝ => phi0 (-(x:ℂ))) := by
  simp_rw [phi0_negative_formula]
  have h1 := Real.continuous_mul_log
  have h2 := Real.continuous_mul_log.comp (continuous_id.sub continuous_const : Continuous (fun x : ℝ => x-1))
  have h4 := Real.continuous_mul_log.comp (continuous_const.sub continuous_id : Continuous (fun x : ℝ => 4-x))
  convert (((h1.const_mul 2).sub (h2.const_mul 3)).sub h4).add_const 1 using 1
  funext x
  dsimp only [Function.comp_apply,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,id_eq]
  ring

theorem continuous_W_real (z : ℝ) (d : DualDatum) : Continuous (fun x : ℝ => W z d.σ (x:ℂ)) := by
  have hphi : Continuous (fun x : ℝ => phi0 (x:ℂ)) := by
    convert continuous_phi0_neg.comp continuous_neg using 1
    funext x
    simp only [Function.comp_apply,Complex.ofReal_neg,neg_neg]
  have hU : U d.σ=CatalanCore.Li2.Uniform.pot d.σ := by
    funext s
    simp only [U,P,CatalanCore.Li2.Uniform.pot,integral_neg]
  simp only [W,V,Complex.ofReal_re,Complex.ofReal_im,abs_zero,mul_zero,sub_zero,hU]
  exact (hphi.add (continuous_const.mul continuous_id)).sub
    (continuous_const.mul ((CatalanCore.Li2.Uniform.datum_continuous_pot d).comp Complex.continuous_ofReal))

theorem continuous_A_real (z ρ : ℝ) (d : DualDatum) : Continuous (A z ρ d.σ) := by
  have hU : U d.σ=CatalanCore.Li2.Uniform.pot d.σ := by
    funext s
    simp only [U,P,CatalanCore.Li2.Uniform.pot,integral_neg]
  unfold A omega
  rw [hU]
  exact (((continuous_phi0_neg.sub (continuous_id.mul continuous_const)).sub continuous_const).sub
    (continuous_const.mul ((CatalanCore.Li2.Uniform.datum_continuous_pot d).comp
      (continuous_neg.comp Complex.continuous_ofReal))))

theorem lattice_pos_compact (z : ℝ) (hz : ValidZ z) (d : DualDatum) (θ : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R < x → pos (W z d.σ (x:ℂ)-θ)=0 := by
  obtain ⟨M,a,hM,ha,hbound⟩ := field_envelope z hz d θ 0
  let R := max 1 ((Real.log M+1)/a)
  have hR1 : 1 ≤ R := le_max_left _ _
  refine ⟨R,by linarith,?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hnorm : ‖(x:ℂ)‖=x := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx0]
  have hh := hbound (x:ℂ) (by simpa only [Complex.ofReal_re] using hx0)
  simp only [pow_zero,mul_one,hnorm] at hh
  have hlin : Real.log M+1 ≤ R*a := (div_le_iff₀ ha).mp (le_max_right _ _)
  have hax : Real.log M < a*x := by nlinarith
  have he : M*Real.exp (-a*x)=Real.exp (Real.log M-a*x) := by
    rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hM]
    congr 1
    ring
  have he1 : M*Real.exp (-a*x) < 1 := by
    rw [he]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hw : W z d.σ (x:ℂ)-θ < 0 := Real.exp_lt_one_iff.mp (hh.trans_lt he1)
  exact max_eq_right hw.le

theorem atom_riemann (z ρ : ℝ) (hz : ValidZ z) (d : DualDatum) (θ : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)⁻¹ *
      ∑ j ∈ Finset.Icc (n+1) (4*n), pos (A z ρ d.σ ((j:ℝ)/n)-θ))
      atTop (nhds (atomPenalty z ρ d.σ θ)) := by
  have hf : Continuous (fun x : ℝ => pos (A z ρ d.σ x-θ)) :=
    ((continuous_A_real z ρ d).sub continuous_const).max continuous_const
  have ht := CatalanCore.Tools.RiemannSampling.interval_right_sum_limit
    (fun x : ℝ => pos (A z ρ d.σ x-θ)) hf 1 4 (by norm_num) (by norm_num)
  have hfour (n : ℕ) : Nat.floor ((4:ℝ)*(n:ℝ))=4*n := by
    have he : (4:ℝ)*(n:ℝ)=((4*n:ℕ):ℝ) := by push_cast; ring
    rw [he,Nat.floor_natCast]
  simp only [hfour] at ht
  simpa only [one_mul,Nat.floor_natCast,smul_eq_mul,atomPenalty] using ht

theorem lattice_riemann (z : ℝ) (hz : ValidZ z) (F : Frame)
    (g : CatalanCore.Li2.Uniform.FrameGeometry F) (d : DualDatum) (θ : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)⁻¹ *
      ∑' x : ℕ, if ((x+1:ℕ):ℝ)/n ∈ lat F
        then pos (W z d.σ (((x+1:ℕ):ℂ)/n)-θ) else 0)
      atTop (nhds (latPenalty z F d.σ θ)) := by
  let f : ℝ → ℝ := fun x => pos (W z d.σ (x:ℂ)-θ)
  have hf : Continuous f := ((continuous_W_real z d).sub continuous_const).max continuous_const
  rcases F.lattice_kind with hlat | ⟨c,hc,hlat⟩
  · obtain ⟨R,hR,hzero⟩ := lattice_pos_compact z hz d θ
    have ht := CatalanCore.Tools.RiemannSampling.compact_right_tsum_limit f hf R hR hzero
    change Tendsto _ _ (nhds (∫ x in F.lattice, f x))
    rw [hlat]
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    dsimp only [f]
    congr 1
    apply tsum_congr
    intro x
    have hmem : ((x+1:ℕ):ℝ)/n ∈ lat F := by
      change _ ∈ F.lattice
      rw [hlat]
      change 0 ≤ ((x+1:ℕ):ℝ)/n
      positivity
    rw [if_pos hmem]
    simp only [Complex.ofReal_div,Complex.ofReal_natCast]
  · have ht := CatalanCore.Tools.RiemannSampling.cut_right_tsum_limit f hf c hc
    change Tendsto _ _ (nhds (∫ x in F.lattice, f x))
    rw [hlat]
    apply ht.congr'
    apply Filter.Eventually.of_forall
    intro n
    dsimp only [f]
    congr 1
    apply tsum_congr
    intro x
    change (if _ ∈ Icc (0:ℝ) c then _ else _) = _
    change _ = (if _ ∈ F.lattice then _ else _)
    rw [hlat]
    split_ifs <;> simp only [Complex.ofReal_div,Complex.ofReal_natCast]
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.occupancy_pos_le
#print axioms CatalanCore.Li2.Decay.atom_riemann
#print axioms CatalanCore.Li2.Decay.lattice_riemann
