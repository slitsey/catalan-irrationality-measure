module
public import CatalanCore.Uniform.Measure.NV0
public import CatalanCore.NT.Interval
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.FieldSimp
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.NormCast
@[expose] public section
set_option maxHeartbeats 1200000
set_option Elab.async false
open Filter Asymptotics
open scoped BigOperators
namespace CatalanCore.Measure
noncomputable section
structure BandNV (Fam : PolyFamily) (mem : ℕ→Fam.ι) (α β : ℝ) where
  bad : Finset ℕ
  res : ℕ→Finset ℕ
  res_card : ∀ ℓ, (res ℓ).card≤3
  n0 : ℕ
  nv : ∀ ℓ n : ℕ, ℓ.Prime → ℓ∉bad → n0≤n →
    α*((n:ℝ)+1)<ℓ → (ℓ:ℝ)<β*n → n%ℓ∉res ℓ →
    ∀ (p : ℤ) (q : ℕ), 0<q → ¬ℓ^2∣q →
      Fam.evalQ (mem n) ((p:ℚ)/q)≠0 ∨ Fam.evalQ (mem (n+1)) ((p:ℚ)/q)≠0
def Good {Fam : PolyFamily} {mem : ℕ→Fam.ι} {α β : ℝ}
    (B : BandNV Fam mem α β) (n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ ℓ∈S, ℓ.Prime ∧ ℓ∉B.bad ∧ B.n0≤n ∧ α*((n:ℝ)+1)<ℓ ∧ (ℓ:ℝ)<β*n ∧ n%ℓ∉B.res ℓ

theorem band_pair_zero_dvd {Fam : PolyFamily} {mem : ℕ→Fam.ι} {α β : ℝ}
    (B : BandNV Fam mem α β) (n : ℕ) (S : Finset ℕ) (hS : Good B n S)
    (p : ℤ) (q : ℕ) (hq : 0<q)
    (h0 : Fam.evalQ (mem n) ((p:ℚ)/q)=0)
    (h1 : Fam.evalQ (mem (n+1)) ((p:ℚ)/q)=0) : (∏ ℓ∈S, ℓ^2)∣q := by
  classical
  apply Finset.prod_dvd_of_isRelPrime
  · intro ℓ hℓ m hm hne
    exact Nat.coprime_iff_isRelPrime.mp (Nat.coprime_pow_primes 2 2 (hS ℓ hℓ).1 (hS m hm).1 hne)
  · intro ℓ hℓ
    by_contra hno
    obtain ⟨hp,hbad,hn,ha,hb,hr⟩:=hS ℓ hℓ
    exact (B.nv ℓ n hp hbad hn ha hb hr p q hq hno).elim (fun h=>h h0) (fun h=>h h1)
private theorem count_window_modEq (N H ℓ r : ℕ) (hℓ:0<ℓ) :
    (((Finset.Ico N (N+H)).filter (fun n => n≡r [MOD ℓ])).card:ℚ)≤(H:ℚ)/ℓ+1 := by
  have hc:=Nat.Ico_filter_modEq_card (a:=N) (b:=N+H) hℓ r
  have ha:=Int.le_ceil (((N:ℚ)-r)/ℓ)
  have hb:=Int.ceil_lt_add_one (((((N+H:ℕ):ℚ)-r)/(ℓ:ℚ)))
  have he : (((Finset.Ico N (N+H)).filter (fun n => n≡r [MOD ℓ])).card:ℚ)=
      ((max (⌈(((N+H:ℕ):ℚ)-r)/(ℓ:ℚ)⌉-⌈((N:ℚ)-r)/(ℓ:ℚ)⌉) 0:ℤ):ℚ) := by exact_mod_cast hc
  rw [he,Int.cast_max,Int.cast_sub,Int.cast_zero]
  apply max_le
  · have hid : ((((N+H:ℕ):ℚ)-r)/(ℓ:ℚ))-(((N:ℚ)-r)/(ℓ:ℚ))=(H:ℚ)/ℓ := by push_cast;ring
    linarith
  · positivity

private theorem count_window_res (N H ℓ : ℕ) (R : Finset ℕ)
    (hℓ:0<ℓ) (hR:R.card≤3) :
    (((Finset.Ico N (N+H)).filter (fun n => n%ℓ∈R)).card:ℚ)≤3*((H:ℚ)/ℓ+1) := by
  classical
  let J:=Finset.Ico N (N+H)
  have hsub : J.filter (fun n=>n%ℓ∈R) ⊆ R.biUnion (fun r=>J.filter (fun n=>n≡r [MOD ℓ])) := by
    intro n hn
    obtain ⟨hnJ,hnR⟩:=Finset.mem_filter.mp hn
    apply Finset.mem_biUnion.mpr
    refine ⟨n%ℓ,hnR,Finset.mem_filter.mpr ⟨hnJ,?_⟩⟩
    simp [Nat.ModEq]
  have hn:= (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  calc
    _ ≤ ∑ r∈R, ((J.filter (fun n=>n≡r [MOD ℓ])).card:ℚ) := by exact_mod_cast hn
    _ ≤ ∑ r∈R, ((H:ℚ)/ℓ+1) := Finset.sum_le_sum (fun r hr=> count_window_modEq N H ℓ r hℓ)
    _ = (R.card:ℚ)*((H:ℚ)/ℓ+1) := by simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hR) (by positivity)

noncomputable def lost (res : ℕ→Finset ℕ) (n X : ℕ) : ℝ :=
  ∑ ℓ∈(Finset.Icc 1 X).filter (fun ℓ=>ℓ.Prime ∧ n%ℓ∈res ℓ),Real.log ℓ

theorem exists_small_lost_mass (res : ℕ→Finset ℕ) (hres : ∀ ℓ,(res ℓ).card≤3)
    (N H X : ℕ) (hH:1≤H) (hX:1≤X) :
    ∃ n∈Finset.Ico N (N+H), lost res n X ≤
      3*Real.log X*(1+Real.log X)+3*(X:ℝ)*Real.log 4/H := by
  classical
  let J:=Finset.Ico N (N+H)
  let P:=(Finset.Icc 1 X).filter Nat.Prime
  have hlogX:0≤Real.log X:=Real.log_nonneg (by exact_mod_cast hX)
  have hp (ℓ : ℕ) (h:ℓ∈P) : ℓ.Prime ∧ 1≤ℓ ∧ ℓ≤X := by
    obtain ⟨hI,hp⟩:=Finset.mem_filter.mp h
    exact ⟨hp,(Finset.mem_Icc.mp hI).1,(Finset.mem_Icc.mp hI).2⟩
  have heq (n : ℕ) : lost res n X=∑ ℓ∈P,if n%ℓ∈res ℓ then Real.log ℓ else 0 := by
    simp only [lost,P,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    split_ifs <;> simp_all
  have hcount (ℓ : ℕ) (hℓ:ℓ∈P) :
      (((J.filter (fun n=>n%ℓ∈res ℓ)).card):ℝ)≤3*((H:ℝ)/ℓ+1) := by
    have hv:=count_window_res N H ℓ (res ℓ) (hp ℓ hℓ).1.pos (hres ℓ)
    have hr := (Rat.cast_le (K:=ℝ)).mpr hv
    simpa only [J,Rat.cast_natCast,Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using hr
  have hsum : (∑ n∈J,lost res n X)=
      ∑ ℓ∈P,((J.filter (fun n=>n%ℓ∈res ℓ)).card:ℝ)*Real.log ℓ := by
    simp_rw [heq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [← Finset.sum_filter]
    simp
  have hlog : (∑ ℓ∈P,Real.log ℓ)≤Real.log 4*X := by
    have he : (∑ ℓ∈P,Real.log ℓ)=Chebyshev.theta (X:ℝ) := by
      unfold Chebyshev.theta
      rw [Nat.floor_natCast]
      congr 1 <;> (ext ℓ; simp only [P,Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]; omega)
    rw [he]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hhar : (∑ ℓ∈P,(ℓ:ℝ)⁻¹)≤1+Real.log X := by
    calc
      _ ≤ ∑ ℓ∈Finset.Icc 1 X,(ℓ:ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro ℓ hℓ hn
        positivity
      _ = (harmonic X:ℝ) := by simp [harmonic_eq_sum_Icc]
      _ ≤ _ := harmonic_le_one_add_log X
  have hw : (∑ ℓ∈P,Real.log ℓ/(ℓ:ℝ))≤Real.log X*(1+Real.log X) := by
    calc
      _ ≤ ∑ ℓ∈P,Real.log X*(ℓ:ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact Real.log_le_log (by exact_mod_cast (hp ℓ hℓ).1.pos) (by exact_mod_cast (hp ℓ hℓ).2.2)
      _ = Real.log X*(∑ ℓ∈P,(ℓ:ℝ)⁻¹) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hhar hlogX
  have htotal : (∑ n∈J,lost res n X)≤
      3*(H:ℝ)*(Real.log X*(1+Real.log X))+3*(Real.log 4*X) := by
    rw [hsum]
    calc
      _ ≤ ∑ ℓ∈P,3*((H:ℝ)/ℓ+1)*Real.log ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        exact mul_le_mul_of_nonneg_right (hcount ℓ hℓ)
          (Real.log_nonneg (by exact_mod_cast (hp ℓ hℓ).2.1))
      _ = 3*(H:ℝ)*(∑ ℓ∈P,Real.log ℓ/(ℓ:ℝ))+3*(∑ ℓ∈P,Real.log ℓ) := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hw (by positivity))
        (mul_le_mul_of_nonneg_left hlog (by norm_num))
  let B:ℝ:=3*Real.log X*(1+Real.log X)+3*(X:ℝ)*Real.log 4/H
  by_contra hn
  push_neg at hn
  have hJ : N∈J := by simp [J];omega
  have hlt : (∑ n∈J,B)<∑ n∈J,lost res n X :=
    Finset.sum_lt_sum (fun n hnJ=>(hn n hnJ).le) ⟨N,hJ,hn N hJ⟩
  have hpos : (0:ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have hc : (∑ n∈J,B)=(H:ℝ)*B := by simp [J]
  rw [hc] at hlt
  have hd : (H:ℝ)*B=3*(H:ℝ)*(Real.log X*(1+Real.log X))+3*(Real.log 4*X) := by
    dsimp only [B]
    field_simp [hpos.ne']
    <;> ring
  rw [hd] at hlt
  exact (not_lt_of_ge htotal) hlt

theorem band_mass (α β : ℝ) (hα : 0<α) (hαβ : α<β)
    (bad : Finset ℕ) (ε : ℝ) (hε : 0<ε) :
  ∀ᶠ n : ℕ in atTop,
    (β-α-ε)*n ≤ ∑ ℓ∈(Finset.range (⌈β*n⌉₊+1)).filter
      (fun ℓ => ℓ.Prime ∧ ℓ∉bad ∧ α*((n:ℝ)+1)<ℓ ∧ (ℓ:ℝ)<β*n), Real.log ℓ := by
  classical
  let δ:=min ((β-α)/4) (ε/8)
  have hδ : 0<δ:=lt_min (by linarith) (by linarith)
  have hδa : δ≤(β-α)/4:=min_le_left _ _
  have hδe : δ≤ε/8:=min_le_right _ _
  have ha : 0<α+δ:=by linarith
  have hab : α+δ≤β-δ:=by linarith
  have hβ : 0<β-δ:=lt_of_lt_of_le ha hab
  have hu : IsUnit (0:ZMod 1) := by
    convert (isUnit_one : IsUnit (1:ZMod 1)) using 1
    exact Subsingleton.elim _ _
  have ht:=NT.theta_interval_abs_le (m:=1) (r:=0) hu ha hab hδ
  have htN : ∀ᶠ n : ℕ in atTop,
      |NT.thetaClass 1 0 ((β-δ)*(n:ℝ))-NT.thetaClass 1 0 ((α+δ)*(n:ℝ))-
        (β-α-2*δ)*n|≤δ*n := by
    have h:=(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually ht
    filter_upwards [h] with n hn
    simpa only [Nat.totient_one,Nat.cast_one,div_one,show β-δ-(α+δ)=β-α-2*δ by ring] using hn
  let B:=∑ ℓ∈bad,Real.log ℓ
  obtain ⟨M,hM⟩:=exists_nat_gt (max (α/δ) (B/δ)+1)
  filter_upwards [htN,eventually_ge_atTop M,eventually_ge_atTop 1] with n hn hnM hn1
  have hnR : (1:ℝ)≤n:=by exact_mod_cast hn1
  have hMR : (M:ℝ)≤n:=by exact_mod_cast hnM
  have halpha : α<δ*n := by
    have hh:=le_max_left (α/δ) (B/δ)
    have hl : α/δ<(n:ℝ):=by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hl
  have hB : B≤δ*n := by
    have hh:=le_max_right (α/δ) (B/δ)
    have hl : B/δ≤(n:ℝ):=by linarith
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hl
  let L:=⌊(α+δ)*(n:ℝ)⌋₊
  let U:=⌊(β-δ)*(n:ℝ)⌋₊
  let S:=(Finset.Ioc L U).filter Nat.Prime
  let O:=(Finset.range (⌈β*(n:ℝ)⌉₊+1)).filter
    (fun ℓ=>ℓ.Prime ∧ ℓ∉bad ∧ α*((n:ℝ)+1)<ℓ ∧ (ℓ:ℝ)<β*n)
  have hLU : L≤U:=Nat.floor_mono (mul_le_mul_of_nonneg_right hab (by positivity))
  have hs : (∑ ℓ∈S,Real.log ℓ)=
      NT.thetaClass 1 0 ((β-δ)*(n:ℝ))-NT.thetaClass 1 0 ((α+δ)*(n:ℝ)) := by
    have hh:=NT.thetaClassN_sub 1 (0:ZMod 1) hLU
    have hmod : ∀ ℓ : ℕ,(ℓ:ZMod 1)=0:=fun _=>Subsingleton.elim _ _
    simpa [NT.thetaClass,S,L,U,hmod] using hh.symm
  have hinner : (β-α-3*δ)*n≤∑ ℓ∈S,Real.log ℓ := by
    rw [hs]
    linarith [(abs_le.mp hn).1]
  have hsubset : S.filter (fun ℓ=>ℓ∉bad) ⊆ O := by
    intro ℓ hℓ
    obtain ⟨hℓS,hbad⟩:=Finset.mem_filter.mp hℓ
    obtain ⟨hI,hprime⟩:=Finset.mem_filter.mp hℓS
    obtain ⟨hL,hU⟩:=Finset.mem_Ioc.mp hI
    have hl : (α+δ)*(n:ℝ)<ℓ := (Nat.floor_lt (by positivity)).mp hL
    have hr : (ℓ:ℝ)≤(β-δ)*n := (Nat.le_floor_iff (by positivity)).mp hU
    have hlo : α*((n:ℝ)+1)<ℓ := by nlinarith
    have hup : (ℓ:ℝ)<β*n := by nlinarith
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,hprime,hbad,hlo,hup⟩
    have hceil : (ℓ:ℝ)≤((⌈β*(n:ℝ)⌉₊:ℕ):ℝ):=
      hup.le.trans (Nat.le_ceil _)
    have hc : ℓ≤⌈β*(n:ℝ)⌉₊:=by exact_mod_cast hceil
    omega
  have hbadmass : (∑ ℓ∈S.filter (fun ℓ=>ℓ∈bad),Real.log ℓ)≤B := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ
      exact (Finset.mem_filter.mp hℓ).2
    · intro ℓ hℓ hn
      exact Real.log_natCast_nonneg ℓ
  have hpart:=Finset.sum_filter_add_sum_filter_not S (fun ℓ=>ℓ∈bad) (fun ℓ=>Real.log ℓ)
  have hout : (∑ ℓ∈S.filter (fun ℓ=>ℓ∉bad),Real.log ℓ)≤∑ ℓ∈O,Real.log ℓ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro ℓ hℓ hn
    exact Real.log_natCast_nonneg ℓ
  change (β-α-ε)*n≤∑ ℓ∈O,Real.log ℓ
  nlinarith
/-- The logarithmic loss is negligible in a linearly sized window. -/
private theorem logloss_eventually (C K η : ℝ) (hC : 0<C) (hη : 0<η) :
    ∀ᶠ N : ℕ in Filter.atTop,
      3*Real.log (C*N)*(1+Real.log (C*N))+K ≤ η*N := by
  have hconst : (fun _ : ℝ => 3*Real.log C*(1+Real.log C)+K) =o[Filter.atTop] id :=
    Real.isLittleO_const_log_atTop.trans Real.isLittleO_log_id_atTop
  have hlin := Real.isLittleO_log_id_atTop.const_mul_left (3+6*Real.log C)
  have hsq := (Real.isLittleO_pow_log_id_atTop (n:=2)).const_mul_left 3
  have hbound := ((hconst.add hlin).add hsq).def hη
  have hn := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hbound
  filter_upwards [hn,Filter.eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have he : 3*Real.log (C*N)*(1+Real.log (C*N))+K =
      (3*Real.log C*(1+Real.log C)+K)+(3+6*Real.log C)*Real.log N+3*Real.log N^2 := by
    rw [Real.log_mul hC.ne' hNpos.ne'];ring
  rw [he]
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs,abs_of_pos hNpos] using hN)
/-- BC04 from the proved prime-band mass statement, isolated from its heavy PNT import. -/
theorem band_pair_mass_of_mass {Fam : PolyFamily} {mem : ℕ→Fam.ι} {α β : ℝ}
    (B : BandNV Fam mem α β) (hα : 0<α) (hαβ : α<β)
    (hmass : ∀ η : ℝ,0<η→∀ᶠ n : ℕ in atTop,
      (β-α-η)*n ≤ ∑ ℓ∈(Finset.range (⌈β*n⌉₊+1)).filter
        (fun ℓ=>ℓ.Prime ∧ ℓ∉B.bad ∧ α*((n:ℝ)+1)<ℓ ∧ (ℓ:ℝ)<β*n),Real.log ℓ)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∃ (n : ℕ) (S : Finset ℕ),
      N≤n ∧ (n:ℝ)≤(1+ε)*N ∧ Good B n S ∧
        (2*(β-α)-ε)*n≤∑ ℓ∈S,2*Real.log ℓ := by
  classical
  let δ:=ε/2
  have hδ : 0<δ:=by dsimp [δ];positivity
  have hβ : 0<β:=lt_trans hα hαβ
  let C:=β*(2+δ)+2
  have hC : 0<C:=by dsimp [C];positivity
  let K:=3*C*Real.log 4/δ
  obtain ⟨M,hM⟩:=Filter.eventually_atTop.mp (hmass (ε/8) (by positivity))
  have hg:=logloss_eventually C K (ε/8) hC (by positivity)
  obtain ⟨A,hA⟩:=exists_nat_gt (2/ε)
  filter_upwards [hg,eventually_ge_atTop M,eventually_ge_atTop B.n0,
    eventually_ge_atTop A,eventually_ge_atTop 1] with N hNg hNM hN0 hNA hN1
  let H:=⌈δ*(N:ℝ)⌉₊
  let X:=⌈β*((N+H:ℕ):ℝ)⌉₊+1
  have hNR : (1:ℝ)≤N:=by exact_mod_cast hN1
  have hNp : (0:ℝ)<N:=by linarith
  have hHlo : δ*N≤(H:ℝ):=Nat.le_ceil _
  have hHhi : (H:ℝ)<δ*N+1:=Nat.ceil_lt_add_one (by positivity)
  have hHp : (0:ℝ)<H:=lt_of_lt_of_le (mul_pos hδ hNp) hHlo
  have hH : 1≤H:=by exact_mod_cast (show (0:ℝ)<H from hHp)
  have hX : 1≤X:=by dsimp [X];omega
  have hXhi : (X:ℝ)≤C*N := by
    have hc:=Nat.ceil_lt_add_one (show 0≤β*((N+H:ℕ):ℝ) by positivity)
    have hcast : (X:ℝ)=(⌈β*((N+H:ℕ):ℝ)⌉₊:ℝ)+1:=by simp [X]
    dsimp [C]
    push_cast at hc hcast
    have hbH:=mul_le_mul_of_nonneg_left hHhi.le hβ.le
    have hbN:=mul_le_mul_of_nonneg_left hNR (show 0≤β+2 by positivity)
    nlinarith only [hc,hcast,hbH,hbN]
  have hfrac : 3*(X:ℝ)*Real.log 4/H≤K := by
    dsimp [K]
    apply (div_le_div_iff₀ hHp hδ).mpr
    have hlog : 0≤Real.log 4:=Real.log_nonneg (by norm_num)
    have hx:=mul_le_mul_of_nonneg_right hXhi (show 0≤3*Real.log 4*δ by positivity)
    have hh:=mul_le_mul_of_nonneg_left hHlo (show 0≤3*C*Real.log 4 by positivity)
    nlinarith only [hx,hh]
  obtain ⟨n,hn,hlost⟩:=exists_small_lost_mass B.res B.res_card N H X hH hX
  obtain ⟨hnlo,hnhi⟩:=Finset.mem_Ico.mp hn
  have hnR : (N:ℝ)≤n:=by exact_mod_cast hnlo
  have hnHR : (n:ℝ)<N+H:=by exact_mod_cast hnhi
  have hna : (n:ℝ)≤(1+ε)*N := by
    have hAR : (A:ℝ)≤N:=by exact_mod_cast hNA
    have hh : 2/ε<(N:ℝ):=lt_of_lt_of_le hA hAR
    have hlarge : (2:ℝ)<ε*N:=by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hh
    dsimp [δ] at hHhi
    nlinarith
  have hlogs : Real.log X≤Real.log (C*N) :=
    Real.log_le_log (by exact_mod_cast hX) hXhi
  have hlogX : 0≤Real.log X:=Real.log_nonneg (by exact_mod_cast hX)
  have hl : lost B.res n X≤(ε/8)*n := by
    have hc : 3*Real.log X*(1+Real.log X)≤3*Real.log (C*N)*(1+Real.log (C*N)):=by nlinarith
    have hη : (ε/8)*N≤(ε/8)*n:=mul_le_mul_of_nonneg_left hnR (by positivity)
    linarith
  let P:=(Finset.range (⌈β*(n:ℝ)⌉₊+1)).filter
    (fun ℓ=>ℓ.Prime ∧ ℓ∉B.bad ∧ α*((n:ℝ)+1)<ℓ ∧ (ℓ:ℝ)<β*n)
  let S:=P.filter (fun ℓ=>n%ℓ∉B.res ℓ)
  have hgood : Good B n S := by
    intro ℓ hℓ
    obtain ⟨hP,hres⟩:=Finset.mem_filter.mp hℓ
    obtain ⟨hr,hprime,hbad,hlo,hhi⟩:=Finset.mem_filter.mp hP
    exact ⟨hprime,hbad,le_trans hN0 hnlo,hlo,hhi,hres⟩
  have hbad : (∑ ℓ∈P.filter (fun ℓ=>n%ℓ∈B.res ℓ),Real.log ℓ)≤lost B.res n X := by
    unfold lost
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ
      obtain ⟨hP,hres⟩:=Finset.mem_filter.mp hℓ
      obtain ⟨hr,hprime,hbad,hlo,hhi⟩:=Finset.mem_filter.mp hP
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hprime.one_le,?_⟩,hprime,hres⟩
      have hℓ : (ℓ:ℝ)<β*((N+H:ℕ):ℝ):=by push_cast;nlinarith
      have hc : (ℓ:ℝ)≤(⌈β*((N+H:ℕ):ℝ)⌉₊:ℝ):=hℓ.le.trans (Nat.le_ceil _)
      have hh : ℓ≤⌈β*((N+H:ℕ):ℝ)⌉₊:=by exact_mod_cast hc
      dsimp [X];omega
    · intro ℓ hℓ hnℓ
      exact Real.log_natCast_nonneg ℓ
  have hsplit:=Finset.sum_filter_add_sum_filter_not P (fun ℓ=>n%ℓ∈B.res ℓ) (fun ℓ=>Real.log ℓ)
  have hmassn : (β-α-ε/8)*n≤∑ ℓ∈P,Real.log ℓ:=hM n (le_trans hNM hnlo)
  have hSn : (β-α-ε/4)*n≤∑ ℓ∈S,Real.log ℓ:=by dsimp [S];linarith
  refine ⟨n,S,hnlo,hna,hgood,?_⟩
  rw [← Finset.mul_sum]
  nlinarith

/-- BC05: a nearby nonzero member obtained from the prime-square band. -/
theorem measure_of_bandNV_of_pair_mass {Fam : PolyFamily} (mem : ℕ→Fam.ι)
    (scale : Fam.ι→ℕ) (hscale : ∀ n,scale (mem n)=n)
    (hAdm : ∀ᶠ n : ℕ in atTop,Fam.Adm (mem n))
    {Λ D ρ κ μ α β : ℝ}
    (hΛ : Uniform.HasScaledContent Fam scale Λ)
    (hD : Uniform.HasScaledDecay Fam scale D ρ)
    (hη : Λ<D) (hρ : 0<ρ) (hκ : 0<κ) (hαβ : 0<α ∧ α<β)
    (hdeg : ∀ n,(Fam.deg (mem n):ℝ)≤κ*n) (B : BandNV Fam mem α β)
    (hpair : ∀ ε : ℝ,0<ε→∀ᶠ N : ℕ in atTop,∃ (n : ℕ) (S : Finset ℕ),
      N≤n ∧ (n:ℝ)≤(1+ε)*N ∧ Good B n S ∧
        (2*(β-α)-ε)*n≤∑ ℓ∈S,2*Real.log ℓ)
    (hμ : ρ*max (κ/(D-Λ)) (1/(2*(β-α)))<μ) :
    ∀ᶠ q : ℕ in atTop,∀ p : ℤ,(q:ℝ)^(-μ)< |Fam.const-(p:ℝ)/q| := by
  classical
  have hgap : 0<D-Λ:=sub_pos.mpr hη
  have hd : 0<β-α:=sub_pos.mpr hαβ.2
  have hh : max (κ/(D-Λ)) (1/(2*(β-α)))<μ/ρ:=
    (lt_div_iff₀ hρ).mpr (by simpa [mul_comm] using hμ)
  obtain ⟨a,ha0,haμ⟩:=exists_between hh
  have hak : κ/(D-Λ)<a:=lt_of_le_of_lt (le_max_left _ _) ha0
  have had : 1/(2*(β-α))<a:=lt_of_le_of_lt (le_max_right _ _) ha0
  have ha : 0<a:=lt_trans (by positivity) hak
  obtain ⟨b,hab,hbμ⟩:=exists_between haμ
  have hb : 0<b:=lt_trans ha hab
  have hka : κ/a<D-Λ:=by
    apply (div_lt_iff₀ ha).mpr
    have hx:=(div_lt_iff₀ hgap).mp hak
    nlinarith
  obtain ⟨θ,hθk,hθgap⟩:=exists_between hka
  have hθ : 0<θ:=lt_trans (by positivity) hθk
  have hθa : κ<θ*a:=(div_lt_iff₀ ha).mp hθk
  have hρb : ρ*b<μ:=by
    have hx:=(lt_div_iff₀ hρ).mp hbμ
    nlinarith
  let η:=min ((D-Λ-θ)/3) ((μ/b-ρ)/2)
  have hηp : 0<η:=by
    apply lt_min
    · linarith
    · have hx : ρ<μ/b:=(lt_div_iff₀ hb).mpr (by nlinarith)
      linarith
  have hbudget : θ+2*η≤D-Λ:=by
    have hx:=min_le_left ((D-Λ-θ)/3) ((μ/b-ρ)/2)
    change η≤(D-Λ-θ)/3 at hx
    linarith
  have hwin : (ρ+η)*b<μ:=by
    have hx:=min_le_right ((D-Λ-θ)/3) ((μ/b-ρ)/2)
    change η≤(μ/b-ρ)/2 at hx
    have he:=div_mul_cancel₀ μ hb.ne'
    nlinarith
  obtain ⟨R,hsep⟩:=Uniform.scaled_sep Fam scale hΛ hD hηp hbudget
  obtain ⟨A,hA⟩:=Filter.eventually_atTop.mp hAdm
  let ε:=min ((b/a-1)/2) ((2*(β-α)-1/a)/2)
  have hε : 0<ε:=by
    apply lt_min
    · have hx : 1<b/a:=(lt_div_iff₀ ha).mpr (by nlinarith)
      linarith
    · have hx : 1/a<2*(β-α):=by
        apply (div_lt_iff₀ ha).mpr
        have hy:=(div_lt_iff₀ (by positivity : 0<2*(β-α))).mp had
        nlinarith
      linarith
  have habε : (1+ε)*a<b:=by
    have hx:=min_le_left ((b/a-1)/2) ((2*(β-α)-1/a)/2)
    change ε≤(b/a-1)/2 at hx
    have he:=div_mul_cancel₀ b ha.ne'
    nlinarith
  have hmassgap : 1<(2*(β-α)-ε)*a:=by
    have hx:=min_le_right ((b/a-1)/2) ((2*(β-α)-1/a)/2)
    change ε≤(2*(β-α)-1/a)/2 at hx
    have he:=div_mul_cancel₀ (1:ℝ) ha.ne'
    have hy:=(div_lt_iff₀ (by positivity : 0<2*(β-α))).mp had
    nlinarith
  have hmasspos : 0<2*(β-α)-ε:=by nlinarith
  obtain ⟨M,hM⟩:=Filter.eventually_atTop.mp (hpair ε hε)
  let T:=max (max R A) M
  let L0:=max (((T:ℝ)+1)/a) ((2+ε)/(b-(1+ε)*a))
  have ht : Tendsto (fun q : ℕ=>Real.log (q:ℝ)) atTop atTop:=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually (eventually_gt_atTop L0),eventually_ge_atTop 1] with q hL hq1
  intro p
  have hq : 0<q:=by omega
  have hqR : (0:ℝ)<q:=by exact_mod_cast hq
  let L:=Real.log (q:ℝ)
  have hlarge : ((T:ℝ)+1)/a<L:=lt_of_le_of_lt (le_max_left _ _) hL
  have hwide : (2+ε)/(b-(1+ε)*a)<L:=lt_of_le_of_lt (le_max_right _ _) hL
  have hLp : 0<L:=lt_trans (by positivity) hlarge
  let N:=⌈a*L⌉₊
  have hNlo : a*L≤(N:ℝ):=Nat.le_ceil _
  have hNhi : (N:ℝ)<a*L+1:=Nat.ceil_lt_add_one (by positivity)
  have hNT : T≤N:=by
    have hx:=(div_lt_iff₀ ha).mp hlarge
    have hh : (T:ℝ)≤N:=by nlinarith
    exact_mod_cast hh
  obtain ⟨n,S,hn,hnb,hgood,hmass⟩:=hM N ((le_max_right _ _).trans hNT)
  have hnR : (N:ℝ)≤n:=by exact_mod_cast hn
  have hnT : T≤n:=hNT.trans hn
  have hna : a*L≤(n:ℝ):=hNlo.trans hnR
  have hnwide : (n:ℝ)+1≤b*L:=by
    have hx:=(div_lt_iff₀ (sub_pos.mpr habε)).mp hwide
    have hy:=mul_lt_mul_of_pos_left hNhi (show 0<1+ε by linarith)
    nlinarith
  have hp_nonzero : Fam.evalQ (mem n) ((p:ℚ)/q)≠0 ∨
      Fam.evalQ (mem (n+1)) ((p:ℚ)/q)≠0 := by
    by_contra hno
    push_neg at hno
    have hdiv:=band_pair_zero_dvd B n S hgood p q hq hno.1 hno.2
    have hp : 0<∏ ℓ∈S,ℓ^2:=Finset.prod_pos (fun ℓ hℓ=>pow_pos (hgood ℓ hℓ).1.pos _)
    have hle:=Nat.le_of_dvd hq hdiv
    have hlog : Real.log ((∏ ℓ∈S,ℓ^2:ℕ):ℝ)≤L:=
      Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hle)
    have he : Real.log ((∏ ℓ∈S,ℓ^2:ℕ):ℝ)=∑ ℓ∈S,2*Real.log ℓ := by
      rw [Nat.cast_prod,Real.log_prod]
      · apply Finset.sum_congr rfl
        intro ℓ hℓ
        rw [Nat.cast_pow,Real.log_pow]
        norm_num
      · intro ℓ hℓ
        exact_mod_cast (pow_ne_zero 2 (hgood ℓ hℓ).1.ne_zero)
    rw [he] at hlog
    have hx:=mul_le_mul_of_nonneg_left hna hmasspos.le
    have hy:=mul_lt_mul_of_pos_right hmassgap hLp
    nlinarith
  obtain ⟨r,hr,hrwide,hrT,hrnz⟩ : ∃ r : ℕ,a*L≤(r:ℝ) ∧ (r:ℝ)≤b*L ∧ T≤r ∧
      Fam.evalQ (mem r) ((p:ℚ)/q)≠0 := by
    rcases hp_nonzero with h | h
    · exact ⟨n,hna,by linarith,hnT,h⟩
    · exact ⟨n+1,by push_cast;linarith,by simpa using hnwide,by omega,h⟩
  by_contra hclose
  have hclose : |Fam.const-(p:ℝ)/q|≤(q:ℝ)^(-μ):=le_of_not_gt hclose
  have hwinr : |Fam.const-(p:ℝ)/q|≤Real.exp (-(ρ+η)*(r:ℝ)) := by
    apply hclose.trans
    rw [Real.rpow_def_of_pos hqR]
    apply Real.exp_le_exp.mpr
    have hx:=mul_le_mul_of_nonneg_left hrwide (show 0≤ρ+η by linarith)
    have hy:=mul_lt_mul_of_pos_right hwin hLp
    dsimp [L] at hx hy
    nlinarith
  have hAr:=hA r ((le_max_right R A).trans ((le_max_left _ _).trans hrT))
  have hRr : R≤scale (mem r):=by
    rw [hscale]
    exact (le_max_left R A).trans ((le_max_left _ _).trans hrT)
  have hsep' :=hsep (mem r) hAr hRr p (q:ℤ) (by exact_mod_cast hq)
    (by simpa using hrnz) (by simpa [hscale] using hwinr)
  simp only [hscale,Int.cast_natCast] at hsep'
  have hdeg':=hdeg r
  have hup:=hsep'.trans (mul_le_mul_of_nonneg_right hdeg' hLp.le)
  have hrp : (0:ℝ)<r:=lt_of_lt_of_le (mul_pos ha hLp) hr
  have hθr : κ*L<θ*(r:ℝ):=by
    have hx:=mul_le_mul_of_nonneg_left hr hθ.le
    have hy:=mul_lt_mul_of_pos_right hθa hLp
    nlinarith
  have hx:=mul_lt_mul_of_pos_right hθr hrp
  nlinarith


/-- BC04 with the canonical PNT prime-band mass theorem. -/
theorem band_pair_mass {Fam : PolyFamily} {mem : ℕ→Fam.ι} {α β : ℝ}
    (B : BandNV Fam mem α β) (hα : 0<α) (hαβ : α<β)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∃ (n : ℕ) (S : Finset ℕ),
      N≤n ∧ (n:ℝ)≤(1+ε)*N ∧ Good B n S ∧
        (2*(β-α)-ε)*n≤∑ ℓ∈S,2*Real.log ℓ :=
  band_pair_mass_of_mass B hα hαβ (band_mass α β hα hαβ B.bad) ε hε

/-- The prime-square band measure criterion at an independent scale. -/
theorem measure_of_bandNV {Fam : PolyFamily} (mem : ℕ→Fam.ι)
    (scale : Fam.ι→ℕ) (hscale : ∀ n,scale (mem n)=n)
    (hAdm : ∀ᶠ n : ℕ in atTop,Fam.Adm (mem n))
    {Λ D ρ κ μ α β : ℝ}
    (hΛ : Uniform.HasScaledContent Fam scale Λ)
    (hD : Uniform.HasScaledDecay Fam scale D ρ)
    (hη : Λ<D) (hρ : 0<ρ) (hκ : 0<κ) (hαβ : 0<α ∧ α<β)
    (hdeg : ∀ n,(Fam.deg (mem n):ℝ)≤κ*n) (B : BandNV Fam mem α β)
    (hμ : ρ*max (κ/(D-Λ)) (1/(2*(β-α)))<μ) :
    ∀ᶠ q : ℕ in atTop,∀ p : ℤ,(q:ℝ)^(-μ)< |Fam.const-(p:ℝ)/q| :=
  measure_of_bandNV_of_pair_mass mem scale hscale hAdm hΛ hD hη hρ hκ hαβ hdeg B
    (band_pair_mass B hαβ.1 hαβ.2) hμ
#print axioms band_pair_zero_dvd
#print axioms exists_small_lost_mass
#print axioms band_mass
#print axioms band_pair_mass
#print axioms measure_of_bandNV
end
end CatalanCore.Measure
