module

public import CatalanCore.Uniform.Bank.Plane3.Frame
public import CatalanCore.Uniform.Bank.Plane3.Data
public import CatalanCore.Uniform.Support.Producer

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Plane 3: actual rational coefficient arithmetic (Q09)
The general all-order suppliers are reused on the exact datum sequences.
All common deletions and all rational coefficients are retained. The first
coefficient is zero; no numerator-prime exclusion or new ND assertion occurs.
-/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Uniform.Support
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.Member
open CatalanCore.Uniform.Content.SmallPrimes Finset Polynomial
open CatalanCore.Uniform.Content.Wire

def coefficients (v u : ℚ) (j : ℕ) : ℚ :=
  if j = 2 then -v else if j = 3 then 2*u else 0

theorem datum_f (v u : ℚ) (hu : u ≠ 0) :
    (datum v u hu).f = hpoleF 4 (coefficients v u) := by
  funext t
  unfold PoleDatum.f hpoleF
  apply Finset.sum_congr rfl
  intro k hk
  change (∑ _i : Fin 1, ∑ j ∈ Icc (1 : ℕ) 3,
    coefficients v u j / ((k : ℚ)+1)^j) = _
  rw [Fin.sum_univ_one]

theorem datum_e (v u : ℚ) (hu : u ≠ 0) :
    (datum v u hu).e = hpoleE 4 (coefficients v u) := by
  funext t
  unfold PoleDatum.e hpoleE
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  change -(-(∑ _i : Fin 1, ∑ j ∈ Icc (1 : ℕ) 3,
    (j : ℚ)*coefficients v u j / ((k : ℚ)+1)^(j+1))) = _
  rw [neg_neg, Fin.sum_univ_one]

def coefficientThreshold (v u : ℚ) : ℕ := IntegerPoleRows.coeffCrude 4 (coefficients v u)

theorem coefficients_mem (v u : ℚ) {p : ℕ} [Fact p.Prime]
    (hp : coefficientThreshold v u < p) :
    ∀ j ∈ Icc (1 : ℕ) 3, coefficients v u j ∈ LocRing p := by
  intro j hj
  have hden : (coefficients v u j).den ≤ coefficientThreshold v u := by
    exact Finset.single_le_sum (f := fun j => (coefficients v u j).den)
      (fun _ _ => Nat.zero_le _) hj
  rw [mem_locRing]
  intro hd
  have := Nat.le_of_dvd (coefficients v u j).den_pos hd
  omega

theorem plane3_catalogue (v u : ℚ) (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ) :
    KCatValidFam c hc const depth
      (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
        (altGeom c hc).geometry)
      [⟨2,1,1⟩, ⟨2,1,1⟩] 2 2 (coefficientThreshold v u) plane3Catalogue := by
  intro br hbr i hi hr p _ hpb hpn hN kv hkv hcond
  have hd := coefficients_mem v u hpn
  have hs := altGeom_hybShape c hc hi.2
  have hwin : i.1 + 2 * ((altGeom c hc).geometry i.1).k < p*p := by
    rw [geometry_k_eq_borderSize]
    omega
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with hp | hp
    · omega
    · exact hp
  have first := IntegerPoleRows.family_first 4 (by decide) (coefficients v u) hd hs i.2 hwin hodd
  simp only [plane3Catalogue, List.mem_cons, List.not_mem_nil, or_false] at hbr
  rcases hbr with rfl | rfl | rfl | rfl | rfl
  · refine ⟨_, first, ?_⟩
    simp [firstBranch, KExpr.evalN, IntegerPoleRows.delta, geometry_k_eq_borderSize]
  · have hpr : p ≤ i.1 := by
      have h := hcond ⟨1,-1,0,[],0,false⟩ (by simp [secondBranch])
      norm_num [KCond.Holds, KCond.L, dot] at h
      omega
    refine ⟨_, IntegerPoleRows.family_second 4 (by decide) (coefficients v u) hd hs i.2 hwin hpr, ?_⟩
    simp [secondBranch, KExpr.evalN, geometry_k_eq_borderSize]
  · have hpr : p ≤ i.1 := by
      have h := hcond ⟨1,-1,0,[],0,false⟩ (by simp [thirdBranch])
      norm_num [KCond.Holds, KCond.L, dot] at h
      omega
    have hrp : i.1 ≤ 2*p := by
      have h := hcond ⟨-1,2,0,[],0,false⟩ (by simp [thirdBranch])
      norm_num [KCond.Holds, KCond.L, dot] at h
      omega
    have hmp : 2*((altGeom c hc).geometry i.1).k ≤ p := by
      have h := hcond ⟨0,1,-2,[],0,false⟩ (by simp [thirdBranch])
      norm_num [KCond.Holds, KCond.L, dot] at h
      rw [geometry_k_eq_borderSize]
      omega
    have hhi : i.1 + 2*((altGeom c hc).geometry i.1).k ≤ 3*p := by
      have h := hcond ⟨-1,3,-2,[],0,false⟩ (by simp [thirdBranch])
      norm_num [KCond.Holds, KCond.L, dot] at h
      rw [geometry_k_eq_borderSize]
      omega
    by_cases hlo : 2*p ≤ i.1 + 2*((altGeom c hc).geometry i.1).k
    · refine ⟨_, IntegerPoleRows.family_third 4 (by decide) (coefficients v u) hd hs i.2 hwin hpr hrp hmp hlo hhi, ?_⟩
      simp [thirdBranch, KExpr.evalN, geometry_k_eq_borderSize]
    · have hrow := IntegerPoleRows.family_second 4 (by decide) (coefficients v u) hd hs i.2 hwin hpr
      refine ⟨_, hrow, ?_⟩
      simp only [thirdBranch, KExpr.evalN, Nat.zero_mul, add_zero]
      simp only [geometry_k_eq_borderSize] at hlo hmp hhi ⊢
      omega
  · have hpr : i.1 ≤ p := by
      have h := hcond ⟨-1,1,0,[],0,false⟩ (by simp [fourthBranch])
      norm_num [KCond.Holds, KCond.L, dot] at h
      omega
    refine ⟨_, IntegerPoleRows.family_fourth 4 (by decide) (coefficients v u) hd hs i.2 hwin hpr, ?_⟩
    simp [fourthBranch, KExpr.evalN, geometry_k_eq_borderSize]
  · have hnp : i.1 + 2*((altGeom c hc).geometry i.1).k ≤ p := by
      have h := hcond ⟨-1,1,-2,[],0,false⟩ (by simp [zeroBranch])
      norm_num [KCond.Holds, KCond.L, dot] at h
      rw [geometry_k_eq_borderSize]
      omega
    have hrow := IntegerPoleRows.family_fourth 4 (by decide) (coefficients v u) hd hs i.2 hwin (by omega)
    refine ⟨0, ?_, ?_⟩
    · rw [Nat.sub_eq_zero_of_le hnp, Nat.mul_zero] at hrow
      exact hrow
    · simp [zeroBranch, KExpr.evalN]

def plane3Translation : Transl 20 1 84 64 plane3BaseCatalogue where
  ρ _ br := br
  debit _ _ := rfl
  price := by
    intro n br hbr r p m kv
    simp only [plane3BaseCatalogue, List.mem_singleton] at hbr
    subst br
    simpa [firstBranch, KExpr.evalN, IntegerPoleRows.lowPrice, IntegerPoleRows.delta] using
      IntegerPoleRows.lowPrice_cov 4 (by decide) r m n 1 20 p
  cond := by
    intro n br hbr r p m kv hΩ hcond cd hcd
    simp only [plane3BaseCatalogue, List.mem_singleton] at hbr
    subst br
    simp [firstBranch] at hcd

theorem plane3_translated_catalogue (v u : ℚ) (c : ℚ) (hc : 0 < c)
    (const : ℝ) (depth n : ℕ) :
    KCatValidFam c hc const depth
      (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
        (altGeom c hc).geometry)
      [⟨2,1,1⟩, ⟨2,1,1⟩] 2 2 (coefficientThreshold v u)
      (plane3BaseCatalogue.map (plane3Translation.ρ n)) := by
  intro br hbr
  apply plane3_catalogue v u c hc const depth br
  simp only [plane3BaseCatalogue, List.map_cons, List.map_nil, List.mem_singleton, plane3Translation] at hbr
  subst br
  simp [plane3Catalogue]

def prefixCutoff (v u : ℚ) : ℕ := 400001 + (coefficientThreshold v u + 1)^2
def crudeFactor (v u : ℚ) : ℕ := coefficientThreshold v u + 5

theorem plane3_scaled_crude (v u : ℚ) (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1)
    (const : ℝ) (depth : ℕ) :
    ∀ i, (AltEvenFam c hc const depth
      (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
        (altGeom c hc).geometry)).Adm i →
    ∀ (p : ℕ) [Fact p.Prime],
      GLE p (crudeFactor v u * Ecrude 1 i.1 p)
        (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
          (altGeom c hc).geometry i) := by
  intro i hi p _
  apply seq_alt_scaled_crude c hc hc1 _ _ (crudeFactor v u) 1 ?_ i hi.2 p
  intro p _ N A B hN hA hB
  have hb := IntegerPoleRows.hpole_lw_gle_crude (p := p) 4 (by decide) (coefficients v u)
    (coefficientThreshold v u)
    (fun j hj => IntegerPoleRows.coeff_scaled_mem (p := p) 4 (coefficients v u) hj) hN hA hB
  refine hb.mono ?_
  dsimp [crudeFactor]
  nlinarith

theorem plane3_pre (v u : ℚ) (const : ℝ) (depth : ℕ) :
    PreValidFam (1/10) (by norm_num) const depth
      (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
        (altGeom (1/10) (by norm_num)).geometry) 2
      (SmallBudget.sqrtLog (prefixCutoff v u) (32*crudeFactor v u))
      (1/40) (420001/100000) := by
  apply preValid_of_scaled_crude_rows (1/10) (by norm_num) const depth _
    (plane3_scaled_crude v u (1/10) (by norm_num) (by norm_num) const depth)
    2 (SmallBudget.sqrtLog (prefixCutoff v u) (32*crudeFactor v u))
    (prefixCutoff v u) (32*crudeFactor v u) (by omega)
    (fun r p hp hpr => by rw [SmallBudget.sqrtLog_X_of _ _ _ _ hp])
    (1/40) (420001/100000) (by norm_num) (by norm_num)
  intro i hi p _ hsq hpr
  have hr : 0 < i.1 := lt_of_lt_of_le (Fact.out : p.Prime).pos hpr
  have hlarge : prefixCutoff v u < i.1 := by
    have hsqr := Nat.mul_self_le_mul_self hpr
    nlinarith
  have hp : coefficientThreshold v u < p := by
    by_contra hn
    have h1 : p ≤ coefficientThreshold v u := by omega
    have h2 : p*p ≤ (coefficientThreshold v u)^2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self h1
    have h3 : prefixCutoff v u ≤ prefixCutoff v u * i.1 := Nat.le_mul_of_pos_right _ hr
    have h4 : (coefficientThreshold v u)^2 < prefixCutoff v u := by
      dsimp [prefixCutoff]
      nlinarith
    omega
  have hs := altGeom_hybShape (1/10) (by norm_num) hi.2
  have hwin : i.1 + 2*((altGeom (1/10) (by norm_num)).geometry i.1).k < p*p := by
    have hm := altGeom_borderSize_le (1/10) (by norm_num) (by norm_num) hi.2
    rw [geometry_k_eq_borderSize]
    have hA : 3 ≤ prefixCutoff v u := by dsimp [prefixCutoff]; omega
    have hmA := Nat.mul_le_mul_right i.1 hA
    omega
  have hodd : p % 2 = 1 := by
    have hpb : 2 < p := by
      have hA : 3 ≤ prefixCutoff v u := by dsimp [prefixCutoff]; omega
      have hmA := Nat.mul_le_mul_right i.1 hA
      nlinarith [(Fact.out : p.Prime).two_le]
    rcases (Fact.out : p.Prime).eq_two_or_odd with hp2 | hp2 <;> omega
  have hrow := IntegerPoleRows.family_first 4 (by decide) (coefficients v u)
    (coefficients_mem v u hp) hs i.2 hwin hodd
  refine ⟨_, hrow, ?_⟩
  have hle : 4*(i.1+((altGeom (1/10) (by norm_num)).geometry i.1).k) -
      IntegerPoleRows.delta ((altGeom (1/10) (by norm_num)).geometry i.1).k p ≤
      4*(i.1+((altGeom (1/10) (by norm_num)).geometry i.1).k) := Nat.sub_le _ _
  have hb := (TwoTerm.altGeom_border (1/10) (by norm_num) hi.2).2
  have hbR := (Rat.cast_lt (K := ℝ)).2 hb
  push_cast at hbR
  have hrR : (400001 : ℝ) < i.1 := by
    exact_mod_cast (show 400001 < i.1 by dsimp [prefixCutoff] at hlarge; omega)
  have hleR : ((4*(i.1+((altGeom (1/10) (by norm_num)).geometry i.1).k) -
      IntegerPoleRows.delta ((altGeom (1/10) (by norm_num)).geometry i.1).k p : ℕ) : ℝ) ≤
      4*((i.1 : ℝ)+((altGeom (1/10) (by norm_num)).geometry i.1).k) := by exact_mod_cast hle
  change _ ≤ (420001/100000 : ℚ) * (i.1 : ℝ)
  push_cast
  change _ ≤ (420001/100000 : ℝ) * (i.1 : ℝ)
  rw [geometry_k_eq_borderSize] at hleR ⊢
  linarith

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.datum_f
#print axioms CatalanCore.Uniform.Bank.Plane3.datum_e
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_catalogue
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3Translation
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_translated_catalogue
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_scaled_crude
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_pre
