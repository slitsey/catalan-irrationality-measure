module

public import CatalanCore.Tools.Jets.Defs
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Tactic.Ring

@[expose] public section
set_option Elab.async false
open Polynomial
open scoped BigOperators
namespace CatalanCore.Tools.Jets

noncomputable def jetOp {M : ℕ} (a b : ℂ) (i : Fin M) :
    MvPolynomial (Fin M) ℂ →ₗ[ℂ] MvPolynomial (Fin M) ℂ :=
  a • LinearMap.id+b • (MvPolynomial.pderiv i).toLinearMap

/-- Independent coefficients are permitted at the two colliding jet coordinates. -/
theorem jet_double_value_general (M : ℕ) (i j : Fin M) (hij : i ≠ j)
    (ai aj bi bj x : ℂ) (R : MvPolynomial (Fin M) ℂ) :
    evalPair i j x (jetOp ai bi i (jetOp aj bj j
      ((MvPolynomial.X i-MvPolynomial.X j)^2*R))) =
      (-2*bi*bj) • evalPair i j x R := by
  classical
  have htwo : (MvPolynomial.C (2:ℂ) : MvPolynomial (Fin M) ℂ)=2 := by
    simpa using (map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin M) ℂ) 2)
  simp [jetOp, evalPair, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    hij, (Ne.symm hij), MvPolynomial.smul_eq_C_mul, htwo]
  <;> ring

theorem jet_double_value (M : ℕ) (i j : Fin M) (hij : i < j)
    (a b x : ℂ) (R : MvPolynomial (Fin M) ℂ) :
    evalPair i j x (jetOp a b i (jetOp a b j
      ((MvPolynomial.X i-MvPolynomial.X j)^2*R))) =
      (-2*b^2) • evalPair i j x R := by
  simpa only [pow_two, mul_assoc] using
    jet_double_value_general M i j (ne_of_lt hij) a a b b x R

#print axioms jet_double_value_general
#print axioms jet_double_value

theorem pderiv_commute (M : ℕ) (i j : Fin M) (p : MvPolynomial (Fin M) ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p)=
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  by_cases hij : i=j
  · subst j; rfl
  ext d
  simp only [MvPolynomial.coeff_pderiv]
  have hs : d+Finsupp.single i 1+Finsupp.single j 1=
      d+Finsupp.single j 1+Finsupp.single i 1 := by ac_rfl
  rw [hs]
  simp [Finsupp.add_apply, hij, (Ne.symm hij), mul_assoc, mul_comm, mul_left_comm]

theorem partials_last (M : ℕ) (S : Finset (Fin M)) (i : Fin M) (hi : i ∈ S)
    (p : MvPolynomial (Fin M) ℂ) :
    partials S p=MvPolynomial.pderiv i (partials (S.erase i) p) := by
  classical
  have hp : S.toList.Perm ((S.erase i).toList++[i]) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.nodup_toList S
    · apply List.nodup_append.mpr
      refine ⟨Finset.nodup_toList _, by simp, ?_⟩
      intro a ha b hb
      have hb' : b=i := by simpa using hb
      subst b
      have ha' : a ∈ S.erase i := by simpa using ha
      exact (Finset.mem_erase.mp ha').1
    · simp [Finset.union_singleton, Finset.insert_erase hi]
  unfold partials
  simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
    hp.foldl_eq' (fun u _ v _ q => pderiv_commute M v u q) p

noncomputable def derivIf {M : ℕ} (i : Fin M) (b : Bool)
    (p : MvPolynomial (Fin M) ℂ) : MvPolynomial (Fin M) ℂ :=
  if b then MvPolynomial.pderiv i p else p

theorem partials_peel (M : ℕ) (S : Finset (Fin M)) (i : Fin M)
    (p : MvPolynomial (Fin M) ℂ) :
    partials S p=derivIf i (decide (i ∈ S)) (partials (S.erase i) p) := by
  classical
  by_cases hi : i ∈ S
  · simpa [derivIf, hi] using partials_last M S i hi p
  · simp [derivIf, hi, Finset.erase_eq_of_notMem hi]

theorem derivFold_fixed (M : ℕ) (F : MvPolynomial (Fin M) ℂ) (l : List (Fin M))
    (hF : ∀ i ∈ l, MvPolynomial.pderiv i F=0) (R : MvPolynomial (Fin M) ℂ) :
    l.foldl (fun p i => MvPolynomial.pderiv i p) (F*R)=
      F*l.foldl (fun p i => MvPolynomial.pderiv i p) R := by
  induction l generalizing R with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [MvPolynomial.pderiv_mul, hF i (by simp), zero_mul, zero_add]
    exact ih (fun j hj => hF j (by simp [hj])) (MvPolynomial.pderiv i R)

theorem partials_mul_fixed (M : ℕ) (S : Finset (Fin M))
    (F R : MvPolynomial (Fin M) ℂ) (hF : ∀ i ∈ S, MvPolynomial.pderiv i F=0) :
    partials S (F*R)=F*partials S R := by
  apply derivFold_fixed M F S.toList
  intro i hi
  exact hF i (by simpa using hi)

noncomputable def tripleCluster {M : ℕ} (i j k : Fin M) : MvPolynomial (Fin M) ℂ :=
  (MvPolynomial.X i-MvPolynomial.X j)^2*
    (MvPolynomial.X i-MvPolynomial.X k)^2*(MvPolynomial.X j-MvPolynomial.X k)^2

theorem tripleCluster_deriv_outside (M : ℕ) (i j k l : Fin M)
    (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) :
    MvPolynomial.pderiv l (tripleCluster i j k)=0 := by
  classical
  simp [tripleCluster, hli, (Ne.symm hli), hlj, (Ne.symm hlj), hlk, (Ne.symm hlk)]

theorem tripleCluster_partials_zero (M : ℕ) (i j k : Fin M) (x : Fin M → ℂ)
    (hijx : x i=x j) (hikx : x i=x k) (S : Finset (Fin M))
    (R : MvPolynomial (Fin M) ℂ) :
    MvPolynomial.eval x (partials S (tripleCluster i j k*R))=0 := by
  classical
  rw [partials_peel M S i, partials_peel M (S.erase i) j,
    partials_peel M ((S.erase i).erase j) k]
  have hF : ∀ l ∈ ((S.erase i).erase j).erase k,
      MvPolynomial.pderiv l (tripleCluster i j k)=0 := by
    intro l hl
    rcases Finset.mem_erase.mp hl with ⟨hlk,hl⟩
    rcases Finset.mem_erase.mp hl with ⟨hlj,hl⟩
    rcases Finset.mem_erase.mp hl with ⟨hli,_⟩
    exact tripleCluster_deriv_outside M i j k l hli hlj hlk
  rw [partials_mul_fixed M _ _ _ hF]
  have hjkx : x j=x k := hijx.symm.trans hikx
  unfold derivIf
  split_ifs <;> simp [tripleCluster, hijx, hikx, hjkx, Pi.single_apply]

noncomputable def vandEdges (M : ℕ) : Finset (Fin M × Fin M) :=
  (Finset.univ.product Finset.univ).filter (fun p => p.1 < p.2)
noncomputable def edgeFactor {M : ℕ} (e : Fin M × Fin M) : MvPolynomial (Fin M) ℂ :=
  (MvPolynomial.X e.1-MvPolynomial.X e.2)^2

theorem vandSq_edges (M : ℕ) : vandSq M=∏ e ∈ vandEdges M, edgeFactor e := by
  classical
  unfold vandEdges
  rw [Finset.prod_filter]
  calc
    vandSq M=∏ i : Fin M, ∏ j : Fin M,
        if i < j then edgeFactor (i,j) else 1 := by
      unfold vandSq
      apply Finset.prod_congr rfl
      intro i _
      have hs : Finset.Ioi i=Finset.univ.filter (fun j : Fin M => i < j) := by ext j; simp
      rw [hs, Finset.prod_filter]
      rfl
    _=∏ e ∈ (Finset.univ : Finset (Fin M)).product Finset.univ,
        if e.1 < e.2 then edgeFactor e else 1 :=
      (Finset.prod_product Finset.univ Finset.univ
        (fun e : Fin M × Fin M => if e.1 < e.2 then edgeFactor e else 1)).symm

def sortEdge {M : ℕ} (i j : Fin M) : Fin M × Fin M := if i < j then (i,j) else (j,i)

theorem sortEdge_mem (M : ℕ) (i j : Fin M) (hne : i ≠ j) : sortEdge i j ∈ vandEdges M := by
  classical
  unfold sortEdge
  split_ifs with h
  · simp [vandEdges, h]
  · have hj : j < i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
    simp [vandEdges, hj]

theorem edgeFactor_sort (M : ℕ) (i j : Fin M) :
    edgeFactor (sortEdge i j)=(MvPolynomial.X i-MvPolynomial.X j)^2 := by
  classical
  unfold sortEdge edgeFactor
  split_ifs <;> dsimp <;> ring

theorem tripleCluster_dvd_vandSq (M : ℕ) (i j k : Fin M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : tripleCluster i j k ∣ vandSq M := by
  classical
  let A := sortEdge i j
  let B := sortEdge i k
  let C := sortEdge j k
  have hAB : A ≠ B := by dsimp [A,B,sortEdge]; split_ifs <;> simp_all
  have hAC : A ≠ C := by dsimp [A,C,sortEdge]; split_ifs <;> simp_all
  have hBC : B ≠ C := by dsimp [B,C,sortEdge]; split_ifs <;> simp_all
  have hsub : ({A,B,C} : Finset (Fin M × Fin M)) ⊆ vandEdges M := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact sortEdge_mem M i j hij
    · exact sortEdge_mem M i k hik
    · exact sortEdge_mem M j k hjk
  have hsmall : (∏ e ∈ ({A,B,C} : Finset (Fin M × Fin M)), edgeFactor e)=tripleCluster i j k := by
    simp [hAB,hAC,hBC,A,B,C,edgeFactor_sort,tripleCluster,mul_assoc]
  have h := Finset.prod_dvd_prod_of_subset {A,B,C} (vandEdges M) edgeFactor hsub
  rw [hsmall, ← vandSq_edges] at h
  exact h

theorem jet_triple_zero (M : ℕ) (a b x : Fin M → ℂ)
    (i j k : Fin M) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hijx : x i=x j) (hikx : x i=x k) : jetAt a b x (vandSq M)=0 := by
  classical
  obtain ⟨R,hR⟩ := tripleCluster_dvd_vandSq M i j k hij hik hjk
  unfold jetAt mixedJet
  apply Finset.sum_eq_zero
  intro S _
  rw [hR, tripleCluster_partials_zero M i j k x hijx hikx]
  simp

#print axioms jet_triple_zero
end CatalanCore.Tools.Jets
