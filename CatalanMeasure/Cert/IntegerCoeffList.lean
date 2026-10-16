module
public import CatalanMeasure.Cert.DescartesBudget
@[expose] public section
namespace CatalanMeasure.Cert
open Polynomial

theorem ipPoly_coeff (p : List ℤ) (n : ℕ) : (ipPoly p).coeff n=p.getD n 0 := by
  induction p generalizing n with
  | nil => simp [ipPoly]
  | cons c p ih =>
    cases n with
    | zero => simp [ipPoly]
    | succ n =>
      rw [ipPoly,coeff_add,coeff_C_succ,coeff_X_mul,zero_add,ih,List.getD_cons_succ]

theorem ipPoly_natDegree_le (p : List ℤ) : (ipPoly p).natDegree ≤ p.length-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [ipPoly_coeff]
  have hge : p.length ≤ n := by omega
  have he : p[n]?=none := List.getElem?_eq_none hge
  simp only [List.getD_eq_getElem?_getD,he,Option.getD_none]

theorem map_range_getD (p : List ℤ) :
    (List.range p.length).map (fun i => p.getD i 0)=p := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map,List.getElem_range]
    exact (List.getElem_eq_getD 0).symm

theorem ipPoly_coeffList_concat (p : List ℤ) {c : ℤ} (hc : c≠0) :
    (ipPoly (p++[c])).coeffList=(p++[c]).reverse := by
  have hcoef : (ipPoly (p++[c])).coeff p.length=c := by rw [ipPoly_coeff];simp
  have hnz : ipPoly (p++[c])≠0 := by
    intro hz
    rw [hz,coeff_zero] at hcoef
    exact hc hcoef.symm
  have hle : (ipPoly (p++[c])).natDegree ≤ p.length := by
    simpa using ipPoly_natDegree_le (p++[c])
  have hnat : (ipPoly (p++[c])).natDegree=p.length :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hcoef];exact hc))
  unfold Polynomial.coeffList
  rw [withBotSucc_degree_eq_natDegree_add_one hnz,hnat,List.map_reverse]
  apply congrArg List.reverse
  calc
    _ = (List.range (p.length+1)).map (fun n => (p++[c]).getD n 0) := by
      apply List.map_congr_left
      intro n hn
      exact ipPoly_coeff _ _
    _ = _ := by simpa only [List.length_append,List.length_singleton] using map_range_getD (p++[c])

theorem ipPoly_append_zero (p : List ℤ) : ipPoly (p++[0])=ipPoly p := by
  induction p with
  | nil => simp [ipPoly]
  | cons c p ih => simp [ipPoly,ih]

theorem ipPoly_append_zeros (p : List ℤ) (n : ℕ) :
    ipPoly (p++List.replicate n 0)=ipPoly p := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ,
      show p++(0::List.replicate n 0)=(p++[0])++List.replicate n 0 by simp]
    rw [ih,ipPoly_append_zero]

theorem ipPoly_signVariations_of_list {p q : List ℤ} {c : ℤ} {n : ℕ}
    (hp : p=(q++[c])++List.replicate n 0) (hc : c≠0) :
    (ipPoly p).signVariations=((q++[c]).reverse).signVariations := by
  rw [hp,ipPoly_append_zeros]
  unfold Polynomial.signVariations
  rw [ipPoly_coeffList_concat q hc]

end CatalanMeasure.Cert
