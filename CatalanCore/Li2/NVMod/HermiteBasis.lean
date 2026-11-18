module
public import CatalanCore.Li2.NVMod.InfinityDefinitions
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

def poleSlots (ts : List ℕ) : List ℕ := ts.flatMap (fun t=>[t,t,t])
def nodeLabel (ts : List ℕ) (i : ℕ) : ℕ := (poleSlots ts).getD i 0
def hermitePoly (A : TypeKey) (earlier : List ℕ) : List ℕ → ℕ → ℚ[X]
  | [],i => earlierPoly A earlier * X^i
  | t::ts,i => if i<3 then earlierPoly A earlier*(X+C (t:ℚ))^i
    else hermitePoly A (earlier++[t]) ts (i-3)

theorem earlierPoly_append (A : TypeKey) (es : List ℕ) (t : ℕ) :
    earlierPoly A (es++[t])=earlierPoly A es*(X+C (t:ℚ))^3 := by
  simp [earlierPoly,List.map_append,List.prod_append,mul_assoc]

theorem earlierPoly_degree (A : TypeKey) (es : List ℕ) :
    (earlierPoly A es).natDegree=(if A.kind=.U then 1 else 0)+3*es.length := by
  induction es using List.reverseRecOn with
  | nil => simp [earlierPoly]; split_ifs <;> simp
  | append_singleton es t ih =>
    rw [earlierPoly_append,Polynomial.natDegree_mul (earlierPoly_monic A es).ne_zero
      ((Polynomial.monic_X_add_C (t:ℚ)).pow 3).ne_zero,ih,
      (Polynomial.monic_X_add_C (t:ℚ)).natDegree_pow,Polynomial.natDegree_X_add_C]
    simp only [List.length_append,List.length_singleton]
    omega

theorem hermitePoly_monic (A : TypeKey) (es ts : List ℕ) (i : ℕ) :
    (hermitePoly A es ts i).Monic := by
  induction ts generalizing es i with
  | nil => exact (earlierPoly_monic A es).mul (Polynomial.monic_X.pow i)
  | cons t ts ih =>
    simp only [hermitePoly]
    split_ifs
    · exact (earlierPoly_monic A es).mul ((Polynomial.monic_X_add_C _).pow i)
    · exact ih _ _

theorem hermitePoly_degree (A : TypeKey) (es ts : List ℕ) (i : ℕ) :
    (hermitePoly A es ts i).natDegree=(if A.kind=.U then 1 else 0)+3*es.length+i := by
  induction ts generalizing es i with
  | nil =>
    simp only [hermitePoly]
    rw [Polynomial.natDegree_mul (earlierPoly_monic A es).ne_zero
      (Polynomial.monic_X.pow i).ne_zero,earlierPoly_degree,Polynomial.natDegree_X_pow]
  | cons t ts ih =>
    simp only [hermitePoly]
    by_cases hi : i<3
    · rw [if_pos hi,Polynomial.natDegree_mul (earlierPoly_monic A es).ne_zero
        ((Polynomial.monic_X_add_C (t:ℚ)).pow i).ne_zero,earlierPoly_degree,
        (Polynomial.monic_X_add_C (t:ℚ)).natDegree_pow,Polynomial.natDegree_X_add_C]
      omega
    · rw [if_neg hi,ih]
      simp only [List.length_append,List.length_singleton]
      omega

theorem earlierPoly_dvd (A : TypeKey) (es : List ℕ) (t : ℕ) (ht : t∈es) :
    (X+C (t:ℚ))^3 ∣ earlierPoly A es := by
  induction es with
  | nil => simp at ht
  | cons m ms ih =>
    have he : earlierPoly A (m::ms)=(X+C (m:ℚ))^3*earlierPoly A ms := by
      simp [earlierPoly,mul_left_comm,mul_assoc]
    rw [he]
    rcases List.mem_cons.mp ht with heq|hm
    · subst m; exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (ih hm) _

theorem hermitePoly_earlier_dvd (A : TypeKey) (es ts : List ℕ) (i : ℕ) :
    earlierPoly A es ∣ hermitePoly A es ts i := by
  induction ts generalizing es i with
  | nil => exact dvd_mul_right _ _
  | cons t ts ih =>
    simp only [hermitePoly]
    split_ifs
    · exact dvd_mul_right _ _
    · exact dvd_trans (by rw [earlierPoly_append]; exact dvd_mul_right _ _) (ih _ _)

theorem poleSlots_length (ts : List ℕ) : (poleSlots ts).length=3*ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [poleSlots,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *
    omega

theorem nodeLabel_cons (t : ℕ) (ts : List ℕ) (i : ℕ) :
    nodeLabel (t::ts) i=if i<3 then t else nodeLabel ts (i-3) := by
  rcases i with _|i
  · rfl
  rcases i with _|i
  · rfl
  rcases i with _|i
  · rfl
  simp [nodeLabel,poleSlots,List.getD]

theorem nodeLabel_mem (ts : List ℕ) (i : ℕ) (hi : i<3*ts.length) : nodeLabel ts i∈ts := by
  induction ts generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
    rw [nodeLabel_cons]
    split_ifs with h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ (by simp only [List.length_cons] at hi; omega))

theorem prefix_pole_before (A : TypeKey) (es ts : List ℕ) (t u : ℕ)
    (hp : es++t::ts=poleList A) (hu : u∈poleSet A) (hut : u<t) : u∈es := by
  have hm : u∈es++t::ts := by rw [hp]; exact (mem_poleList A u).mpr hu
  rcases List.mem_append.mp hm with he|hts
  · exact he
  · have hpair : (es++t::ts).Pairwise (·<·) := hp ▸ poleList_pairwise A
    have htail := (List.pairwise_append.mp hpair).2.1
    rcases List.mem_cons.mp hts with heq|hmem
    · omega
    · have htu := (List.pairwise_cons.mp htail).1 u hmem
      omega

theorem hermitePoly_previous_dvd (A : TypeKey) (es ts : List ℕ) (i u : ℕ)
    (hp : es++ts=poleList A) (hi : i<3*ts.length) (hu : u∈poleSet A)
    (hui : u<nodeLabel ts i) : (X+C (u:ℚ))^3∣hermitePoly A es ts i := by
  induction ts generalizing es i with
  | nil => simp at hi
  | cons t ts ih =>
    by_cases hit : i<3
    · have hut : u<t := by simpa only [nodeLabel_cons,if_pos hit] using hui
      exact dvd_trans (earlierPoly_dvd A es u (prefix_pole_before A es ts t u hp hu hut))
        (hermitePoly_earlier_dvd A es (t::ts) i)
    · simp only [hermitePoly,if_neg hit]
      apply ih (es++[t]) (i-3)
      · simpa only [List.append_assoc,List.singleton_append] using hp
      · simp only [List.length_cons] at hi; omega
      · simpa only [nodeLabel_cons,if_neg hit] using hui

theorem hermitePoly_X_dvd (A : TypeKey) (es ts : List ℕ) (i : ℕ) (hU : A.kind=.U) :
    X∣hermitePoly A es ts i := by
  apply dvd_trans _ (hermitePoly_earlier_dvd A es ts i)
  simp only [earlierPoly,hU,ite_true]
  exact dvd_mul_right _ _

#print axioms hermitePoly_monic
#print axioms hermitePoly_degree
#print axioms hermitePoly_earlier_dvd
#print axioms nodeLabel_mem
#print axioms hermitePoly_previous_dvd
#print axioms hermitePoly_X_dvd
end
end CatalanCore.Li2.NVMod
