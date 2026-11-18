module
public import CatalanCore.Tools.Jets.Collisions
public import CatalanCore.Tools.IntegratedJets
@[expose] public section
set_option Elab.async false
open scoped BigOperators
namespace CatalanCore.Tools.JetConfigurations
open CatalanCore.Tools.Jets
attribute [local instance] Classical.propDecidable

theorem pairFactor_dvd_vandSq (M : ℕ) (i j : Fin M) (hij : i ≠ j) :
    (MvPolynomial.X i-MvPolynomial.X j)^2 ∣ vandSq M := by
  have hs : ({sortEdge i j} : Finset (Fin M × Fin M)) ⊆ vandEdges M := by
    intro p hp
    rw [Finset.mem_singleton.mp hp]
    exact sortEdge_mem M i j hij
  have hh := Finset.prod_dvd_prod_of_subset {sortEdge i j} (vandEdges M) edgeFactor hs
  simpa only [Finset.prod_singleton,edgeFactor_sort,← vandSq_edges] using hh

theorem pair_partials_zero (M : ℕ) (i j : Fin M) (hij : i ≠ j)
    (x : Fin M → ℂ) (he : x i=x j) (S : Finset (Fin M)) (hi : i ∉ S)
    (R : MvPolynomial (Fin M) ℂ) :
    MvPolynomial.eval x (partials S ((MvPolynomial.X i-MvPolynomial.X j)^2*R))=0 := by
  let E : MvPolynomial (Fin M) ℂ := (MvPolynomial.X i-MvPolynomial.X j)^2
  have hz (k : Fin M) (hki : k ≠ i) (hkj : k ≠ j) : MvPolynomial.pderiv k E=0 := by
    simp [E,MvPolynomial.pderiv_pow,map_sub,hki.symm,hkj.symm]
  have hEval : MvPolynomial.eval x E=0 := by simp [E,he]
  by_cases hj : j ∈ S
  · rw [partials_last M S j hj]
    have hfixed : ∀ k ∈ S.erase j, MvPolynomial.pderiv k E=0 := by
      intro k hk
      exact hz k (fun hh => hi (hh ▸ (Finset.mem_erase.mp hk).2)) (Finset.mem_erase.mp hk).1
    change MvPolynomial.eval x (MvPolynomial.pderiv j (partials (S.erase j) (E*R)))=0
    rw [partials_mul_fixed M (S.erase j) E R hfixed,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hEval]
    have hDer : MvPolynomial.eval x (MvPolynomial.pderiv j E)=0 := by
      simp [E,MvPolynomial.pderiv_pow,map_sub,he]
    rw [hDer]
    simp
  · have hfixed : ∀ k ∈ S, MvPolynomial.pderiv k E=0 := by
      intro k hk
      exact hz k (fun hh => hi (hh ▸ hk)) (fun hh => hj (hh ▸ hk))
    change MvPolynomial.eval x (partials S (E*R))=0
    rw [partials_mul_fixed M S E R hfixed,map_mul,hEval,zero_mul]

theorem mixedJet_pair_zero_left (M : ℕ) (J : Finset (Fin M)) (a b x : Fin M → ℂ)
    (i j : Fin M) (hij : i ≠ j) (he : x i=x j) (hi : i ∉ J) :
    mixedJet J a b x (vandSq M)=0 := by
  obtain ⟨R,hR⟩ := pairFactor_dvd_vandSq M i j hij
  unfold mixedJet
  apply Finset.sum_eq_zero
  intro S hS
  have hiS : i ∉ S := fun hh => hi (Finset.mem_powerset.mp hS hh)
  rw [hR,pair_partials_zero M i j hij x he S hiS R]
  simp

theorem mixedJet_pair_zero (M : ℕ) (J : Finset (Fin M)) (a b x : Fin M → ℂ)
    (i j : Fin M) (hij : i ≠ j) (he : x i=x j) (hn : i∉J ∨ j∉J) :
    mixedJet J a b x (vandSq M)=0 := by
  rcases hn with hi|hj
  · exact mixedJet_pair_zero_left M J a b x i j hij he hi
  · exact mixedJet_pair_zero_left M J a b x j i hij.symm he.symm hj

theorem mixedJet_triple_zero (M : ℕ) (J : Finset (Fin M)) (a b x : Fin M → ℂ)
    (i j k : Fin M) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hijx : x i=x j) (hikx : x i=x k) : mixedJet J a b x (vandSq M)=0 := by
  obtain ⟨R,hR⟩ := tripleCluster_dvd_vandSq M i j k hij hik hjk
  unfold mixedJet
  apply Finset.sum_eq_zero
  intro S hS
  rw [hR,tripleCluster_partials_zero M i j k x hijx hikx]
  simp

theorem fiber_cap_no_triple (M : ℕ) (x : Fin M → ℂ)
    (hcap : ∀ u : ℂ, (Finset.univ.filter (fun i => x i=u)).card≤2)
    (i j k : Fin M) (hijx : x i=x j) (hikx : x i=x k) : i=j ∨ i=k ∨ j=k := by
  by_contra hn
  have hij : i≠j := by tauto
  have hik : i≠k := by tauto
  have hjk : j≠k := by tauto
  have hs : ({i,j,k} : Finset (Fin M)) ⊆ Finset.univ.filter (fun l => x l=x i) := by
    intro l hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl|rfl|rfl
    · simp
    · simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hijx.symm
    · simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hikx.symm
  have hc := (Finset.card_le_card hs).trans (hcap (x i))
  simp [hij,hik,hjk] at hc

theorem exists_confluent (M : ℕ) (x : Fin M → ℂ)
    (hcap : ∀ u : ℂ, (Finset.univ.filter (fun i => x i=u)).card≤2) :
    ∃ c : ConfluentConfig M, c.x=x := by
  let ps : Finset (Fin M × Fin M) := Finset.univ.filter (fun p => p.1<p.2 ∧ x p.1=x p.2)
  have hmem (i j : Fin M) : (i,j) ∈ ps ↔ i<j ∧ x i=x j := by simp [ps]
  have hdis : ∀ p ∈ ps, ∀ q ∈ ps, p≠q → p.1≠q.1 ∧ p.1≠q.2 ∧ p.2≠q.1 ∧ p.2≠q.2 := by
    rintro ⟨i,j⟩ hp ⟨k,l⟩ hq hpq
    have hij := (hmem i j).mp hp
    have hkl := (hmem k l).mp hq
    have hneij : i≠j := ne_of_lt hij.1
    have hnekl : k≠l := ne_of_lt hkl.1
    have h1 : i≠k := by
      intro he
      subst k
      rcases fiber_cap_no_triple M x hcap i j l hij.2 hkl.2 with hh|hh|hh
      · exact hneij hh
      · exact hnekl hh
      · exact hpq (Prod.ext rfl hh)
    have h2 : i≠l := by
      intro he
      subst l
      rcases fiber_cap_no_triple M x hcap i j k hij.2 hkl.2.symm with hh|hh|hh
      · exact hneij hh
      · exact hnekl hh.symm
      · subst k; exact (lt_asymm hij.1 hkl.1)
    have h3 : j≠k := by
      intro he
      subst k
      rcases fiber_cap_no_triple M x hcap j i l hij.2.symm hkl.2 with hh|hh|hh
      · exact hneij hh.symm
      · exact hnekl hh
      · subst l; exact (lt_asymm hij.1 hkl.1)
    have h4 : j≠l := by
      intro he
      subst l
      rcases fiber_cap_no_triple M x hcap j i k hij.2.symm hkl.2.symm with hh|hh|hh
      · exact hneij hh.symm
      · exact hnekl hh.symm
      · exact hpq (Prod.ext hh rfl)
    exact ⟨h1,h2,h3,h4⟩
  refine ⟨⟨x,ps,?_,hdis,?_⟩,rfl⟩
  · intro p hp
    exact ((by simpa [ps] using hp : p.1<p.2 ∧ x p.1=x p.2)).1
  · intro i j hij
    rw [hmem,hmem]
    constructor
    · intro he
      rcases lt_or_gt_of_ne hij with h|h
      · exact Or.inl ⟨h,he⟩
      · exact Or.inr ⟨h,he.symm⟩
    · rintro (⟨h,he⟩|⟨h,he⟩)
      · exact he
      · exact he.symm
end CatalanCore.Tools.JetConfigurations
#print axioms CatalanCore.Tools.JetConfigurations.mixedJet_pair_zero
#print axioms CatalanCore.Tools.JetConfigurations.mixedJet_triple_zero
#print axioms CatalanCore.Tools.JetConfigurations.exists_confluent