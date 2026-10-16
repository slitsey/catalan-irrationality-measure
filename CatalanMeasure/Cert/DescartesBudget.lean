module
public import CatalanMeasure.Cert.HomWitness
public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Topology.Order.IntermediateValue
@[expose] public section
namespace CatalanMeasure.Cert
open Polynomial Set Finset
open scoped BigOperators
noncomputable section

def ipPoly : List ℤ → ℤ[X]
  | [] => 0
  | c::p => C c+X*ipPoly p

theorem ipPoly_eval_real (p : List ℤ) (x : ℝ) :
    ((ipPoly p).map (Int.castRingHom ℝ)).eval x=ipEval p x := by
  induction p with
  | nil => simp [ipPoly,ipEval]
  | cons c p ih => simp [ipPoly,ipEval,ih]

theorem ipPoly_continuous (p : List ℤ) : Continuous (ipEval p) := by
  have he : ipEval p=fun x => ((ipPoly p).map (Int.castRingHom ℝ)).eval x := by
    funext x; exact (ipPoly_eval_real p x).symm
  rw [he]
  fun_prop

theorem coeffList_map_int_real (P : ℤ[X]) :
    (P.map (Int.castRingHom ℝ)).coeffList=P.coeffList.map (fun z : ℤ => (z:ℝ)) := by
  unfold Polynomial.coeffList
  rw [degree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)]
  simp only [List.map_map]
  apply List.map_congr_left
  intro n hn
  simp

theorem signVariations_map_int_real (P : ℤ[X]) :
    (P.map (Int.castRingHom ℝ)).signVariations=P.signVariations := by
  unfold Polynomial.signVariations
  rw [coeffList_map_int_real]
  exact List.signVariations_map (fun z => sign_intCast z) P.coeffList

/-- A root-count certificate bounds every finite set of distinct roots in its
open interval. It is independent of any subdivision or root-cover algorithm. -/
def RootBudget (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : Prop :=
  ∀ s : Finset ℝ, (∀ x ∈ s, x ∈ Ioo a b ∧ f x=0) → s.card ≤ n

theorem rootBudget_of_positive_polynomial {f g : ℝ → ℝ} {a b : ℝ}
    (Q : ℝ[X]) (hQ : Q≠0) (hg : Set.InjOn g (Ioo a b))
    (hroot : ∀ x ∈ Ioo a b, f x=0 → 0<g x ∧ Q.eval (g x)=0) :
    RootBudget f a b Q.signVariations := by
  classical
  intro s hs
  let t := (Q.roots.filter (fun x => 0<x)).toFinset
  have hi : Set.InjOn g (s: Set ℝ) := by
    intro x hx y hy hxy
    exact hg (hs x hx).1 (hs y hy).1 hxy
  have hsub : s.image g ⊆ t := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨hp,hr⟩ := hroot x (hs x hx).1 (hs x hx).2
    simp only [t,Multiset.mem_toFinset,Multiset.mem_filter]
    exact ⟨(Polynomial.mem_roots hQ).mpr hr,hp⟩
  calc
    s.card=(s.image g).card := (card_image_iff.mpr hi).symm
    _ ≤ t.card := card_le_card hsub
    _ ≤ (Q.roots.filter (fun x => 0<x)).card := Multiset.toFinset_card_le _
    _ = Q.roots.countP (fun x => 0<x) := (Multiset.countP_eq_card_filter _ _).symm
    _ ≤ Q.signVariations := Polynomial.roots_countP_pos_le_signVariations Q

theorem ipHom_rootBudget {p D N : List ℤ} {a b d : ℤ}
    (hh : ipHom a b d p=(D,N)) (hd : 0<d) (hab : a<b)
    (hN : ipPoly N≠0) :
    RootBudget (ipEval p) ((a:ℝ)/d) ((b:ℝ)/d) (ipPoly N).signVariations := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  let g : ℝ → ℝ := fun x => ((b:ℝ)-d*x)/(d*x-a)
  have hmap (x : ℝ) (hx : x ∈ Ioo ((a:ℝ)/d) ((b:ℝ)/d)) :
      0<g x ∧ ((b:ℝ)+a*g x)/(d+d*g x)=x := by
    have hl : (a:ℝ)<d*x := by
      have := (div_lt_iff₀ hdR).mp hx.1; nlinarith only [this]
    have hu : d*x<(b:ℝ) := by
      have := (lt_div_iff₀ hdR).mp hx.2; nlinarith only [this]
    have hp : 0<g x := div_pos (sub_pos.mpr hu) (sub_pos.mpr hl)
    refine ⟨hp,?_⟩
    have hden : (d:ℝ)+d*g x≠0 := by positivity
    apply (div_eq_iff hden).mpr
    have hxa : (d:ℝ)*x-a≠0 := (sub_pos.mpr hl).ne'
    dsimp [g]
    field_simp [hxa]
    ring
  have hi : Set.InjOn g (Ioo ((a:ℝ)/d) ((b:ℝ)/d)) := by
    intro x hx y hy he
    rw [← (hmap x hx).2,← (hmap y hy).2,he]
  have hc := rootBudget_of_positive_polynomial (f := ipEval p) (g := g)
    ((ipPoly N).map (Int.castRingHom ℝ))
    ((Polynomial.map_ne_zero_iff
      (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)).mpr hN) hi (by
      intro x hx hz
      have hm := hmap x hx
      refine ⟨hm.1,?_⟩
      rw [ipPoly_eval_real]
      have hr : (d:ℝ)+d*g x≠0 := (add_pos hdR (mul_pos hdR hm.1)).ne'
      have he := (ipHom_eval p a b d (g x) hr).2
      rw [hh,hm.2,hz,mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_left hr)
  simpa only [signVariations_map_int_real] using hc

/-- Once every root allowed by a finite budget has been found in disjoint
brackets, there are no further roots outside those brackets. -/
theorem root_coverage_of_budget {f : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (B : Fin n → ℝ × ℝ) (hb : RootBudget f a b n)
    (hinside : ∀ i, a≤(B i).1 ∧ (B i).2≤b)
    (hdisjoint : ∀ i j, i≠j → (B i).2≤(B j).1 ∨ (B j).2≤(B i).1)
    (hroots : ∀ i, ∃ x ∈ Ioo (B i).1 (B i).2, f x=0) :
    ∀ x ∈ Ioo a b, f x=0 → ∃ i, x ∈ Icc (B i).1 (B i).2 := by
  classical
  choose r hr hz using hroots
  have hinj : Function.Injective r := by
    intro i j hij
    by_contra hn
    rcases hdisjoint i j hn with h|h
    · have hi := (hr i).2
      have hj := (hr j).1
      linarith only [hi,hj,h,hij]
    · have hi := (hr i).1
      have hj := (hr j).2
      linarith only [hi,hj,h,hij]
  intro x hx hfx
  by_contra hn
  have hxnot : x ∉ Finset.univ.image r := by
    intro hxmem
    obtain ⟨i,_,hi⟩ := mem_image.mp hxmem
    apply hn
    exact ⟨i,by simpa only [← hi] using (show r i ∈ Icc (B i).1 (B i).2 from
      ⟨(hr i).1.le,(hr i).2.le⟩)⟩
  have hcard : (Finset.univ.image r).card=n := by
    rw [Finset.card_image_of_injective _ hinj,card_univ,Fintype.card_fin]
  have hh := hb (insert x (Finset.univ.image r)) (by
    intro y hy
    rcases mem_insert.mp hy with rfl|hy
    · exact ⟨hx,hfx⟩
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hy
      exact ⟨⟨lt_of_le_of_lt (hinside i).1 (hr i).1,
        lt_of_lt_of_le (hr i).2 (hinside i).2⟩,hz i⟩)
  rw [card_insert_of_notMem hxnot,hcard] at hh
  omega

end
end CatalanMeasure.Cert
