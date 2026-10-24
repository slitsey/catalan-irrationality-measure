module
public import OAI.NumberTheory.Catalan.Estimates.TwoAdicSelectorExponent
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Finset
open scoped BigOperators

/-- The selected parameter tuple has an exact quadratic lower bound. -/
theorem twenty_two_adic_quadratic (N m l : ℝ) (hN : 0 ≤ N) (hm : 0 ≤ m) (hl : 0 ≤ l)
    (hml : m+l ≤ 20*N) :
    -(42*N^2) ≤ (3/2)*m^2+(1/2)*l^2-50*N*m-26*N*l+520*N^2 :=by
  have hr : 0 ≤ 20*N-m-l :=by linarith only [hml]
  have hc : 0 ≤ 6*N+m :=by linarith only [hN,hm]
  have he : (3/2)*m^2+(1/2)*l^2-50*N*m-26*N*l+520*N^2+42*N^2=
      2*(m-11*N)^2+(20*N-m-l)*(6*N+m)+(1/2)*(20*N-m-l)^2 :=by ring
  have hp :=mul_nonneg hr hc
  nlinarith only [he,hp,sq_nonneg (m-11*N),sq_nonneg (20*N-m-l)]

private theorem twenty_triangle_product (m : ℕ) :
    ((m*(m-1):ℕ):ℝ)=(m:ℝ)*((m:ℝ)-1) :=by
  cases m with
  | zero =>norm_num
  | succ m =>simp only [Nat.succ_sub_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one];ring

private theorem twenty_distinct_twice {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f (s:Set ι)) (b : ℕ) (hb : ∀ i ∈ s,b ≤ f i) :
    2*((s.card:ℝ)*(b:ℝ))+(s.card:ℝ)*((s.card:ℝ)-1) ≤ 2*∑ i ∈ s,(f i:ℝ) :=by
  have hs : s.card*b+(∑ k ∈ range s.card,k) ≤ ∑ i ∈ s,f i :=by
    rw [sum_range_id]
    exact distinct_indices_sum_lower_of_le s f hf b hb
  have hg :=sum_range_id_mul_two s.card
  have hn : 2*(s.card*b)+s.card*(s.card-1) ≤ 2*∑ i ∈ s,f i :=by omega
  have hr : 2*((s.card:ℝ)*(b:ℝ))+((s.card*(s.card-1):ℕ):ℝ) ≤
      2*∑ i ∈ s,(f i:ℝ) :=by exact_mod_cast hn
  rwa [twenty_triangle_product] at hr

/-- This verifies the exponent budget for selector data. The actual matrix
    decomposition must separately supply these injectivity hypotheses. -/
theorem twenty_two_adic_selector_budget {ι : Type*} (N : ℕ) (E B : Finset ι)
    (u j : ι → ℕ) (huE : Set.InjOn u (E:Set ι)) (huB : Set.InjOn u (B:Set ι))
    (hjE : Set.InjOn j (E:Set ι)) (hb : ∀ k ∈ E,3*N ≤ j k)
    (hcard : E.card+B.card ≤ 20*N) :
    -(42:ℝ)*(N:ℝ)^2-40*N ≤
      ((2*(∑ k ∈ E,(u k:ℤ))+(∑ k ∈ E,(j k:ℤ))-
        (27*N:ℕ)* (E.card:ℤ)+(∑ k ∈ B,(u k:ℤ))+
        (26*N:ℕ)*((20*N:ℕ)-(E.card:ℤ)-(B.card:ℤ)):ℤ):ℝ) :=by
  have hE :=twenty_distinct_twice E u huE 0 (by simp)
  have hB :=twenty_distinct_twice B u huB 0 (by simp)
  have hJ :=twenty_distinct_twice E j hjE (3*N) hb
  simp only [Nat.cast_zero,mul_zero,zero_add] at hE hB
  have hm : (0:ℝ) ≤ E.card :=Nat.cast_nonneg _
  have hl : (0:ℝ) ≤ B.card :=Nat.cast_nonneg _
  have hml : (E.card:ℝ)+(B.card:ℝ) ≤ 20*(N:ℝ) :=by exact_mod_cast hcard
  have hq :=twenty_two_adic_quadratic (N:ℝ) (E.card:ℝ) (B.card:ℝ) (Nat.cast_nonneg _) hm hl hml
  push_cast at hJ ⊢
  nlinarith only [hE,hB,hJ,hq,hm,hl,hml]

end CatalanMeasure.Parametric
