import CatalanCore.Uniform.Content.RankProducer.FibreCounts
import CatalanCore.Uniform.Content.RankProducer.LineMember
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open Finset Module CatalanCore CatalanCore.Uniform.Content.Hybrid
open scoped Classical

/-- A matching subset contributes its cardinality through an injective residue image. -/
theorem card_filter_le_score {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (S : Finset β) (g : α → β) (P : α → Prop) (f : β → ℕ)
    (hinj : Set.InjOn g (A : Set α)) (hmem : ∀ x ∈ A, g x ∈ S)
    (hscore : ∀ x ∈ A, P x → 1 ≤ f (g x)) :
    (A.filter P).card ≤ ∑ y ∈ S, f y := by
  have himage : (A.filter P).image g ⊆ S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact hmem x (Finset.mem_filter.1 hx).1
  have hsubinj : Set.InjOn g (A.filter P : Set α) := fun x hx y hy h =>
    hinj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hy).1 h
  calc
    _ = ∑ _x ∈ A.filter P, 1 := by simp
    _ ≤ ∑ x ∈ A.filter P, f (g x) := Finset.sum_le_sum (fun x hx =>
      hscore x (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx).2)
    _ = ∑ y ∈ (A.filter P).image g, f y := (Finset.sum_image hsubinj).symm
    _ ≤ ∑ y ∈ S, f y := Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun _ _ _ => Nat.zero_le _)

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℕ} {f e : ℕ → ℚ}

theorem matching_killRows_eq_sum (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (ha : Function.Injective a) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hReal : ∀ x, Realizes PS a b x (cert x))
    (P : ZMod p → ℕ → Prop) :
    ((killRows (p := p) a cert).filter (fun i => P (a i : ZMod p) (a i / p))).card =
      ∑ x, ((cert x).kr.filter (P x)).card := by
  have h := killCount_eq_sum a ha (fun x => (cert x).kr.filter (P x)) (by
    intro x d hd
    exact (hReal x).r_cov d ((hOk x).kr_sub (Finset.mem_filter.1 hd).1))
  have he : (Finset.univ.filter (fun i => a i / p ∈
      (cert (a i : ZMod p)).kr.filter (P (a i : ZMod p)))) =
      (killRows (p := p) a cert).filter (fun i => P (a i : ZMod p) (a i / p)) := by
    ext i
    simp only [killRows, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he] at h
  exact h

theorem matching_killCols_eq_sum (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (hb : Function.Injective b) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hReal : ∀ x, Realizes PS a b x (cert x))
    (P : ZMod p → ℕ → Prop) :
    ((killCols (p := p) b cert).filter (fun i => P (b i : ZMod p) (b i / p))).card =
      ∑ x, ((cert x).kc.filter (P x)).card := by
  have h := killCount_eq_sum b hb (fun x => (cert x).kc.filter (P x)) (by
    intro x d hd
    exact (hReal x).c_cov d ((hOk x).kc_sub (Finset.mem_filter.1 hd).1))
  have he : (Finset.univ.filter (fun i => b i / p ∈
      (cert (b i : ZMod p)).kc.filter (P (b i : ZMod p)))) =
      (killCols (p := p) b cert).filter (fun i => P (b i : ZMod p) (b i / p)) := by
    ext i
    simp only [killCols, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he] at h
  exact h

theorem lineMc_eq_one_of_mem (c : FibreCert) (w : RatFunc (ZMod p) × RatFunc (ZMod p))
    (d : ℕ) (hd : d ∈ c.kc) (hn : castV p (c.cload d) ≠ 0)
    (hV : castV p (c.cload d) ∈ Submodule.span (RatFunc (ZMod p)) {w}) :
    lineMc p c w = 1 := if_pos ⟨d, hd, hn, hV⟩

theorem lineMr_eq_one_of_single (c : FibreCert) (w : RatFunc (ZMod p) × RatFunc (ZMod p))
    (hsmall : c.kr.card ≤ 1) (d : ℕ) (hd : d ∈ c.kr)
    (horth : omegaL (castV p (c.rload d)) w = 0) : lineMr p c w = 1 := by
  apply if_pos
  intro k hk
  have he : k = d := (Finset.card_le_one.1 hsmall) k hk d hd
  simpa only [he] using horth

#print axioms card_filter_le_score
#print axioms matching_killRows_eq_sum
#print axioms lineMr_eq_one_of_single
end CatalanCore.Uniform.Content.RankProducer
