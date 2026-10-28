module

public import CatalanCore.Uniform.Content.RankProducer.Cert

@[expose] public section

/-!
# `BlockKernel` from one certificate per fibre (lane H15)
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.RankProducer

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ℕ} {f e : ℕ → ℚ}

lemma liftQ_sum_mul {α : Type*} [Fintype α] (u v : α → ℚ) (hu : ∀ l, u l ∈ S p)
    (hv : ∀ l, v l ∈ S p) :
    ∑ l, liftQ p (u l) * liftQ p (v l) = liftQ p (∑ l, u l * v l) := by
  rw [liftQ_sum _ _ (fun l _ => (S p).mul_mem (hu l) (hv l))]
  exact Finset.sum_congr rfl fun l _ => (liftQ_mul (hu l) (hv l)).symm

/-- The digit of a fibre element. -/
def dig (a : ι → ℕ) (p : ℕ) {x : ZMod p} (t : TrOf a p x) : ℕ := a t.1 / p

lemma dig_inj {a : ι → ℕ} (ha : Function.Injective a) (x : ZMod p) :
    Function.Injective (dig a p (x := x)) := by
  intro t t' h
  apply Subtype.ext
  apply ha
  exact node_eq_of_digit (t.2.trans t'.2.symm) h

/-- Sum over a fibre as a sum over digits. -/
lemma sum_fibre {a : ι → ℕ} (ha : Function.Injective a) (x : ZMod p) (R : Finset ℕ)
    (hmem : ∀ i, (a i : ZMod p) = x → a i / p ∈ R)
    (hcov : ∀ d ∈ R, ∃ i, (a i : ZMod p) = x ∧ a i / p = d)
    {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ l : TrOf a p x, g (dig a p l) = ∑ d ∈ R, g d := by
  refine sum_digits (dig a p) R (dig_inj ha x) (fun d => ⟨fun hd => ?_, fun ⟨l, hl⟩ => ?_⟩) g
  · obtain ⟨i, hi, hid⟩ := hcov d hd
    exact ⟨⟨i, hi⟩, hid⟩
  · rw [← hl]; exact hmem l.1 l.2

variable (PS : PoleSplit p B f e) (a b : ι → ℕ) (hd : DigitHyp p B a b)
  (ha : Function.Injective a) (hb : Function.Injective b)
  (cert : ZMod p → FibreCert)

/-- Local blocks of a certificate, on the fibre elements. -/
noncomputable def locMat {α : Type*} (dg : α → ℕ) (M : ℕ → ℕ → ℚ) : Matrix α α (LocRing p) :=
  Matrix.of fun s t => liftQ p (M (dg s) (dg t))

include hd in
lemma Kc_mem {x : ZMod p} {c : FibreCert} (hR : Realizes PS a b x c) {i j : ι}
    (hi : (a i : ZMod p) = x) (hj : (b j : ZMod p) = x) : c.Kc (a i / p) (b j / p) ∈ S p := by
  rw [← Kq_eq_Kc hR hi hj]; exact PS.Kq_mem hd i j


lemma locMat_mul_inv {α : Type*} [Fintype α] [DecidableEq α] (dg : α → ℕ) (R : Finset ℕ)
    (hinj : Function.Injective dg) (hR : ∀ d, d ∈ R ↔ ∃ l, dg l = d) (M N : ℕ → ℕ → ℚ)
    (hM : ∀ d ∈ R, ∀ e ∈ R, M d e ∈ S p) (hN : ∀ d ∈ R, ∀ e ∈ R, N d e ∈ S p)
    (h : ∀ d ∈ R, ∀ e ∈ R, ∑ f ∈ R, M d f * N f e = if d = e then 1 else 0) :
    locMat (p := p) dg M * locMat (p := p) dg N = 1 := by
  have hmem : ∀ l, dg l ∈ R := fun l => (hR _).2 ⟨l, rfl⟩
  ext s t
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [locMat, Matrix.of_apply]
  rw [liftQ_sum_mul (fun l => M (dg s) (dg l)) (fun l => N (dg l) (dg t))
    (fun l => hM _ (hmem s) _ (hmem l)) (fun l => hN _ (hmem l) _ (hmem t))]
  rw [sum_digits dg R hinj hR (fun f => M (dg s) f * N f (dg t)), h _ (hmem s) _ (hmem t)]
  by_cases hst : s = t
  · subst hst; simp [liftQ_one]
  · have : dg s ≠ dg t := fun e => hst (hinj e)
    simp [this, hst, liftQ_zero]

variable {PS a b}

include hd ha hb in
lemma triple_entry {x : ZMod p} {c : FibreCert} (hR : Realizes PS a b x c) (hI : c.Integral p)
    (t : TrOf a p x) (u : TrOf b p x) :
    (locMat (p := p) (dig a p (x := x)) c.Lq * localK (erOf a p) (erOf b p) (PS.K a b) x *
        locMat (p := p) (dig b p (x := x)) c.Pq) t u =
      liftQ p (c.LKP (dig a p t) (dig b p u)) := by
  have hrm : ∀ l : TrOf a p x, dig a p l ∈ c.R := fun l => hR.r_mem l.1 l.2
  have hcm : ∀ m : TrOf b p x, dig b p m ∈ c.C := fun m => hR.c_mem m.1 m.2
  have hK : ∀ (l : TrOf a p x) (m : TrOf b p x),
      PS.K a b l.1 m.1 = liftQ p (c.Kc (dig a p l) (dig b p m)) := by
    intro l m
    simp only [PoleSplit.K, Matrix.of_apply]
    rw [Kq_eq_Kc hR l.2 m.2]; rfl
  have hKm : ∀ (l : TrOf a p x) (m : TrOf b p x), c.Kc (dig a p l) (dig b p m) ∈ S p :=
    fun l m => Kc_mem PS a b hd hR l.2 m.2
  have hL : ∀ (l : TrOf a p x), c.Lq (dig a p t) (dig a p l) ∈ S p :=
    fun l => (hI.lq _ (hrm t) _ (hrm l)).1
  have hP : ∀ (m : TrOf b p x), c.Pq (dig b p m) (dig b p u) ∈ S p :=
    fun m => (hI.pq _ (hcm m) _ (hcm u)).1
  simp only [Matrix.mul_apply, locMat, localK, Matrix.of_apply, erOf_symm]
  have h1 : ∀ m : TrOf b p x,
      (∑ l : TrOf a p x, liftQ p (c.Lq (dig a p t) (dig a p l)) * PS.K a b l.1 m.1) *
        liftQ p (c.Pq (dig b p m) (dig b p u)) =
      liftQ p ((∑ l : TrOf a p x, c.Lq (dig a p t) (dig a p l) * c.Kc (dig a p l) (dig b p m)) *
        c.Pq (dig b p m) (dig b p u)) := by
    intro m
    have e : (∑ l : TrOf a p x, liftQ p (c.Lq (dig a p t) (dig a p l)) * PS.K a b l.1 m.1) =
        ∑ l : TrOf a p x, liftQ p (c.Lq (dig a p t) (dig a p l)) *
          liftQ p (c.Kc (dig a p l) (dig b p m)) :=
      Finset.sum_congr rfl fun l _ => by rw [hK l m]
    rw [e, liftQ_sum_mul (fun l => c.Lq (dig a p t) (dig a p l))
      (fun l => c.Kc (dig a p l) (dig b p m)) hL (fun l => hKm l m),
      ← liftQ_mul ((S p).sum_mem fun l _ => (S p).mul_mem (hL l) (hKm l m)) (hP m)]
  rw [Finset.sum_congr rfl fun m _ => h1 m]
  have h2 : ∀ m : TrOf b p x, ((∑ l : TrOf a p x, c.Lq (dig a p t) (dig a p l) *
      c.Kc (dig a p l) (dig b p m)) * c.Pq (dig b p m) (dig b p u)) ∈ S p :=
    fun m => (S p).mul_mem ((S p).sum_mem fun l _ => (S p).mul_mem (hL l) (hKm l m)) (hP m)
  rw [← liftQ_sum _ _ (fun m _ => h2 m)]
  congr 1
  have e1 : ∀ g : ℕ, ∑ l : TrOf a p x, c.Lq (dig a p t) (dig a p l) * c.Kc (dig a p l) g =
      ∑ f ∈ c.R, c.Lq (dig a p t) f * c.Kc f g := fun g =>
    sum_fibre ha x c.R hR.r_mem hR.r_cov (fun f => c.Lq (dig a p t) f * c.Kc f g)
  simp_rw [e1]
  rw [sum_fibre hb x c.C hR.c_mem hR.c_cov
    (fun g => (∑ f ∈ c.R, c.Lq (dig a p t) f * c.Kc f g) * c.Pq g (dig b p u))]
  unfold FibreCert.LKP
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_mul]

end CatalanCore.Uniform.Content.RankProducer
