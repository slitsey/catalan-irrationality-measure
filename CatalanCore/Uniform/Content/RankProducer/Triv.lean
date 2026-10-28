module

public import CatalanCore.Uniform.Content.RankProducer.Build

@[expose] public section

/-!
# The trivial certificate (lane H15)

Kills nothing, so it is valid for EVERY fibre: `trivCert` realises the actual fibre of any
Loewner matrix.  Mixed assignments (typed certificates on classified fibres, trivial ones on the
rest, e.g. fibres touched by deletions) are the intended use; with trivial certificates only,
`RankMember` is the natural price `2 h`.
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Uniform CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.RankProducer

open scoped Classical

/-- Identity-matrix entries. -/
def delta (d e : ℕ) : ℚ := if d = e then 1 else 0

/-- A certificate that kills nothing. -/
def FibreCert.triv (R C : Finset ℕ) (lf ee : ℕ → ℚ) : FibreCert where
  R := R
  C := C
  lf := lf
  ee := ee
  Lq := delta
  Lq' := delta
  Pq := delta
  Pq' := delta
  kr := ∅
  kc := ∅

theorem sum_delta (R : Finset ℕ) {d e : ℕ} (hd : d ∈ R) (he : e ∈ R) :
    ∑ f ∈ R, delta d f * delta f e = delta d e := by
  unfold delta
  by_cases h : d = e
  · subst h; simp [hd]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun f _ => ?_
    by_cases h1 : d = f <;> by_cases h2 : f = e <;> simp_all

theorem FibreCert.triv_ok (R C : Finset ℕ) (lf ee : ℕ → ℚ) : (FibreCert.triv R C lf ee).Ok where
  hLL := fun d hd e he => sum_delta R hd he
  hPP := fun d hd e he => sum_delta C hd he
  kr_sub := Finset.empty_subset _
  kc_sub := Finset.empty_subset _
  hrow := fun d hd => absurd hd (Finset.notMem_empty _)
  hcol := fun d _ e he => absurd he (Finset.notMem_empty _)

theorem delta_mem {p : ℕ} [Fact p.Prime] (d e : ℕ) : delta d e ∈ S p := by
  unfold delta
  split_ifs
  · exact (S p).one_mem
  · exact (S p).zero_mem

theorem FibreCert.triv_integral {p : ℕ} [Fact p.Prime] (R C : Finset ℕ) (lf ee : ℕ → ℚ) :
    (FibreCert.triv R C lf ee).Integral p where
  lq := fun d _ e _ => ⟨delta_mem d e, delta_mem d e⟩
  pq := fun d _ e _ => ⟨delta_mem d e, delta_mem d e⟩

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ} {f e : ℕ → ℚ}

/-- The trivial certificate of the actual fibre `x`. -/
noncomputable def trivCert (PS : PoleSplit p B f e) (a b : ι → ℕ) (x : ZMod p) : FibreCert :=
  FibreCert.triv ((Finset.univ.filter fun i => (a i : ZMod p) = x).image fun i => a i / p)
    ((Finset.univ.filter fun j => (b j : ZMod p) = x).image fun j => b j / p)
    (fun d => PS.Lf (x.val + p * d)) (fun d => PS.E (x.val + p * d))

theorem node_eq_val {n : ℕ} {x : ZMod p} (h : (n : ZMod p) = x) : n = x.val + p * (n / p) := by
  have hv : x.val = n % p := by rw [← h, ZMod.val_natCast]
  have := Nat.div_add_mod n p
  omega

theorem trivCert_realizes (PS : PoleSplit p B f e) (a b : ι → ℕ) (x : ZMod p) :
    Realizes PS a b x (trivCert PS a b x) where
  r_mem := fun i hi => Finset.mem_image.2 ⟨i, by simp [hi], rfl⟩
  r_cov := fun d hd => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
    exact ⟨i, by simpa using hi, rfl⟩
  c_mem := fun j hj => Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩
  c_cov := fun d hd => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hd
    exact ⟨j, by simpa using hj, rfl⟩
  lf_r := fun i hi => by
    show PS.Lf (a i) = PS.Lf (x.val + p * (a i / p))
    rw [← node_eq_val hi]
  lf_c := fun j hj => by
    show PS.Lf (b j) = PS.Lf (x.val + p * (b j / p))
    rw [← node_eq_val hj]
  ee_r := fun i hi => by
    show PS.E (a i) = PS.E (x.val + p * (a i / p))
    rw [← node_eq_val hi]

theorem killRows_triv (PS : PoleSplit p B f e) (a b : ι → ℕ) :
    killRows (p := p) a (trivCert PS a b) = ∅ := by
  ext i; simp [killRows, trivCert, FibreCert.triv]

theorem killCols_triv (PS : PoleSplit p B f e) (a b : ι → ℕ) :
    killCols (p := p) b (trivCert PS a b) = ∅ := by
  ext i; simp [killCols, trivCert, FibreCert.triv]


section Member

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ι' : Type} [Fintype ι'] [DecidableEq ι']

/-- The kill-nothing member: valid whenever the band hypotheses hold; price `≤ 2 h`. -/
noncomputable def RankMember.triv (Fr : Frame) (u q : Fin Fr.d → ℕ) (common : ι' → ℕ)
    (xs ys : κ → ℕ) (T : Finset ι') (p : ℕ) [Fact p.Prime] (B : ℕ)
    (hcoef : ∀ j, (frameDigamma Fr u q).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (frameDigamma Fr u q).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2)
    (hB : B < p ^ 2) (ha : ∀ i, memberRows common xs T i ≤ B)
    (hb : ∀ j, memberCols common ys T j ≤ B)
    (hia : Function.Injective (memberRows common xs T))
    (hib : Function.Injective (memberCols common ys T)) :
    RankMember Fr u q common xs ys T p :=
  RankMember.ofExact Fr u q common xs ys T p B hcoef hpq hp3 hbd hB ha hb hia hib
    (trivCert ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
      (memberRows common xs T) (memberCols common ys T))
    (fun x => FibreCert.triv_ok _ _ _ _) (fun x => FibreCert.triv_integral _ _ _ _)
    (fun x => trivCert_realizes _ _ _ x)
    (by rw [killRows_triv, killCols_triv]) ⊥

/-- Every `RankMember` is priced at most the natural `2 h`. -/
theorem RankMember.price_le_two_mul {Fr : Frame} {u q : Fin Fr.d → ℕ} {common : ι' → ℕ}
    {xs ys : κ → ℕ} {T : Finset ι'} {p : ℕ} [Fact p.Prime] (M : RankMember Fr u q common xs ys T p) :
    M.price ≤ 2 * Fintype.card (T ⊕ κ) := by
  unfold RankMember.price
  exact le_trans (le_trans (Nat.sub_le _ _) (Nat.add_le_add_left (Nat.sub_le _ _) _)) (by omega)

end Member

end CatalanCore.Uniform.Content.RankProducer
