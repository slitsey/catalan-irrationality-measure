module
public import CatalanCore.Arith.Hybrid.TwoLevelFull
public import CatalanCore.Arith.Hybrid.LemmaE.Bridge
public import CatalanCore.Basic.ZModGood
@[expose] public section
open Finset Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # Reduction of `p`-integral polynomials into `𝔽_p(X)`

`redI f` is `phiP` of the (unique) integral lift of `f`, defined whenever all coefficients of `f`
are `p`-integral (`GLE p 0 f`).  It is a ring homomorphism on integral polynomials and is
constant on `Cng` classes.  This lets the T-route congruences (`Cng`, Gauss norms over `ℚ[X]`)
be transported to identities over `RatFunc (ZMod p)` without carrying lifts around. -/

section RedI
variable (p : ℕ) [Fact p.Prime]

lemma gle0_toQ (g : (LocRing p)[X]) : GLE p 0 (toQ p g) := by
  intro i
  simpa [toQ_coeff] using (g.coeff i).2

lemma exists_lift0 {f : ℚ[X]} (hf : GLE p 0 f) : ∃ g : (LocRing p)[X], toQ p g = f := by
  obtain ⟨g, hg⟩ := exists_lift p hf
  exact ⟨g, by simpa using hg⟩

open Classical in
/-- Reduction of an integral polynomial (junk value `0` for non-integral input). -/
noncomputable def redI (f : ℚ[X]) : RatFunc (ZMod p) :=
  if h : GLE p 0 f then phiP p (Classical.choose (exists_lift0 p h)) else 0

variable {p}

lemma redI_toQ (g : (LocRing p)[X]) : redI p (toQ p g) = phiP p g := by
  unfold redI
  rw [dif_pos (gle0_toQ p g)]
  have := Classical.choose_spec (exists_lift0 p (gle0_toQ p g))
  rw [toQ_injective p this]

lemma redI_eq {f : ℚ[X]} (hf : GLE p 0 f) {g : (LocRing p)[X]} (hg : toQ p g = f) :
    redI p f = phiP p g := by
  rw [← hg, redI_toQ]

lemma redI_add {f g : ℚ[X]} (hf : GLE p 0 f) (hg : GLE p 0 g) :
    redI p (f + g) = redI p f + redI p g := by
  obtain ⟨a, rfl⟩ := exists_lift0 p hf
  obtain ⟨b, rfl⟩ := exists_lift0 p hg
  rw [← map_add, redI_toQ, redI_toQ, redI_toQ, map_add]

lemma redI_mul {f g : ℚ[X]} (hf : GLE p 0 f) (hg : GLE p 0 g) :
    redI p (f * g) = redI p f * redI p g := by
  obtain ⟨a, rfl⟩ := exists_lift0 p hf
  obtain ⟨b, rfl⟩ := exists_lift0 p hg
  rw [← map_mul, redI_toQ, redI_toQ, redI_toQ, map_mul]

lemma redI_neg {f : ℚ[X]} (hf : GLE p 0 f) : redI p (-f) = - redI p f := by
  obtain ⟨a, rfl⟩ := exists_lift0 p hf
  rw [← map_neg, redI_toQ, redI_toQ, map_neg]

lemma redI_sub {f g : ℚ[X]} (hf : GLE p 0 f) (hg : GLE p 0 g) :
    redI p (f - g) = redI p f - redI p g := by
  obtain ⟨a, rfl⟩ := exists_lift0 p hf
  obtain ⟨b, rfl⟩ := exists_lift0 p hg
  rw [← map_sub, redI_toQ, redI_toQ, redI_toQ, map_sub]

lemma redI_zero : redI p 0 = 0 := by
  have := redI_toQ (p := p) 0
  simpa using this

lemma redI_one : redI p 1 = 1 := by
  have := redI_toQ (p := p) 1
  simpa using this

lemma redI_X : redI p (X : ℚ[X]) = rfX p := by
  have := redI_toQ (p := p) X
  rw [phiP_X] at this
  simpa [toQ] using this

lemma redI_C {x : ℚ} (hx : x ∈ LocRing p) : redI p (C x) = rfC p (red p x) := by
  have := redI_toQ (p := p) (C ⟨x, hx⟩)
  rw [phiP_C] at this
  simpa [toQ, redQ_apply, red] using this

lemma redI_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (hf : ∀ i ∈ s, GLE p 0 (f i)) :
    redI p (∑ i ∈ s, f i) = ∑ i ∈ s, redI p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using redI_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      redI_add (hf a (Finset.mem_insert_self _ _))
        (GLE.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Congruent integral polynomials have the same reduction. -/
lemma redI_cng {f g : ℚ[X]} (hf : GLE p 0 f) (hg : GLE p 0 g)
    (h : LemmaE.Cng p f g) : redI p f = redI p g := by
  obtain ⟨a, rfl⟩ := exists_lift0 p hf
  obtain ⟨b, rfl⟩ := exists_lift0 p hg
  rw [redI_toQ, redI_toQ, ← sub_eq_zero, ← map_sub, phiP_eq_zero_iff, C_dvd_iff_dvd_coeff]
  intro n
  have h1 : padicNorm p (((a - b).coeff n : LocRing p) : ℚ) < 1 := by
    have hgn : gn p (toQ p (a - b)) < 1 := by
      rw [map_sub]; exact h
    have := padic_coeff_le_gn (p := p) (toQ p (a - b)) n
    rw [toQ_coeff] at this
    exact_mod_cast lt_of_le_of_lt this hgn
  have h2 : redQ p ((a - b).coeff n) = 0 := by
    rw [redQ_apply]
    exact (LemmaE.padicNorm_lt_one_iff ((a - b).coeff n).2).1 h1
  exact (redQ_eq_zero_iff p _).1 h2

end RedI

#print axioms redI_add
#print axioms redI_mul
#print axioms redI_C
#print axioms redI_cng
end CatalanCore.Arith.Hybrid
