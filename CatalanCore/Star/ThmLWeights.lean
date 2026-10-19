module

public import CatalanCore.Star.ThmLLead
public import CatalanCore.Star.Defs

/-!
# Star.ThmLWeights: leading terms of the pencil weights over `LS = ℚ((1/θ))`

With `θ = theta` (order `-1`), the node `ζ_a = -(θ+a)`, the node weight `ω_a` (θ-degree `2m`,
lead `1/π_a²`) and the column weight `γ_j` (θ-degree `-2K`, lead `Π_Z(j)`).
-/

@[expose] public section

open Finset

namespace CatalanCore.Star.ThmL

/-- `π_a` as a rational. -/
def piaQ (K : ℕ) (a : Fin K) : ℚ := ∏ b ∈ univ.erase a, (((b : ℕ) : ℚ) - ((a : ℕ) : ℚ))

/-- Rational node weight `1/π_a²`. -/
def wQ (K : ℕ) (a : Fin K) : ℚ := 1 / piaQ K a ^ 2

/-- `Π_Z(j)` as a rational. -/
def cQ (m S : ℕ) (j : ℤ) : ℚ := ∏ i ∈ range (2 * m), ((j : ℚ) - ((S + 1 + i : ℕ) : ℚ))

lemma piaQ_ne_zero (K : ℕ) (a : Fin K) : piaQ K a ≠ 0 := by
  unfold piaQ
  rw [Finset.prod_ne_zero_iff]
  intro b hb
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  intro h
  apply hba
  have : ((b : ℕ) : ℚ) = ((a : ℕ) : ℚ) := by linarith
  exact Fin.ext (by exact_mod_cast this)

lemma ratC (q : ℚ) : (q : LS) = HahnSeries.C q := by
  simpa using (map_ratCast (HahnSeries.C : ℚ →+* LS) q).symm

lemma pia_eq (K : ℕ) (a : Fin K) : pia (F := LS) K a = (piaQ K a : LS) := by
  unfold pia piaQ
  rw [ratC, map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [map_sub, map_natCast]

lemma PiZ_int_eq (m S : ℕ) (j : ℤ) : PiZ (F := LS) m S (j : LS) = (cQ m S j : LS) := by
  unfold PiZ cQ
  rw [ratC, map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [map_sub, map_natCast, map_intCast]

lemma hl_neg_theta_add {c : LS} (hc : OrdGe 0 c) : HasLead (-1) (-1) (-(theta + c)) := by
  simpa using (hasLead_theta_add_of_ordGe hc).neg

/-- node: `ζ_a = -(θ + a)`. -/
lemma hl_zeta {K : ℕ} (a : Fin K) : HasLead (-1) (-1) (-(theta + ((a : ℕ) : LS))) :=
  hl_neg_theta_add (hasLead_natCast _).1

/-- `Π_Z(ζ_a)` has θ-degree `2m` and lead `1`. -/
lemma hl_PiZ_zeta (K m S : ℕ) (a : Fin K) :
    HasLead (-(2 * m : ℤ)) 1 (PiZ (F := LS) m S (-(theta + ((a : ℕ) : LS)))) := by
  unfold PiZ
  have h : ∀ i ∈ range (2 * m), HasLead (-1) (-1)
      (-(theta + ((a : ℕ) : LS)) - ((S + 1 + i : ℕ) : LS)) := by
    intro i _
    have : -(theta + ((a : ℕ) : LS)) - ((S + 1 + i : ℕ) : LS)
        = -(theta + (((a : ℕ) : LS) + ((S + 1 + i : ℕ) : LS))) := by ring
    rw [this]
    refine hl_neg_theta_add ?_
    have h1 := (hasLead_natCast (a : ℕ)).1
    have h2 := (hasLead_natCast (S + 1 + i)).1
    simpa using OrdGe.add h1 h2
  have := HasLead.prod (range (2 * m)) h
  refine this.cast_eq ?_ ?_ rfl
  · simp
  · rw [Finset.prod_const, card_range, show (-1 : ℚ) ^ (2 * m) = 1 by simp [pow_mul]]

/-- node weight `ω_a`. -/
lemma hl_omega (K m S : ℕ) (θ : LS) (hθ : θ = theta) (a : Fin K) :
    HasLead (-(2 * m : ℤ)) (wQ K a) (omegaN K m S θ a) := by
  subst hθ
  unfold omegaN
  have hp : HasLead 0 (piaQ K a ^ 2) (pia (F := LS) K a ^ 2) := by
    rw [pia_eq]
    simpa using (hasLead_ratCast (piaQ K a)).pow 2
  have := (hl_PiZ_zeta K m S a).div hp (pow_ne_zero 2 (piaQ_ne_zero K a))
  refine this.cast_eq (by simp) ?_ rfl
  simp [wQ]

/-- column weight `γ_j` has order `2K` (θ-degree `-2K`) with lead `Π_Z(j)`. -/
lemma hl_gamma (K m S : ℕ) (θ : LS) (hθ : θ = theta) (j : ℤ) :
    HasLead (2 * K : ℤ) (cQ m S j) (gammaC K m S θ j) := by
  subst hθ
  unfold gammaC
  have hnum : HasLead 0 (cQ m S j) (PiZ (F := LS) m S (j : LS)) := by
    rw [PiZ_int_eq]; exact hasLead_ratCast _
  have hden1 : ∀ a ∈ (univ : Finset (Fin K)), HasLead (-1) 1
      (theta + ((a : ℕ) : LS) + (j : LS)) := by
    intro a _
    rw [add_assoc]
    refine hasLead_theta_add_of_ordGe ?_
    simpa using OrdGe.add (hasLead_natCast (a : ℕ)).1 (hasLead_intCast j).1
  have hden := HasLead.prod univ hden1
  have hden2 := hden.pow 2
  have := hnum.div hden2 (by simp)
  refine this.cast_eq ?_ ?_ rfl
  · simp
  · simp

end CatalanCore.Star.ThmL
