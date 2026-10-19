module

public import CatalanCore.Star.ThmLEntry
public import CatalanCore.Star.ThmLWeights
public import CatalanCore.Star.ThmLPoly

/-!
# Star.ThmLTerm: leading term of one summand of the entry formula
-/

@[expose] public section

open Finset Polynomial

namespace CatalanCore.Star.ThmL

lemma vsq_zeta {K : ℕ} (A : Finset (Fin K)) :
    vsq (fun a : Fin K => -(theta + ((a : ℕ) : LS))) A
      = ((vsq (fun a : Fin K => ((a : ℕ) : ℚ)) A : ℚ) : LS) := by
  unfold vsq
  rw [ratC, map_prod]
  apply prod_congr rfl; intro a _; rw [map_prod]
  apply prod_congr rfl; intro a' _
  simp only [map_pow, map_sub, map_natCast]; ring

lemma vsq_eps {r : ℕ} (e : Fin r → ℤ) (B : Finset (Fin r)) :
    vsq (fun b : Fin r => ((e b : ℤ) : LS)) B
      = ((vsq (fun b : Fin r => ((e b : ℤ) : ℚ)) B : ℚ) : LS) := by
  rw [ratC, ← vsq_map (HahnSeries.C : ℚ →+* LS) (fun b : Fin r => ((e b : ℤ) : ℚ)) B]
  congr 1
lemma hl_negOnePow (c : ℕ) : HasLead 0 ((-1 : ℚ) ^ c) ((-1 : LS) ^ c) := by
  have := (hasLead_intCast (-1)).pow c
  refine this.cast_eq (by simp) ?_ ?_ <;> simp

theorem term_lead {K r : ℕ} (m S : ℕ) (e : Fin r → ℤ) (A : Finset (Fin K)) (B : Finset (Fin r)) :
    HasLead (-(2 * m * A.card : ℤ) + 2 * K * B.card - 2 * A.card * B.card - A.card)
      ((-1) ^ B.card * (∏ a ∈ A, wQ K a) * (∏ b ∈ B, cQ m S (e b))
        * vsq (fun a : Fin K => ((a : ℕ) : ℚ)) A * vsq (fun b : Fin r => ((e b : ℤ) : ℚ)) B
        * (∏ b ∈ B, ((S : ℚ) - e b)))
      (entryVal (fun a => omegaN K m S theta a) (fun a : Fin K => -(theta + ((a : ℕ) : LS)))
        (fun b => gammaC K m S theta (e b)) (fun b => ((e b : ℤ) : LS)) ((S : ℕ) : LS) A B) := by
  have f1 := hl_negOnePow B.card
  have f2 := HasLead.prod A (fun a _ => hl_omega K m S theta rfl a)
  have f3 := HasLead.prod B (fun b _ => hl_gamma K m S theta rfl (e b))
  have f4 : HasLead 0 (vsq (fun a : Fin K => ((a : ℕ) : ℚ)) A)
      (vsq (fun a : Fin K => -(theta + ((a : ℕ) : LS))) A) := by
    rw [vsq_zeta]; exact hasLead_ratCast _
  have f5 : HasLead 0 (vsq (fun b : Fin r => ((e b : ℤ) : ℚ)) B)
      (vsq (fun b : Fin r => ((e b : ℤ) : LS)) B) := by
    rw [vsq_eps]; exact hasLead_ratCast _
  have hcross : ∀ a ∈ A, ∀ b ∈ B, HasLead (-2) 1
      ((-(theta + ((a : ℕ) : LS)) - ((e b : ℤ) : LS)) ^ 2) := by
    intro a _ b _
    have h : -(theta + ((a : ℕ) : LS)) - ((e b : ℤ) : LS)
        = -(theta + (((a : ℕ) : LS) + ((e b : ℤ) : LS))) := by ring
    rw [h]
    have := (hl_neg_theta_add (OrdGe.add (hasLead_natCast (a : ℕ)).1 (hasLead_intCast (e b)).1)).pow 2
    exact this.cast_eq (by norm_num) (by norm_num) rfl
  have f6 := HasLead.prod A (fun a ha => HasLead.prod B (fun b hb => hcross a ha b hb))
  have f7 := HasLead.prod A (fun a _ => show HasLead (-1) 1
      (((S : ℕ) : LS) - (-(theta + ((a : ℕ) : LS)))) by
    have h : ((S : ℕ) : LS) - (-(theta + ((a : ℕ) : LS)))
        = theta + (((a : ℕ) : LS) + ((S : ℕ) : LS)) := by ring
    rw [h]
    exact hasLead_theta_add_of_ordGe (OrdGe.add (hasLead_natCast (a : ℕ)).1 (hasLead_natCast S).1))
  have f8 := HasLead.prod B (fun b _ => show HasLead 0 ((S : ℚ) - e b)
      (((S : ℕ) : LS) - ((e b : ℤ) : LS)) by
    have := hasLead_ratCast ((S : ℚ) - e b)
    refine this.cast_eq rfl rfl ?_
    rw [ratC, map_sub, map_natCast, map_intCast])
  have := (((((f1.mul f2).mul f3).mul f4).mul f5).mul f6).mul f7 |>.mul f8
  unfold entryVal
  refine this.cast_eq ?_ ?_ ?_
  · simp; ring
  · simp
  · rfl

end CatalanCore.Star.ThmL
