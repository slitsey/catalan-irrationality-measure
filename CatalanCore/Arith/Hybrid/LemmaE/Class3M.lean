module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3L

@[expose] public section

/-!
# Lemma E, class 3: the dual value `∑u + ∑v = 2 r + m`
-/

open Finset

namespace CatalanCore.Arith.Hybrid

section

variable {o p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

variable (S : ESetup3 o p r m k1)

include S

lemma sum_wr_C : ∑ c : Fin r, wr p r m (c : ℕ) = Fintype.card (Pt3 p r m) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun c : Fin r => isCz p r m (c : ℕ))]
  have h1 : ∑ w : {c : Fin r // isCz p r m (c : ℕ)}, wr p r m (w.1 : ℕ) = 0 :=
    Finset.sum_eq_zero fun w _ => wr_Wt w
  have h2 : ∑ c : {c : Fin r // ¬ isCz p r m (c : ℕ)}, wr p r m (c.1 : ℕ) =
      Fintype.card (Pt3 p r m) := by
    rw [Finset.sum_congr rfl (fun c _ => wr_Pt c)]
    simp
  rw [h1, h2, zero_add]

lemma sum_wc_C : ∑ c : Fin r, wc p r m (c : ℕ) =
    Fintype.card (Pt3 p r m) + 2 * Fintype.card (Wt3 p r m) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun c : Fin r => isCz p r m (c : ℕ))]
  have h1 : ∑ w : {c : Fin r // isCz p r m (c : ℕ)}, wc p r m (w.1 : ℕ) =
      2 * Fintype.card (Wt3 p r m) := by
    rw [Finset.sum_congr rfl (fun w _ => wc_Wt w)]
    simp [mul_comm]
  have h2 : ∑ c : {c : Fin r // ¬ isCz p r m (c : ℕ)}, wc p r m (c.1 : ℕ) =
      Fintype.card (Pt3 p r m) := by
    rw [Finset.sum_congr rfl (fun c _ => wc_Pt c)]
    simp
  rw [h1, h2]; ring

/-- **The dual value of the class-3 potentials is `2r + m`.** -/
lemma wrc_sum : ∑ a : Fin r ⊕ Fin m, wr p r m (Frame.hybRow r m a) +
    ∑ b : Fin r ⊕ Fin m, wc p r m (Frame.hybCol r m b) = 2 * r + m := by
  have hN := S.hN; have hpr := S.hpr
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hz1 : ∑ i : Fin m, wr p r m (Frame.hybRow r m (Sum.inr i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact wr_zone (show r ≤ r + 2 * (i : ℕ) by omega)
  have hz2 : ∑ i : Fin m, wc p r m (Frame.hybCol r m (Sum.inr i)) = m := by
    have : ∀ i : Fin m, wc p r m (Frame.hybCol r m (Sum.inr i)) = 1 := fun i =>
      wc_zone (show r ≤ r + 2 * (i : ℕ) + 1 by omega)
    simp [this]
  have hc : ∀ c : Fin r, wr p r m (Frame.hybRow r m (Sum.inl c)) = wr p r m (c : ℕ) := fun c => rfl
  have hc' : ∀ c : Fin r, wc p r m (Frame.hybCol r m (Sum.inl c)) = wc p r m (c : ℕ) := fun c => rfl
  simp only [hc, hc', hz1, hz2, sum_wr_C S, sum_wc_C S]
  have := card_Pt_Wt S
  have h2 := card_Wt S
  omega

end

end CatalanCore.Arith.Hybrid
