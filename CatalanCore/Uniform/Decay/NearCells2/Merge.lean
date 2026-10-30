module

public import CatalanCore.Uniform.Decay.NearCells2.Defs

@[expose] public section
set_option Elab.async false

/-!
# Soundness of endpoint merging (lane D, package D6d)
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools

/-- The jet remainder of `(∑_{j<n} P_j s^j) Log (1 - q s)`. -/
noncomputable def remT (n : ℕ) (P : ℕ → ℂ) (q s : ℂ) : ℂ :=
  (∑ j ∈ range n, P j * s ^ j) * Complex.log (1 - q * s) - jet n P q s

theorem remT_add (n : ℕ) (P R : ℕ → ℂ) (q s : ℂ) :
    remT n (fun j => P j + R j) q s = remT n P q s + remT n R q s := by
  simp only [remT, jet, termJet, add_mul, Finset.sum_add_distrib, neg_add]
  ring

theorem remT_smul (n : ℕ) (w : ℝ) (P : ℕ → ℂ) (q s : ℂ) :
    remT n (fun j => (w : ℂ) * P j) q s = (w : ℂ) * remT n P q s := by
  have h1 : ∑ j ∈ range n, (w : ℂ) * P j * s ^ j = (w : ℂ) * ∑ j ∈ range n, P j * s ^ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : jet n (fun j => (w : ℂ) * P j) q s = (w : ℂ) * jet n P q s := by
    unfold jet termJet
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  unfold remT
  rw [h1, h2]; ring

theorem remT_congr (n : ℕ) {P P' : ℕ → ℂ} (h : ∀ j < n, P j = P' j) (q s : ℂ) :
    remT n P q s = remT n P' q s := by
  have h1 : ∑ j ∈ range n, P j * s ^ j = ∑ j ∈ range n, P' j * s ^ j :=
    Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]
  have h2 : jet n P q s = jet n P' q s := by
    unfold jet
    exact Finset.sum_congr rfl fun j hj => by
      unfold termJet; rw [h j (Finset.mem_range.1 hj)]
  unfold remT; rw [h1, h2]

theorem toC_czero : czero.toC = 0 := CQ.toC_zero

theorem ccoef_nil (j : ℕ) : ccoef [] j = czero := by simp [ccoef]

theorem ccoef_addC (a b : List CQ) (j : ℕ) :
    (ccoef (addC a b) j).toC = (ccoef a j).toC + (ccoef b j).toC := by
  induction a generalizing b j with
  | nil => simp [addC, ccoef_nil, toC_czero]
  | cons x xs ih =>
    cases b with
    | nil => simp [addC, ccoef_nil, toC_czero]
    | cons y ys =>
      cases j with
      | zero => simp [addC, ccoef, CQ.toC_add]
      | succ j => simpa [addC, ccoef] using ih ys j

theorem ccoef_scaleC (w : ℚ) (a : List CQ) (j : ℕ) :
    (ccoef (scaleC w a) j).toC = (w : ℂ) * (ccoef a j).toC := by
  induction a generalizing j with
  | nil => simp [scaleC, ccoef_nil, toC_czero]
  | cons x xs ih =>
    cases j with
    | zero => simp [scaleC, ccoef, CQ.toC_smul]
    | succ j => simpa [scaleC, ccoef] using ih j

/-- Semantic value of a term. -/
noncomputable def tmC (n : ℕ) (t : Tm) (s : ℂ) : ℂ :=
  remT n (fun j => (ccoef t.P j).toC) t.q.toC s

noncomputable def remSum (n : ℕ) (T : List Tm) (s : ℂ) : ℂ := (T.map fun t => tmC n t s).sum

theorem remSum_cons (n : ℕ) (t : Tm) (T : List Tm) (s : ℂ) :
    remSum n (t :: T) s = tmC n t s + remSum n T s := by
  simp [remSum]

theorem remSum_append (n : ℕ) (T T' : List Tm) (s : ℂ) :
    remSum n (T ++ T') s = remSum n T s + remSum n T' s := by
  simp [remSum]

theorem cqEq_toC {a b : CQ} (h : cqEq a b = true) : a.toC = b.toC := by
  simp only [cqEq, Bool.and_eq_true, decide_eq_true_eq] at h
  simp [CQ.toC, h.1, h.2]

theorem remSum_insTm (n : ℕ) (t : Tm) (T : List Tm) (s : ℂ) :
    remSum n (insTm t T) s = tmC n t s + remSum n T s := by
  induction T with
  | nil => simp [insTm, remSum]
  | cons u us ih =>
    unfold insTm
    split_ifs with hq
    · rw [remSum_cons, remSum_cons]
      have hq' := cqEq_toC hq
      have e : tmC n ⟨u.q, addC t.P u.P⟩ s = tmC n t s + tmC n u s := by
        unfold tmC
        simp only []
        rw [remT_congr n (P' := fun j => (ccoef t.P j).toC + (ccoef u.P j).toC)
          (fun j _ => ccoef_addC _ _ j), remT_add, hq']
      rw [e]; ring
    · rw [remSum_cons, remSum_cons, ih]; ring

theorem remSum_mergeAll (n : ℕ) (T : List Tm) (s : ℂ) :
    remSum n (mergeAll T) s = remSum n T s := by
  induction T with
  | nil => simp [mergeAll]
  | cons t ts ih => rw [mergeAll, remSum_insTm, remSum_cons, ih]

theorem remSum_scale (n : ℕ) (w : ℚ) (T : List Tm) (s : ℂ) :
    remSum n (T.map fun t => (⟨t.q, scaleC w t.P⟩ : Tm)) s = (w : ℂ) * remSum n T s := by
  induction T with
  | nil => simp [remSum]
  | cons t ts ih =>
    rw [List.map_cons, remSum_cons, remSum_cons, ih]
    have : tmC n ⟨t.q, scaleC w t.P⟩ s = (w : ℂ) * tmC n t s := by
      unfold tmC
      simp only []
      rw [remT_congr n (P' := fun j => ((w : ℝ) : ℂ) * (ccoef t.P j).toC)
        (fun j _ => by rw [ccoef_scaleC]; push_cast; rfl), remT_smul]
      push_cast; rfl
    rw [this]; ring

theorem norm_tmC_le (n : ℕ) (t : Tm) {h : ℚ} (hh : 0 ≤ h) (hr : rOf t.q h < 1) (s : ℂ)
    (hs : ‖s‖ ≤ (h : ℝ)) :
    ‖tmC n t s‖ ≤ (jbQ (ccoef t.P) n (rOf t.q h) h : ℝ) := by
  have hnn : 0 ≤ t.q.nsq * h ^ 2 :=
    mul_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (sq_nonneg _)
  have hn : ‖t.q.toC‖ * (h : ℝ) ≤ (rOf t.q h : ℝ) :=
    norm_le_of_nsq hh (sqrtUp_nonneg _) (le_sqrtUp_sq hnn)
  have hrR : (rOf t.q h : ℝ) < 1 := by exact_mod_cast hr
  have h1 := norm_jet_remainder_le n (fun j => (ccoef t.P j).toC) hs (q := t.q.toC) (by linarith)
  have h2 := jetBound_le_jbQ (q := t.q.toC) (ccoef t.P) n hh hn hr
  exact h1.trans h2

theorem norm_remSum_le (n : ℕ) {h : ℚ} (T : List Tm) (hT : tmOk h T = true) (s : ℂ)
    (hs : ‖s‖ ≤ (h : ℝ)) : ‖remSum n T s‖ ≤ (tmErr n h T : ℝ) := by
  simp only [tmOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hT
  obtain ⟨hh, hall⟩ := hT
  induction T with
  | nil => simp [remSum, tmErr]
  | cons t ts ih =>
    rw [remSum_cons]
    have h1 := norm_tmC_le n t hh (by simpa using hall t (by simp)) s hs
    have h2 := ih (fun u hu => hall u (by simp [hu]))
    refine (norm_add_le _ _).trans ?_
    have : tmErr n h (t :: ts) = jbQ (ccoef t.P) n (rOf t.q h) h + tmErr n h ts := by
      simp [tmErr]
    rw [this]; push_cast
    linarith

end CatalanCore.Uniform.Decay.NearCells
