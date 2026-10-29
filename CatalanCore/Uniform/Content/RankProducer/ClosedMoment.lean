import CatalanCore.Uniform.Content.RankProducer.Cert
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
set_option Elab.async false

/-! # The moment lemma (Lemma 3 of C2/PAPER.md), existence route (lane C2L)

For a palette `lf` and an arbitrary diagonal `ee`, the Loewner-type block `kcf lf ee` on row digits
`0..k` and column digits `0..k-1` has a left kernel vector `u` whose moment pair
`(Σ u, Σ lf · u)` is nonzero (`exists_normal`, normalised so that `u i0 = 1`).

Proof (support descent, NOTES P1): the displacement identity `d K(d,e) = e K(d,e) + L_d - L_e`
shows that `(d - c) u_d` is again a kernel vector when the moment of `u` vanishes; this strictly
shrinks the support, and a kernel vector with one-point support has moment `u_i (1, L_i) ≠ 0`.
No nonsingularity and no values of the palette enter.
-/

namespace CatalanCore.Uniform.Content.RankProducer
open Finset

/-- The Loewner-type block entry with palette `lf` and diagonal `-ee` (`FibreCert.Kc`). -/
def kcf (lf ee : ℕ → ℚ) (d e : ℕ) : ℚ :=
  if d = e then -ee d else (lf e - lf d) / ((e : ℚ) - d)

theorem FibreCert.Kc_eq_kcf (c : FibreCert) : c.Kc = kcf c.lf c.ee := rfl

theorem kcf_symm (lf ee : ℕ → ℚ) (d e : ℕ) : kcf lf ee d e = kcf lf ee e d := by
  unfold kcf
  by_cases h : d = e
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), ← neg_div_neg_eq]
    congr 1 <;> ring

/-- The displacement identity (2.1), entrywise. -/
theorem kcf_disp (lf ee : ℕ → ℚ) (d e : ℕ) :
    (d : ℚ) * kcf lf ee d e = (e : ℚ) * kcf lf ee d e + lf d - lf e := by
  unfold kcf
  by_cases h : d = e
  · subst h; simp
  · rw [if_neg h]
    have hde : ((e : ℚ) - d) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast Ne.symm h)
    have hX : (lf e - lf d) / ((e : ℚ) - d) * ((e : ℚ) - d) = lf e - lf d :=
      div_mul_cancel₀ _ hde
    linear_combination (-1 : ℚ) * hX

/-- `u` is a left kernel vector of the `(k+1) × k` block. -/
def InKer (lf ee : ℕ → ℚ) (k : ℕ) (u : ℕ → ℚ) : Prop :=
  ∀ e ∈ range k, ∑ d ∈ range (k + 1), u d * kcf lf ee d e = 0

/-- The moment pair `(Σ u, Σ lf · u)` (the load of `u`). -/
def mom (lf : ℕ → ℚ) (k : ℕ) (u : ℕ → ℚ) : ℚ × ℚ :=
  (∑ d ∈ range (k + 1), u d, ∑ d ∈ range (k + 1), lf d * u d)

/-- A kernel vector with vanishing moment stays in the kernel after multiplication by `d - c`. -/
theorem inKer_shift {lf ee : ℕ → ℚ} {k : ℕ} {u : ℕ → ℚ} (hu : InKer lf ee k u)
    (hm : mom lf k u = 0) (c : ℚ) : InKer lf ee k (fun d : ℕ => ((d : ℚ) - c) * u d) := by
  intro e he
  have h1 := hu e he
  have hm1 : ∑ d ∈ range (k + 1), u d = 0 := congrArg Prod.fst hm
  have hm2 : ∑ d ∈ range (k + 1), lf d * u d = 0 := congrArg Prod.snd hm
  have hterm : ∀ d : ℕ, ((d : ℚ) - c) * u d * kcf lf ee d e =
      ((e : ℚ) - c) * (u d * kcf lf ee d e) + lf d * u d - lf e * u d := by
    intro d
    have := kcf_disp lf ee d e
    linear_combination (u d) * this
  rw [Finset.sum_congr rfl (fun d _ => hterm d), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, h1, hm2, hm1]
  ring

/-- The block has a nonzero left kernel vector (`k + 1` rows in a `k`-dimensional space). -/
theorem exists_inKer_ne (lf ee : ℕ → ℚ) (k : ℕ) :
    ∃ u : ℕ → ℚ, InKer lf ee k u ∧ ∃ d ∈ range (k + 1), u d ≠ 0 := by
  let v : Fin (k + 1) → (Fin k → ℚ) := fun i e => kcf lf ee i e
  have hnot : ¬ LinearIndependent ℚ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fin_fun] at this
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
  refine ⟨fun d => if h : d < k + 1 then g ⟨d, h⟩ else 0, ?_, i, Finset.mem_range.2 i.2, ?_⟩
  · intro e he
    have he' := Finset.mem_range.1 he
    have hge := congrFun hg ⟨e, he'⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v, Fin.val_mk] at hge
    rw [Finset.sum_range (fun d => (if h : d < k + 1 then g ⟨d, h⟩ else 0) * kcf lf ee d e)]
    simpa only [Fin.is_lt, dite_true, Fin.eta, Fin.val_mk] using hge
  · simpa only [Fin.is_lt, dite_true, Fin.eta] using hi

/-- **Lemma 3.** A left kernel vector with nonzero moment exists. -/
theorem exists_inKer_mom (lf ee : ℕ → ℚ) (k : ℕ) :
    ∃ u : ℕ → ℚ, InKer lf ee k u ∧ mom lf k u ≠ 0 := by
  classical
  suffices H : ∀ n, ∀ u : ℕ → ℚ, InKer lf ee k u →
      ((range (k + 1)).filter (fun d => u d ≠ 0)).Nonempty →
      ((range (k + 1)).filter (fun d => u d ≠ 0)).card ≤ n →
      ∃ v : ℕ → ℚ, InKer lf ee k v ∧ mom lf k v ≠ 0 by
    obtain ⟨u, hu, d, hd, hud⟩ := exists_inKer_ne lf ee k
    exact H _ u hu ⟨d, Finset.mem_filter.2 ⟨hd, hud⟩⟩ le_rfl
  intro n
  induction n with
  | zero =>
    intro u _ hne hc
    have := Finset.card_pos.2 hne
    omega
  | succ n ih =>
    intro u hu hne hc
    by_cases hm : mom lf k u = 0
    · obtain ⟨i', hi'⟩ := hne
      have hs : ∑ d ∈ range (k + 1), u d = 0 := congrArg Prod.fst hm
      have hex : ∃ i ∈ (range (k + 1)).filter (fun d => u d ≠ 0), i ≠ i' := by
        by_contra hno
        push_neg at hno
        have hsum : ∑ d ∈ range (k + 1), u d = u i' := by
          refine Finset.sum_eq_single_of_mem i' (Finset.mem_filter.1 hi').1 ?_
          intro b hb hbi
          by_contra hub
          exact hbi (hno b (Finset.mem_filter.2 ⟨hb, hub⟩))
        exact (Finset.mem_filter.1 hi').2 (hsum ▸ hs)
      obtain ⟨i, hi, hii⟩ := hex
      have hv := inKer_shift hu hm (i' : ℚ)
      have hsub : (range (k + 1)).filter (fun d : ℕ => ((d : ℚ) - i') * u d ≠ 0) ⊆
          ((range (k + 1)).filter (fun d => u d ≠ 0)).erase i' := by
        intro d hd
        obtain ⟨hd1, hd2⟩ := Finset.mem_filter.1 hd
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨hd1, ?_⟩⟩
        · rintro rfl
          exact hd2 (by simp)
        · intro h0
          exact hd2 (by rw [h0, mul_zero])
      have hvi : i ∈ (range (k + 1)).filter (fun d : ℕ => ((d : ℚ) - i') * u d ≠ 0) := by
        obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
        refine Finset.mem_filter.2 ⟨hi1, mul_ne_zero (sub_ne_zero.2 ?_) hi2⟩
        exact_mod_cast hii
      refine ih _ hv ⟨i, hvi⟩ ?_
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hi'] at h1
      omega
    · exact ⟨u, hu, hm⟩

/-- **Lemma 3, normalised.** A kernel vector with nonzero moment and a unit coordinate. -/
theorem exists_normal (lf ee : ℕ → ℚ) (k : ℕ) :
    ∃ u : ℕ → ℚ, ∃ i0 ∈ range (k + 1), u i0 = 1 ∧ InKer lf ee k u ∧ mom lf k u ≠ 0 := by
  obtain ⟨u, hu, hm⟩ := exists_inKer_mom lf ee k
  have hex : ∃ i0 ∈ range (k + 1), u i0 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hm
    have h1 : ∑ d ∈ range (k + 1), u d = 0 := Finset.sum_eq_zero h
    have h2 : ∑ d ∈ range (k + 1), lf d * u d = 0 :=
      Finset.sum_eq_zero (fun d hd => by rw [h d hd, mul_zero])
    exact Prod.ext h1 h2
  obtain ⟨i0, hi0, hu0⟩ := hex
  refine ⟨fun d => u d / u i0, i0, hi0, div_self hu0, ?_, ?_⟩
  · intro e he
    have h0 := hu e he
    calc ∑ d ∈ range (k + 1), u d / u i0 * kcf lf ee d e
        = (∑ d ∈ range (k + 1), u d * kcf lf ee d e) / u i0 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun d _ => by ring
      _ = 0 := by rw [h0, zero_div]
  · intro h0
    apply hm
    have h1 : ∑ d ∈ range (k + 1), u d / u i0 = 0 := congrArg Prod.fst h0
    have h2 : ∑ d ∈ range (k + 1), lf d * (u d / u i0) = 0 := congrArg Prod.snd h0
    rw [← Finset.sum_div, div_eq_zero_iff] at h1
    have e2 : ∑ d ∈ range (k + 1), lf d * (u d / u i0) =
        (∑ d ∈ range (k + 1), lf d * u d) / u i0 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [e2, div_eq_zero_iff] at h2
    exact Prod.ext (h1.resolve_right hu0) (h2.resolve_right hu0)

#print axioms exists_normal
end CatalanCore.Uniform.Content.RankProducer
