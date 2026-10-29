import CatalanCore.Uniform.Content.RankProducer.ClosedMoment
import CatalanCore.Uniform.Content.RankProducer.Triv
import CatalanCore.Uniform.Content.RankProducer.RationalLoads
set_option Elab.async false

/-! # The closed-form fibre certificates (C2/PAPER.md §2, lane C2L)

From a normalised kernel vector `(u, i0)` of the `(k+1) × k` block (`exists_normal`):

* `bordRow`: rows `0..k`, columns `0..k-1`; `Lq` is the identity with row `i0` replaced by `u`;
  kills row digit `i0`.  Its row load is the moment `mom lf k u`.
* `bordCol`: the transpose (columns `0..k`), kills column digit `i0`, same load (`Kc` symmetric).
* `sqCert`: the square `(1, 0)` fibre `K = [0]`, kills row and column digit `0`, load `(1, lf 0)`.

`clsVec`, `clsIdx`: the class data of a shape `(k, z)`; `e_0` on the D0 shapes `k ≤ 1, z = 0`
(moment `(1, lf 0)`), Lemma 3's vector otherwise.  `clsBnd`: the denominator / numerator bound;
below a prime `p` it makes the vector `p`-integral and its reduced moment nonzero (NOTES P3).
-/

namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid

theorem sum_mul_delta (s : Finset ℕ) (g : ℕ → ℚ) (e : ℕ) :
    ∑ f ∈ s, g f * delta f e = if e ∈ s then g e else 0 := by
  simp only [delta, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq' s e g

theorem sum_delta_mul (s : Finset ℕ) (g : ℕ → ℚ) (d : ℕ) :
    ∑ f ∈ s, delta d f * g f = if d ∈ s then g d else 0 := by
  simp only [delta, ite_mul, one_mul, zero_mul]
  exact Finset.sum_ite_eq s d g

/-- The identity with row `i0` replaced by `u` times its inverse. -/
theorem rowRep_mul (s : Finset ℕ) (u : ℕ → ℚ) (i0 : ℕ) (hi0 : i0 ∈ s) (hu0 : u i0 = 1)
    (d e : ℕ) (he : e ∈ s) (hd : d ∈ s) :
    ∑ f ∈ s, (if d = i0 then u f else delta d f) *
      (if f = i0 then (if e = i0 then 1 else -u e) else delta f e) = if d = e then 1 else 0 := by
  by_cases hdi : d = i0
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hi0]
    have hrest : ∑ f ∈ s \ {i0}, (if d = i0 then u f else delta d f) *
        (if f = i0 then (if e = i0 then 1 else -u e) else delta f e) =
        ∑ f ∈ s \ {i0}, u f * delta f e := by
      refine Finset.sum_congr rfl fun f hf => ?_
      have hf' : f ≠ i0 := fun h => (Finset.mem_sdiff.1 hf).2 (Finset.mem_singleton.2 h)
      rw [if_pos hdi, if_neg hf']
    rw [hrest, sum_mul_delta, if_pos hdi, if_pos rfl, hu0, one_mul]
    by_cases hei : e = i0
    · have hn : e ∉ s \ {i0} := fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_singleton.2 hei)
      rw [if_pos hei, if_neg hn, if_pos (hdi.trans hei.symm), add_zero]
    · have hmem : e ∈ s \ {i0} :=
        Finset.mem_sdiff.2 ⟨he, fun h => hei (Finset.mem_singleton.1 h)⟩
      have hde : ¬ d = e := fun h => hei (h.symm.trans hdi)
      rw [if_neg hei, if_pos hmem, if_neg hde]
      ring
  · have h1 : ∀ f, (if d = i0 then u f else delta d f) = delta d f := fun f => if_neg hdi
    simp only [h1]
    rw [sum_delta_mul, if_pos hd, if_neg hdi]
    rfl

/-- The identity with column `i0` replaced by `u` times its inverse. -/
theorem colRep_mul (s : Finset ℕ) (u : ℕ → ℚ) (i0 : ℕ) (hi0 : i0 ∈ s) (hu0 : u i0 = 1)
    (d e : ℕ) (hd : d ∈ s) (he : e ∈ s) :
    ∑ f ∈ s, (if f = i0 then u d else delta d f) *
      (if e = i0 then (if f = i0 then 1 else -u f) else delta f e) = if d = e then 1 else 0 := by
  by_cases hei : e = i0
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hi0]
    have hrest : ∑ f ∈ s \ {i0}, (if f = i0 then u d else delta d f) *
        (if e = i0 then (if f = i0 then 1 else -u f) else delta f e) =
        ∑ f ∈ s \ {i0}, delta d f * (-u f) := by
      refine Finset.sum_congr rfl fun f hf => ?_
      have hf' : f ≠ i0 := fun h => (Finset.mem_sdiff.1 hf).2 (Finset.mem_singleton.2 h)
      rw [if_neg hf', if_pos hei, if_neg hf']
    rw [hrest, sum_delta_mul (s \ {i0}) (fun f => -u f) d, if_pos rfl, if_pos hei, if_pos rfl,
      mul_one]
    by_cases hdi : d = i0
    · have hn : d ∉ s \ {i0} := fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_singleton.2 hdi)
      rw [if_neg hn, if_pos (hdi.trans hei.symm), add_zero, hdi, hu0]
    · have hmem : d ∈ s \ {i0} :=
        Finset.mem_sdiff.2 ⟨hd, fun h => hdi (Finset.mem_singleton.1 h)⟩
      have hde : ¬ d = e := fun h => hdi (h.trans hei)
      rw [if_pos hmem, if_neg hde]
      ring
  · have h1 : ∀ f, (if e = i0 then (if f = i0 then (1 : ℚ) else -u f) else delta f e) =
        delta f e := fun f => if_neg hei
    simp only [h1]
    rw [sum_mul_delta, if_pos he, if_neg hei]
    rfl

/-- Bordered fibre certificate, row role: kills row digit `i0` with the kernel vector `u`. -/
def bordRow (lf ee : ℕ → ℚ) (k : ℕ) (u : ℕ → ℚ) (i0 : ℕ) : FibreCert where
  R := range (k + 1)
  C := range k
  lf := lf
  ee := ee
  Lq := fun d f => if d = i0 then u f else delta d f
  Lq' := fun d f => if d = i0 then (if f = i0 then 1 else -u f) else delta d f
  Pq := delta
  Pq' := delta
  kr := {i0}
  kc := ∅

/-- Bordered fibre certificate, column role: kills column digit `i0`. -/
def bordCol (lf ee : ℕ → ℚ) (k : ℕ) (u : ℕ → ℚ) (i0 : ℕ) : FibreCert where
  R := range k
  C := range (k + 1)
  lf := lf
  ee := ee
  Lq := delta
  Lq' := delta
  Pq := fun g e => if e = i0 then u g else delta g e
  Pq' := fun g e => if e = i0 then (if g = i0 then 1 else -u g) else delta g e
  kr := ∅
  kc := {i0}

/-- The square `(1, 0)` certificate: `K = [0]`, kills row and column digit `0`. -/
def sqCert (lf ee : ℕ → ℚ) : FibreCert where
  R := range 1
  C := range 1
  lf := lf
  ee := ee
  Lq := delta
  Lq' := delta
  Pq := delta
  Pq' := delta
  kr := {0}
  kc := {0}

section Ok
variable {lf ee : ℕ → ℚ} {k : ℕ} {u : ℕ → ℚ} {i0 : ℕ}

theorem bordRow_ok (hi0 : i0 ∈ range (k + 1)) (hu0 : u i0 = 1) (hker : InKer lf ee k u) :
    (bordRow lf ee k u i0).Ok where
  hLL := fun d hd e he => rowRep_mul (range (k + 1)) u i0 hi0 hu0 d e he hd
  hPP := fun d hd e he => sum_delta (range k) hd he
  kr_sub := Finset.singleton_subset_iff.2 hi0
  kc_sub := Finset.empty_subset _
  hrow := by
    intro d hd e he
    have hd : d = i0 := Finset.mem_singleton.1 hd
    show ∑ f ∈ range (k + 1), ∑ g ∈ range k,
      (if d = i0 then u f else delta d f) * kcf lf ee f g * delta g e = 0
    have he' : e ∈ range k := he
    simp only [if_pos hd]
    simp only [sum_mul_delta, if_pos he']
    exact hker e he'
  hcol := fun d _ e he => absurd he (Finset.notMem_empty _)

theorem bordCol_ok (hi0 : i0 ∈ range (k + 1)) (hu0 : u i0 = 1) (hker : InKer lf ee k u) :
    (bordCol lf ee k u i0).Ok where
  hLL := fun d hd e he => sum_delta (range k) hd he
  hPP := fun d hd e he => colRep_mul (range (k + 1)) u i0 hi0 hu0 d e hd he
  kr_sub := Finset.empty_subset _
  kc_sub := Finset.singleton_subset_iff.2 hi0
  hrow := fun d hd _ _ => absurd hd (Finset.notMem_empty _)
  hcol := by
    intro d hd e he
    have he : e = i0 := Finset.mem_singleton.1 he
    show ∑ f ∈ range k, ∑ g ∈ range (k + 1),
      delta d f * kcf lf ee f g * (if e = i0 then u g else delta g e) = 0
    simp only [if_pos he]
    have h1 : ∀ f, ∑ g ∈ range (k + 1), delta d f * kcf lf ee f g * u g =
        delta d f * ∑ g ∈ range (k + 1), kcf lf ee f g * u g := by
      intro f
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring
    simp only [h1]
    have hd' : d ∈ range k := hd
    rw [sum_delta_mul, if_pos hd']
    have h2 := hker d hd'
    rw [← h2]
    exact Finset.sum_congr rfl fun g _ => by rw [kcf_symm, mul_comm]

theorem sqCert_ok (hee : ee 0 = 0) : (sqCert lf ee).Ok where
  hLL := fun d hd e he => sum_delta (range 1) hd he
  hPP := fun d hd e he => sum_delta (range 1) hd he
  kr_sub := by simp [sqCert]
  kc_sub := by simp [sqCert]
  hrow := by
    intro d hd e he
    have hd0 : d = 0 := Finset.mem_singleton.1 hd
    have he0 : e = 0 := by simpa [sqCert] using he
    subst hd0; subst he0
    simp [FibreCert.LKP, sqCert, FibreCert.Kc, delta, hee]
  hcol := by
    intro d hd e he
    have he0 : e = 0 := Finset.mem_singleton.1 he
    have hd0 : d = 0 := by simpa [sqCert] using hd
    subst hd0; subst he0
    simp [FibreCert.LKP, sqCert, FibreCert.Kc, delta, hee]

theorem bordRow_integral {p : ℕ} [Fact p.Prime] (hu : ∀ f ∈ range (k + 1), u f ∈ S p) :
    (bordRow lf ee k u i0).Integral p where
  lq := by
    intro d _ e he
    show (if d = i0 then u e else delta d e) ∈ S p ∧
      (if d = i0 then (if e = i0 then 1 else -u e) else delta d e) ∈ S p
    by_cases hdi : d = i0
    · rw [if_pos hdi, if_pos hdi]
      refine ⟨hu e he, ?_⟩
      by_cases hei : e = i0
      · rw [if_pos hei]; exact (S p).one_mem
      · rw [if_neg hei]; exact (S p).neg_mem (hu e he)
    · rw [if_neg hdi, if_neg hdi]
      exact ⟨delta_mem d e, delta_mem d e⟩
  pq := fun d _ e _ => ⟨delta_mem d e, delta_mem d e⟩

theorem bordCol_integral {p : ℕ} [Fact p.Prime] (hu : ∀ f ∈ range (k + 1), u f ∈ S p) :
    (bordCol lf ee k u i0).Integral p where
  lq := fun d _ e _ => ⟨delta_mem d e, delta_mem d e⟩
  pq := by
    intro d hd e _
    show (if e = i0 then u d else delta d e) ∈ S p ∧
      (if e = i0 then (if d = i0 then 1 else -u d) else delta d e) ∈ S p
    by_cases hei : e = i0
    · rw [if_pos hei, if_pos hei]
      refine ⟨hu d hd, ?_⟩
      by_cases hdi : d = i0
      · rw [if_pos hdi]; exact (S p).one_mem
      · rw [if_neg hdi]; exact (S p).neg_mem (hu d hd)
    · rw [if_neg hei, if_neg hei]
      exact ⟨delta_mem d e, delta_mem d e⟩

theorem sqCert_integral {p : ℕ} [Fact p.Prime] : (sqCert lf ee).Integral p where
  lq := fun d _ e _ => ⟨delta_mem d e, delta_mem d e⟩
  pq := fun d _ e _ => ⟨delta_mem d e, delta_mem d e⟩

theorem bordRow_rload : (bordRow lf ee k u i0).rload i0 = mom lf k u := by
  simp [FibreCert.rload, bordRow, mom]

theorem bordCol_cload : (bordCol lf ee k u i0).cload i0 = mom lf k u := by
  simp [FibreCert.cload, bordCol, mom]

theorem sqCert_rload : (sqCert lf ee).rload 0 = (1, lf 0) := by
  simp [FibreCert.rload, sqCert, delta]

theorem sqCert_cload : (sqCert lf ee).cload 0 = (1, lf 0) := by
  simp [FibreCert.cload, sqCert, delta]

theorem mom_delta0 (lf : ℕ → ℚ) (k : ℕ) : mom lf k (delta 0) = (1, lf 0) := by
  simp [mom, delta]

end Ok

/-! ## Class data and the bound `clsBnd` -/

/-- The class vector: `e_0` on the D0 shapes (`k ≤ 1`, bit `0`), else Lemma 3's vector. -/
noncomputable def clsVec (lf ee : ℕ → ℚ) (k : ℕ) (z : Bool) : ℕ → ℚ :=
  if k ≤ 1 ∧ z = false then delta 0 else Classical.choose (exists_normal lf ee k)

/-- The killed digit of the class. -/
noncomputable def clsIdx (lf ee : ℕ → ℚ) (k : ℕ) (z : Bool) : ℕ :=
  if k ≤ 1 ∧ z = false then 0
  else Classical.choose (Classical.choose_spec (exists_normal lf ee k))

section Cls
variable (lf ee : ℕ → ℚ) (k : ℕ) (z : Bool)

theorem clsIdx_mem : clsIdx lf ee k z ∈ range (k + 1) := by
  unfold clsIdx
  split_ifs
  · simp
  · exact (Classical.choose_spec (Classical.choose_spec (exists_normal lf ee k))).1

theorem clsVec_idx : clsVec lf ee k z (clsIdx lf ee k z) = 1 := by
  unfold clsVec clsIdx
  split_ifs
  · simp [delta]
  · exact (Classical.choose_spec (Classical.choose_spec (exists_normal lf ee k))).2.1

theorem clsVec_ker (hee : k ≤ 1 ∧ z = false → ee 0 = 0) : InKer lf ee k (clsVec lf ee k z) := by
  unfold clsVec
  split_ifs with h
  · intro e he
    have he0 : e = 0 := by have := Finset.mem_range.1 he; omega
    subst he0
    rw [sum_delta_mul (range (k + 1)) (fun d => kcf lf ee d 0) 0, if_pos (by simp)]
    simp [kcf, hee h]
  · exact (Classical.choose_spec (Classical.choose_spec (exists_normal lf ee k))).2.2.1

theorem clsVec_mom (h : ¬ (k ≤ 1 ∧ z = false)) : mom lf k (clsVec lf ee k z) ≠ 0 := by
  unfold clsVec
  rw [if_neg h]
  exact (Classical.choose_spec (Classical.choose_spec (exists_normal lf ee k))).2.2.2

theorem clsVec_D0 (h : k ≤ 1 ∧ z = false) : clsVec lf ee k z = delta 0 := by
  unfold clsVec; rw [if_pos h]

theorem clsIdx_D0 (h : k ≤ 1 ∧ z = false) : clsIdx lf ee k z = 0 := by
  unfold clsIdx; rw [if_pos h]

end Cls

/-- Bound of the first nonzero component of a pair. -/
def pairBnd (v : ℚ × ℚ) : ℕ :=
  if v.1 ≠ 0 then v.1.num.natAbs + v.1.den else v.2.num.natAbs + v.2.den

/-- The class bound: denominators of the class vector plus the moment bound. -/
noncomputable def clsBnd (lf ee : ℕ → ℚ) (k : ℕ) (z : Bool) : ℕ :=
  (∑ f ∈ range (k + 1), (clsVec lf ee k z f).den) + pairBnd (mom lf k (clsVec lf ee k z))

section Bnd
variable {p : ℕ} [Fact p.Prime]

theorem red_ne_zero_of_bnd {x : ℚ} (hx : x ≠ 0) (h : x.num.natAbs + x.den < p) :
    red p x ≠ 0 := by
  unfold red
  rw [Rat.cast_def]
  have hnum : (x.num : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.1 hd
    have h2 : 0 < x.num.natAbs := Int.natAbs_pos.2 (Rat.num_ne_zero.2 hx)
    have := Nat.le_of_dvd h2 h1
    omega
  have hden : (x.den : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd x.den_pos hd
    omega
  exact div_ne_zero hnum hden

theorem castV_ne_zero_of_bnd {v : ℚ × ℚ} (hv : v ≠ 0) (h : pairBnd v < p) : castV p v ≠ 0 := by
  unfold pairBnd at h
  by_cases h1 : v.1 ≠ 0
  · rw [if_pos h1] at h
    exact castV_ne_zero_of_fst p v (red_ne_zero_of_bnd h1 h)
  · rw [if_neg h1] at h
    have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext (not_not.1 h1) h2)
    exact castV_ne_zero_of_snd p v (red_ne_zero_of_bnd h2 h)

theorem castV_one_ne_zero (y : ℚ) : castV p (1, y) ≠ 0 := by
  apply castV_ne_zero_of_fst p
  show ((1 : ℚ) : ZMod p) ≠ 0
  rw [Rat.cast_one]; exact one_ne_zero

variable (lf ee : ℕ → ℚ) (k : ℕ) (z : Bool)

theorem clsVec_mem (h : clsBnd lf ee k z < p) :
    ∀ f ∈ range (k + 1), clsVec lf ee k z f ∈ S p := by
  intro f hf
  apply rational_mem_of_den_lt
  have := Finset.single_le_sum (f := fun f => (clsVec lf ee k z f).den)
    (fun _ _ => Nat.zero_le _) hf
  unfold clsBnd at h
  omega

theorem clsMom_ne (hD : ¬ (k ≤ 1 ∧ z = false)) (h : clsBnd lf ee k z < p) :
    castV p (mom lf k (clsVec lf ee k z)) ≠ 0 :=
  castV_ne_zero_of_bnd (clsVec_mom lf ee k z hD) (by unfold clsBnd at h; omega)

end Bnd

#print axioms bordRow_ok
#print axioms bordCol_ok
#print axioms clsVec_ker
end CatalanCore.Uniform.Content.RankProducer
