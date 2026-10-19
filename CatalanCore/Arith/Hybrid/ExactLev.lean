module

public import CatalanCore.Arith.Hybrid.SingLev

@[expose] public section

/-!
# Exact-class levels: the instance constructor `HybInst.ofExact` (any frame)

For a prime power `q = p^e` let `c = p^{e-1}`.  Two positions `A, B` are *`q`-equivalent* when
* `c (S A - S B) ∈ ℤ_(p)` (`S A = ∑_{k ≤ A} Δ_k`), and
* `D A → c² S2 A ∈ ℤ_(p)` holds iff `D B → c² S2 B ∈ ℤ_(p)` (`S2 A = ∑_{k ≤ A} D_k`, and `D` is the
  set of positions whose diagonal entry is used).

The level `xlev D q A` is the least representative of the class of `A`.  Levels may cancel (unlike the
block levels of `SingLev`), and no residue arithmetic is needed: the valuation bounds `off_val`,
`diag_val` follow from the generic count lemma `pow_count_mem` and the generic reductions
`off_val_of_jump`, `diag_val_of_pos` of `SingLev`.  `HybInst.ofExact` only needs the two p-adic bounds
`p^E Δ_k, p^{2E} D_k ∈ ℤ_(p)` for `L N < p^{E+1}`.
-/

open Finset CatalanCore CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

section Exact

variable {Fr : Frame}

/-- `p`-integrality (the carrier of `LocRing p`, without the `Fact` argument). -/
def pint (p : ℕ) (x : ℚ) : Prop := ¬ p ∣ x.den

lemma pint_iff (p : ℕ) [Fact p.Prime] (x : ℚ) : pint p x ↔ x ∈ LocRing p := Iff.rfl

lemma pint_zero {p : ℕ} (hp : p.Prime) : pint p 0 := by
  haveI := Fact.mk hp
  exact (pint_iff p 0).2 (LocRing p).zero_mem

/-- The partial sums of `Δ` and `D`. -/
def Sp (Fr : Frame) (a : ℕ) : ℚ := ∑ k ∈ Icc 1 a, Fr.Delta k

def Sp2 (Fr : Frame) (a : ℕ) : ℚ := ∑ k ∈ Icc 1 a, Fr.Dsq k

lemma Sp_zero : Sp Fr 0 = 0 := by simp [Sp]

lemma Sp2_zero : Sp2 Fr 0 = 0 := by simp [Sp2]

lemma Icc_one_eq_Ioc (a : ℕ) : Icc 1 a = Ioc 0 a := by
  ext k; simp only [mem_Icc, mem_Ioc]; omega

lemma Sp_sub {lo hi : ℕ} (h : lo ≤ hi) :
    Sp Fr hi - Sp Fr lo = ∑ k ∈ Ioc lo hi, Fr.Delta k := by
  unfold Sp
  rw [Icc_one_eq_Ioc, Icc_one_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le lo) h]
  ring

/-- The class relation at the scaling `c = p^{e-1}`. -/
def lrel (Fr : Frame) (D : ℕ → Prop) (p c A B : ℕ) : Prop :=
  pint p ((c : ℚ) * (Sp Fr A - Sp Fr B)) ∧
  ((D A → pint p ((c : ℚ) ^ 2 * Sp2 Fr A)) ↔ (D B → pint p ((c : ℚ) ^ 2 * Sp2 Fr B)))

lemma lrel_refl (D : ℕ → Prop) {p : ℕ} (hp : p.Prime) (c A : ℕ) : lrel Fr D p c A A :=
  ⟨by rw [sub_self, mul_zero]; exact pint_zero hp, Iff.rfl⟩

lemma lrel_symm {D : ℕ → Prop} {p : ℕ} (hp : p.Prime) {c A B : ℕ} (h : lrel Fr D p c A B) :
    lrel Fr D p c B A := by
  haveI := Fact.mk hp
  refine ⟨?_, h.2.symm⟩
  have h1 := (pint_iff p _).1 h.1
  have e : (c : ℚ) * (Sp Fr B - Sp Fr A) = -((c : ℚ) * (Sp Fr A - Sp Fr B)) := by ring
  rw [e]
  exact (pint_iff p _).2 ((LocRing p).neg_mem h1)

lemma lrel_trans {D : ℕ → Prop} {p : ℕ} (hp : p.Prime) {c A B C : ℕ} (h : lrel Fr D p c A B)
    (h' : lrel Fr D p c B C) : lrel Fr D p c A C := by
  haveI := Fact.mk hp
  refine ⟨?_, h.2.trans h'.2⟩
  have e : (c : ℚ) * (Sp Fr A - Sp Fr C) =
      (c : ℚ) * (Sp Fr A - Sp Fr B) + (c : ℚ) * (Sp Fr B - Sp Fr C) := by ring
  rw [e]
  exact (pint_iff p _).2 ((LocRing p).add_mem ((pint_iff p _).1 h.1) ((pint_iff p _).1 h'.1))

/-- The level: the least representative of the class of `A` (zero for non prime powers). -/
noncomputable def xlev (Fr : Frame) (D : ℕ → Prop) (q A : ℕ) : ℕ := by
  classical
  exact if h : IsPrimePow q then
    Nat.find (⟨A, lrel_refl D (Nat.minFac_prime h.ne_one) (q / q.minFac) A⟩ :
      ∃ B, lrel Fr D q.minFac (q / q.minFac) A B)
  else 0

lemma xlev_spec (D : ℕ → Prop) {q : ℕ} (hq : IsPrimePow q) (A : ℕ) :
    lrel Fr D q.minFac (q / q.minFac) A (xlev Fr D q A) := by
  classical
  unfold xlev
  rw [dif_pos hq]
  exact Nat.find_spec (p := fun B => lrel Fr D q.minFac (q / q.minFac) A B) _

lemma xlev_eq (D : ℕ → Prop) {q A B : ℕ} (hq : IsPrimePow q) (h : xlev Fr D q A = xlev Fr D q B) :
    lrel Fr D q.minFac (q / q.minFac) A B := by
  have hp := Nat.minFac_prime hq.ne_one
  refine lrel_trans hp (xlev_spec D hq A) ?_
  rw [h]
  exact lrel_symm hp (xlev_spec D hq B)

lemma xlev_zero_iff' (D : ℕ → Prop) {q A : ℕ} (hq : IsPrimePow q) :
    xlev Fr D q A = 0 ↔ lrel Fr D q.minFac (q / q.minFac) A 0 := by
  classical
  unfold xlev
  rw [dif_pos hq]
  exact Nat.find_eq_zero (p := fun B => lrel Fr D q.minFac (q / q.minFac) A B) _

lemma sq_pow_eq (x : ℚ) (n : ℕ) : (x ^ n) ^ 2 = x ^ (2 * n) := by
  rw [← pow_mul, mul_comm]

lemma pow_div_self' {p e : ℕ} (hp : 0 < p) (he : 1 ≤ e) : p ^ e / p = p ^ (e - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [pow_succ, Nat.mul_div_cancel _ hp]; simp

lemma xlev_pow_eq (D : ℕ → Prop) {p e A B : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (h : xlev Fr D (p ^ e) A = xlev Fr D (p ^ e) B) : lrel Fr D p (p ^ (e - 1)) A B := by
  have hq : IsPrimePow (p ^ e) := hp.isPrimePow.pow (by omega)
  have := xlev_eq D hq h
  rwa [hp.pow_minFac (by omega), pow_div_self' hp.pos he] at this

/-- **Zero criterion** for the level at `q = p^e`. -/
lemma xlev_pow_zero_iff (D : ℕ → Prop) {p e A : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    xlev Fr D (p ^ e) A = 0 ↔
      pint p ((p : ℚ) ^ (e - 1) * Sp Fr A) ∧
        (D A → pint p (((p : ℚ) ^ (e - 1)) ^ 2 * Sp2 Fr A)) := by
  have hq : IsPrimePow (p ^ e) := hp.isPrimePow.pow (by omega)
  rw [xlev_zero_iff' D hq, hp.pow_minFac (by omega), pow_div_self' hp.pos he]
  unfold lrel
  simp only [Sp_zero, Sp2_zero, sub_zero, mul_zero, Nat.cast_pow]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hA => h2.mpr (fun _ => pint_zero hp) hA⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, ⟨fun _ _ => pint_zero hp, fun _ => h3⟩⟩

/-- **The count lemma**: if `p^{c(e-1)} x ∉ ℤ_(p)` forces `P e` for `e ∈ [1, E]`, and `p^{cE} x ∈
ℤ_(p)`, then `p^{c · #{e ≤ E : P e}} x ∈ ℤ_(p)`. -/
lemma pow_count_mem (p : ℕ) [Fact p.Prime] (c E : ℕ) (x : ℚ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ e ∈ Icc 1 E, (p : ℚ) ^ (c * (e - 1)) * x ∉ LocRing p → P e)
    (htop : (p : ℚ) ^ (c * E) * x ∈ LocRing p) :
    (p : ℚ) ^ (c * ((Icc 1 E).filter P).card) * x ∈ LocRing p := by
  classical
  have hex : ∃ j, (p : ℚ) ^ (c * j) * x ∈ LocRing p := ⟨E, htop⟩
  have hspec : (p : ℚ) ^ (c * Nat.find hex) * x ∈ LocRing p := Nat.find_spec hex
  have hj0E : Nat.find hex ≤ E := Nat.find_min' hex htop
  have hsub : Icc 1 (Nat.find hex) ⊆ (Icc 1 E).filter P := by
    intro e he
    have he' := Finset.mem_Icc.mp he
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨he'.1, by omega⟩,
      hP e (Finset.mem_Icc.mpr ⟨he'.1, by omega⟩) ?_⟩
    exact Nat.find_min hex (show e - 1 < Nat.find hex by omega)
  have hle : Nat.find hex ≤ ((Icc 1 E).filter P).card := by
    have := Finset.card_le_card hsub
    simpa using this
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
  rw [ht]
  have e : (p : ℚ) ^ (c * (Nat.find hex + t)) * x =
      ((p : ℚ) ^ (c * t)) * ((p : ℚ) ^ (c * Nat.find hex) * x) := by
    rw [mul_add, pow_add]; ring
  rw [e]
  exact (LocRing p).mul_mem ((LocRing p).pow_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)) _)
    hspec

end Exact

/-! ### The constructor -/

section Constructor

variable {Fr : Frame} (cd : CatalanCore.Arith.ContentData Fr) (D : ℕ → Prop)
  (hD : ∀ (p : ℕ) [Fact p.Prime] (E N k : ℕ), cd.L * N < p ^ (E + 1) → 1 ≤ k → k ≤ N →
    (p : ℚ) ^ E * Fr.Delta k ∈ LocRing p)
  (hD2 : ∀ (p : ℕ) [Fact p.Prime] (E N k : ℕ), cd.L * N < p ^ (E + 1) → 1 ≤ k → k ≤ N →
    (p : ℚ) ^ (2 * E) * Fr.Dsq k ∈ LocRing p)

include hD in
lemma exact_top_Sp (p : ℕ) [Fact p.Prime] (E N : ℕ) (hE : cd.L * N < p ^ (E + 1)) {lo hi : ℕ}
    (hlo : lo ≤ hi) (hhi : hi ≤ N) : (p : ℚ) ^ E * (Sp Fr hi - Sp Fr lo) ∈ LocRing p := by
  rw [Sp_sub hlo, Finset.mul_sum]
  refine (LocRing p).sum_mem fun k hk => ?_
  have := Finset.mem_Ioc.mp hk
  exact hD p E N k hE (by omega) (by omega)

include hD in
lemma exact_top_Sp' (p : ℕ) [Fact p.Prime] (E N : ℕ) (hE : cd.L * N < p ^ (E + 1)) {a : ℕ}
    (ha : a ≤ N) : (p : ℚ) ^ E * Sp Fr a ∈ LocRing p := by
  simpa [Sp_zero] using exact_top_Sp cd hD p E N hE (Nat.zero_le a) ha

include hD2 in
lemma exact_top_Sp2 (p : ℕ) [Fact p.Prime] (E N : ℕ) (hE : cd.L * N < p ^ (E + 1)) {a : ℕ}
    (ha : a ≤ N) : (p : ℚ) ^ (2 * E) * Sp2 Fr a ∈ LocRing p := by
  unfold Sp2
  rw [Finset.mul_sum]
  refine (LocRing p).sum_mem fun k hk => ?_
  have := Finset.mem_Icc.mp hk
  exact hD2 p E N k hE (by omega) (by omega)

include hD hD2 in
lemma xlev_large {p e N a : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hbig : cd.L * N < p ^ e)
    (ha : a ≤ N) : xlev Fr D (p ^ e) a = 0 := by
  haveI := Fact.mk hp
  rw [xlev_pow_zero_iff D hp he]
  have hE : cd.L * N < p ^ ((e - 1) + 1) := by rwa [Nat.sub_add_cancel he]
  refine ⟨(pint_iff p _).2 (exact_top_Sp' cd hD p (e - 1) N hE ha), fun _ => (pint_iff p _).2 ?_⟩
  have := exact_top_Sp2 cd hD2 p (e - 1) N hE ha
  rwa [sq_pow_eq]

/-- **The exact-class hybrid instance.**  `D` is the set of positions whose diagonal entry is used;
`Ebd N = L N`. -/
noncomputable def HybInst.ofExact : HybInst Fr where
  cd := cd
  Ebd := fun N => cd.L * N
  lev := xlev Fr D
  dok := D
  off_val := fun p _ E N lo hi h1 h2 hlo hhi => by
    refine off_val_of_jump _ p E lo hi hlo (by omega) ?_
    rw [← Sp_sub hlo.le]
    have := pow_count_mem p 1 E (Sp Fr hi - Sp Fr lo)
      (fun e => xlev Fr D (p ^ e) lo ≠ xlev Fr D (p ^ e) hi) ?_ ?_
    · simpa using this
    · intro e he hnot
      by_contra hEq
      have hr := (xlev_pow_eq D (Fact.out : p.Prime) (Finset.mem_Icc.mp he).1 hEq).1
      apply hnot
      have e1 : (p : ℚ) ^ (1 * (e - 1)) * (Sp Fr hi - Sp Fr lo) =
          -(((p ^ (e - 1) : ℕ) : ℚ) * (Sp Fr lo - Sp Fr hi)) := by push_cast; ring
      rw [e1]
      exact (LocRing p).neg_mem hr
    · rw [one_mul]
      exact exact_top_Sp cd hD p E N h1 hlo.le hhi
  diag_val := fun p _ E N a h1 h2 hDa => by
    refine diag_val_of_pos _ p E a ?_
    have := pow_count_mem p 2 E (Sp2 Fr a) (fun e => 0 < xlev Fr D (p ^ e) a) ?_ ?_
    · exact this
    · intro e he hnot
      by_contra h0
      have h0' : xlev Fr D (p ^ e) a = 0 := by omega
      have hr := ((xlev_pow_zero_iff D (Fact.out : p.Prime) (Finset.mem_Icc.mp he).1).1 h0').2 hDa
      apply hnot
      rw [sq_pow_eq] at hr
      exact hr
    · exact exact_top_Sp2 cd hD2 p E N h1 h2
  lev_large := fun p e N a hp _ he hbig ha => xlev_large cd D hD hD2 hp he hbig ha
  lev_Ebd := fun q N a hbig ha => by
    by_cases hq : IsPrimePow q
    · obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff q).1 hq
      have hL := cd.hL
      refine xlev_large cd D hD hD2 hp he ?_ ha
      have : cd.L * N + N < p ^ e := hbig
      omega
    · unfold xlev
      rw [dif_neg hq]

/-- **Zero below the first singular index** (any frame, good prime): the level is `0` for `A < kq p`. -/
theorem ofExact_lev_zero_low {p A : ℕ} (hp : p.Prime) (hb : p ∉ cd.bad) (hA : A < cd.kq p) :
    (HybInst.ofExact cd D hD hD2).lev p A = 0 := by
  haveI := Fact.mk hp
  show xlev Fr D p A = 0
  have e1 : p = p ^ 1 := (pow_one p).symm
  rw [e1, xlev_pow_zero_iff D hp le_rfl]
  have key : ∀ k, 1 ≤ k → k ≤ A → ¬ p ∣ cd.Phi k := by
    intro k hk1 hkA hd
    have hcop : ∀ p' ∈ cd.bad, ¬ p' ∣ p := by simpa using cd.coprime_bad_pow (e := 1) hp hb
    have := (cd.kq_le p k hp.isPrimePow hcop hk1 hd).1
    omega
  have hunit : ∀ k, 1 ≤ k → k ≤ A → (1 : ℚ) / (cd.Phi k : ℚ) ∈ LocRing p := by
    intro k hk1 hkA
    have hn := cd.Phi_pos k hk1
    have := pow_div_mem (p := p) (n := cd.Phi k) (j := 0) hn
      (by rw [Nat.factorization_eq_zero_of_not_dvd (key k hk1 hkA)])
    simpa using this
  simp only [Nat.sub_self, pow_zero, one_pow, one_mul]
  refine ⟨(pint_iff p _).2 ?_, fun _ => (pint_iff p _).2 ?_⟩
  · unfold Sp
    refine (LocRing p).sum_mem fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    obtain ⟨z, hz⟩ := cd.delta_int k hk'.1
    have hPq : (cd.Phi k : ℚ) ≠ 0 := by exact_mod_cast (cd.Phi_pos k hk'.1).ne'
    have e : Fr.Delta k = (z : ℚ) * (1 / (cd.Phi k : ℚ)) := by
      rw [← hz]; field_simp
    rw [e]
    exact (LocRing p).mul_mem (int_mem_locRing _) (hunit k hk'.1 hk'.2)
  · unfold Sp2
    refine (LocRing p).sum_mem fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    obtain ⟨z, hz⟩ := cd.dsq_int k hk'.1
    have hPq : (cd.Phi k : ℚ) ≠ 0 := by exact_mod_cast (cd.Phi_pos k hk'.1).ne'
    have e : Fr.Dsq k = (z : ℚ) * (1 / (cd.Phi k : ℚ)) ^ 2 := by
      rw [← hz]; field_simp
    rw [e]
    exact (LocRing p).mul_mem (int_mem_locRing _) ((LocRing p).pow_mem (hunit k hk'.1 hk'.2) 2)

end Constructor

end CatalanCore.Arith.Hybrid
