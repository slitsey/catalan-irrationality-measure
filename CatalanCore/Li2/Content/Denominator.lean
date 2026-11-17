/-
Portions adapted from Tang, dtq1997/li2-half-irrationality, revision
950ee9d53914e1afb89c8f835a8bca6ccfaa0108, Apache-2.0.
See CatalanCore/Li2/Port/LICENSE and NOTICE. Changes: arbitrary prime and valuation loss.
-/
module

public import CatalanCore.Li2.Content.Moments
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P048
public import CatalanCore.Li2.Port.Unified.Modular.Base.DecayTwoAdic

@[expose] public section

/-! General denominator-prime estimates and their asymptotic rate, I1-I6. -/
open Polynomial Finset Filter
open scoped Topology BigOperators
open CatalanCore.Li2.Port
open CatalanCore.Li2.Port.Unified

namespace CatalanCore.Li2.Content
open Port.Unified.Proofs.Arithmetic

def omega (p n : ℕ) (e : ℚ) : Li2.Slot n → ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (_, s)) => -(s.val : ℚ) * L p n
  | Sum.inr (Sum.inr _) => ((4 * n + 1 : ℕ) : ℚ) * e - 2 * L p n

def kappa (p n : ℕ) (e : ℚ) : Li2.Slot n → ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (u, s)) => (Li2.nodeOf n u : ℚ) * e + ((s.val : ℚ) - 2) * L p n
  | Sum.inr (Sum.inr _) => 0

def theta (p n : ℕ) (e : ℚ) (i : ℕ) : ℚ :=
  e * (if i = 0 then 0 else (min (n + 1 + (i - 1) / 3) (4 * n + 1) : ℕ)) - 2 * L p n


private lemma invPowDraft (p : ℕ) [Fact p.Prime] (lam e : ℚ) (he : 0 ≤ e) (hmu : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ e) (m : ℕ) :
    CatalanCore.Li2.Port.Li2.VG p (lam⁻¹^m) ((m:ℚ) * e) := by
  simpa using! hmu.pow m

private lemma cstDraft (p : ℕ) [Fact p.Prime] (lam e : ℚ) (he : 0 ≤ e) (hmu : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ e)
    {K N : ℕ} (hKN : K ≤ N) :
    CatalanCore.Li2.Port.Li2.VG p (parameterCst lam K) (-2 * (Nat.log p N : ℚ)) := by
  unfold parameterCst
  apply CatalanCore.Li2.Port.Li2.VG.sum
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have h1 : CatalanCore.Li2.Port.Li2.VG p (lam⁻¹^a) 0 :=
    (invPowDraft p lam e he hmu a).mono (by positivity)
  have h2 := CatalanCore.Li2.Port.Li2.VG.inv_nat (p := p) (j := a) (n := N) ha1 (ha2.trans hKN)
  have h3 : CatalanCore.Li2.Port.Li2.VG p (((a:ℚ)^2)⁻¹) (2 * -(Nat.log p N : ℚ)) := by
    rw [← inv_pow]
    exact_mod_cast h2.pow 2
  rw [div_eq_mul_inv]
  refine (h1.mul h3).mono ?_
  nlinarith

private lemma poleNodeDraft (p : ℕ) [Fact p.Prime] (lam e : ℚ) (he : 0 ≤ e) (hmu : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ e)
    {j m N : ℕ} (hjm : j ≠ m) (hN : j - m ≤ N ∧ m - j ≤ N) :
    CatalanCore.Li2.Port.Li2.VG p (parameterPoleNode lam j m)
      ((m:ℚ) * e - 2 * (Nat.log p N : ℚ)) := by
  unfold parameterPoleNode
  have hd : ((j:ℚ) - m)^2 =
      ((((j - m : ℕ) + (m - j : ℕ) : ℕ) : ℚ))^2 := by
    rcases le_total j m with h | h
    · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]
      ring
    · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h]
  set t := (j - m : ℕ) + (m - j : ℕ) with ht
  have ht1 : 1 ≤ t := by omega
  have htN : t ≤ N := by omega
  rw [hd, div_eq_mul_inv]
  have h2 := CatalanCore.Li2.Port.Li2.VG.inv_nat (p := p) (j := t) (n := N) ht1 htN
  have h3 : CatalanCore.Li2.Port.Li2.VG p (((t:ℚ)^2)⁻¹) (2 * -(Nat.log p N : ℚ)) := by
    rw [← inv_pow]
    exact_mod_cast h2.pow 2
  have hpow := invPowDraft p lam e he hmu m
  refine (((CatalanCore.Li2.Port.Li2.VG.natCast (p := p) j).mul hpow).mul h3).mono ?_
  nlinarith

private lemma tailDraft (p : ℕ) [Fact p.Prime] (lam e : ℚ) (he : 0 ≤ e) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG p (lam/(1-lam)) 0)
    (hmu : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ e) {n : ℕ} (hn : 1 ≤ n)
    (a b : ℕ) (ha : a < 2*n) (hb : b < 2*n) :
    CatalanCore.Li2.Port.Li2.VG p (parameterTailC lam (4*n) (CatalanCore.Li2.Port.Li2.gramNum n a b))
      (((4*n+1 : ℕ) : ℚ) * e - 2 * (Nat.log p (7*n-2) : ℚ)) := by
  let L : ℚ := Nat.log p (7*n-2)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  unfold parameterTailC
  apply CatalanCore.Li2.Port.Li2.VG.sub
  · set G := CatalanCore.Li2.Port.Li2.gpart (4*n) (CatalanCore.Li2.Port.Li2.gramNum n a b)
    have hGv : ∀ x : ℤ, CatalanCore.Li2.Port.Li2.VG p (G.eval (x:ℚ)) (-2 * L) := by
      intro x
      rw [CatalanCore.Li2.Port.Li2.gpart_eval]
      have hq := CatalanCore.Li2.Port.Li2.gramQuot_eval_VG p n a b x
      have hq' := CatalanCore.Li2.Port.Li2.derivative_eval_VG p (CatalanCore.Li2.Port.Li2.gramQuot_natDegree_le n a b)
        _ (CatalanCore.Li2.Port.Li2.gramQuot_eval_VG p n a b) x
      have l1 : (Nat.log p (3*n+a+b) : ℚ) ≤ L := by
        dsimp [L]
        exact_mod_cast Nat.log_mono_right (by omega : 3*n+a+b ≤ 7*n-2)
      have l2 : (Nat.log p (3*n+a+b-4*n) : ℚ) ≤ L := by
        dsimp [L]
        exact_mod_cast Nat.log_mono_right (by omega : 3*n+a+b-4*n ≤ 7*n-2)
      refine (hq.mono (by nlinarith)).add
        (((CatalanCore.Li2.Port.Li2.VG.intCast (p := p) x).mul hq').mono ?_)
      nlinarith
    have hR := parameterG_VG_of_integral_ratio p lam h1 hratio
      (le_refl ((G.comp (X - C ((4*n+1 : ℕ):ℚ))).natDegree))
      (-2 * L) (fun i _ => by
        have := hGv ((i:ℤ) - ((4*n+1 : ℕ) : ℤ))
        simp only [eval_comp, eval_sub, eval_X, eval_C]
        push_cast at this ⊢
        exact this)
    refine ((invPowDraft p lam e he hmu (4*n+1)).mul hR).mono ?_
    push_cast
    nlinarith
  · apply CatalanCore.Li2.Port.Li2.VG.sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hres : CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.dres (4*n) (CatalanCore.Li2.Port.Li2.gramNum n a b) j) 0 :=
      CatalanCore.Li2.Port.Li2.gramRes_VG p n a b hj1 hj2
    have hin : CatalanCore.Li2.Port.Li2.VG p
        (∑ m ∈ Finset.Ico (4*n+1) (j+4*n+1), parameterPoleNode lam j m)
        (((4*n+1 : ℕ) : ℚ) * e - 2 * L) := by
      apply CatalanCore.Li2.Port.Li2.VG.sum
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
      have hv := poleNodeDraft p lam e he hmu (j := j) (m := m)
        (N := 7*n-2) (by omega) ⟨by omega, by omega⟩
      refine hv.mono ?_
      have : ((4*n+1 : ℕ) : ℚ) ≤ m := by exact_mod_cast hm1
      push_cast at this ⊢
      nlinarith
    simpa only [zero_add] using! hres.mul hin

theorem parameterCst_PoleNode_TailC_VG (p : ℕ) [Fact p.Prime] (z e : ℚ)
    (he : 0 ≤ e) (h1 : z ≠ 1) (hr : Port.Li2.VG p (z / (1 - z)) 0)
    (hmu : Port.Li2.VG p z⁻¹ e) :
    (∀ K N : ℕ, K ≤ N → Port.Li2.VG p (parameterCst z K) (-2 * (Nat.log p N : ℚ))) ∧
    (∀ j m N : ℕ, j ≠ m → j - m ≤ N ∧ m - j ≤ N →
      Port.Li2.VG p (parameterPoleNode z j m) ((m : ℚ) * e - 2 * (Nat.log p N : ℚ))) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ a b : ℕ, a < 2 * n → b < 2 * n →
      Port.Li2.VG p (parameterTailC z (4 * n) (Port.Li2.gramNum n a b))
        (((4 * n + 1 : ℕ) : ℚ) * e - 2 * L p n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K N hKN
    exact cstDraft p z e he hmu hKN
  · intro j m N hjm hN
    exact poleNodeDraft p z e he hmu hjm hN
  · intro n hn a b ha hb
    exact tailDraft p z e he h1 hr hmu hn a b ha hb

private lemma bhatDraft (p : ℕ) [Fact p.Prime] (lam e : ℚ) (he : 0 ≤ e) {n : ℕ} (hn : 1 ≤ n) (hmu : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ e)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (4*n)) {t : ℕ} (ht : t ≤ 2) :
    CatalanCore.Li2.Port.Li2.GV p (parameterBhat lam (4*n) m t) (-(2 - (t:ℚ)) * (L p n)) := by
  have hL : 0 ≤ L p n := Nat.cast_nonneg _
  have e1 : CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.eps (4*n) m 1) (-(1:ℚ) * (L p n)) := by
    simpa using! CatalanCore.Li2.Port.Li2.eps_VG p (N := 7*n-2) hm (by omega) (k := 1) (by norm_num)
  have e2 : CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.eps (4*n) m 2) (-(2:ℚ) * (L p n)) := by
    simpa using! CatalanCore.Li2.Port.Li2.eps_VG p (N := 7*n-2) hm (by omega) (k := 2) le_rfl
  have hC : CatalanCore.Li2.Port.Li2.VG p (parameterCst lam (4*n)) (-2 * (L p n)) :=
    cstDraft p lam e he hmu (by omega)
  have hm' := CatalanCore.Li2.Port.Li2.VG.natCast (p := p) m
  have t1 : CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.eps (4*n) m 1) (-2 * (L p n)) := e1.mono (by linarith)
  have t2 : CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.eps (4*n) m 1 ^ 2) (-2 * (L p n)) := by
    have h := e1.pow 2
    refine h.mono (le_of_eq ?_)
    push_cast
    ring
  have t3 : CatalanCore.Li2.Port.Li2.VG p ((m:ℚ) * (CatalanCore.Li2.Port.Li2.eps (4*n) m 1 ^ 2 - CatalanCore.Li2.Port.Li2.eps (4*n) m 2))
      (-2 * (L p n)) := by
    have h := hm'.mul (t2.sub e2)
    simpa using! h
  have t4 : CatalanCore.Li2.Port.Li2.VG p ((m:ℚ) * parameterCst lam (4*n)) (-2 * (L p n)) := by
    have h := hm'.mul hC
    simpa using! h
  have tX : CatalanCore.Li2.Port.Li2.GV p (C (m:ℚ) * X) (-2 * (L p n)) :=
    (CatalanCore.Li2.Port.Li2.GV.mul (CatalanCore.Li2.Port.Li2.GV.C hm') CatalanCore.Li2.Port.Li2.GV.X).mono (by linarith)
  interval_cases t
  · have g : CatalanCore.Li2.Port.Li2.GV p (parameterBhat lam (4*n) m 0) (-2 * (L p n)) := by
      simp only [parameterBhat]
      exact CatalanCore.Li2.Port.Li2.GV.add (CatalanCore.Li2.Port.Li2.GV.C ((t1.add t3).add t4)) tX
    convert g using 2
    push_cast
    ring
  · have g : CatalanCore.Li2.Port.Li2.GV p (parameterBhat lam (4*n) m 1) (-1 * (L p n)) := by
      simp only [parameterBhat]
      exact CatalanCore.Li2.Port.Li2.GV.C (((CatalanCore.Li2.Port.Li2.VG.one (p := p)).neg.mono (by linarith)).sub
        (by simpa using! hm'.mul e1))
    convert g using 2
    push_cast
    ring
  · have g : CatalanCore.Li2.Port.Li2.GV p (parameterBhat lam (4*n) m 2) 0 := by
      simp only [parameterBhat]
      exact CatalanCore.Li2.Port.Li2.GV.C hm'
    convert g using 2
    push_cast
    ring

private lemma kapDraft (p : ℕ) [Fact p.Prime] (lam e : ℚ) (he : 0 ≤ e) {n : ℕ} (hn : 1 ≤ n) (hmu : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ e)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (4*n)) (s s' : ℕ) :
    CatalanCore.Li2.Port.Li2.GV p (parameterKap lam n m s s') (((s:ℚ) + s' - 2) * (L p n)) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  have hL : 0 ≤ L p n := Nat.cast_nonneg _
  have hsig : CatalanCore.Li2.Port.Li2.JGV p ((CatalanCore.Li2.Port.Li2.shiftBinom n ^ 3).comp (X - C (m:ℚ))) (L p n) := by
    rw [pow_comp]
    exact (CatalanCore.Li2.Port.Li2.shiftBinom_JGV p n m (by dsimp [L]; exact_mod_cast Nat.log_mono_right (b := p) (by omega : n ≤ 7*n-2))).pow 3
  unfold parameterKap
  apply CatalanCore.Li2.Port.Li2.GV.sum
  intro i hi
  have hi2 : i ≤ 2 := by simp at hi; omega
  split_ifs with hle
  · have hscale := CatalanCore.Li2.Port.Li2.residueScale_VG p (K := 4*n) h1 h2
    have hc := CatalanCore.Li2.Port.Li2.GV.C (hscale.mul (hsig i hi2))
    refine (hc.mul (bhatDraft p lam e he hn hmu hm hle)).mono ?_
    push_cast
    nlinarith
  · exact CatalanCore.Li2.Port.Li2.GV.zero _

theorem parameterBhat_Kap_GV (p : ℕ) [Fact p.Prime] (z e : ℚ)
    (he : 0 ≤ e) (hmu : Port.Li2.VG p z⁻¹ e) {n : ℕ} (hn : 1 ≤ n) :
    (∀ m ∈ Finset.Icc 1 (4 * n), ∀ t ≤ 2,
      Port.Li2.GV p (parameterBhat z (4 * n) m t) (-(2 - (t : ℚ)) * L p n)) ∧
    (∀ m ∈ Finset.Icc 1 (4 * n), ∀ s s' : ℕ,
      Port.Li2.GV p (parameterKap z n m s s') (((s : ℚ) + s' - 2) * L p n)) := by
  constructor
  · intro m hm t ht
    exact bhatDraft p z e he hn hmu hm ht
  · intro m hm s s'
    exact kapDraft p z e he hn hmu hm s s'

private lemma logLeDraft (p n : ℕ) {d : ℕ} (hd : d ≤ 7*n-2) :
    (Nat.log p d : ℚ) ≤ L p n := by
  dsimp [L]
  exact_mod_cast Nat.log_mono_right (b := p) hd

private lemma wmDraft (p : ℕ) [Fact p.Prime] (lam e : ℚ) (he : 0 ≤ e) {n : ℕ} (hn : 1 ≤ n) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG p (lam/(1-lam)) 0)
    (hmu : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ e) (a : Fin (2*n)) (i : CatalanCore.Li2.Port.Li2.Slot n) :
    CatalanCore.Li2.Port.Li2.GV p (parameterWm lam n a i) (omega p n e i) := by
  rcases i with _ | ⟨μ, s⟩ | b'
  · apply CatalanCore.Li2.Port.Li2.GV.C
    have h1' := CatalanCore.Li2.Port.Li2.shiftBinom_eval_int p n 0
    have h2 := CatalanCore.Li2.Port.Li2.binomPoly_eval_int_VG p a 0
    simp only [Int.cast_zero] at h1' h2
    simpa [omega, parameterWm] using! (h1'.pow 3).mul h2
  · apply CatalanCore.Li2.Port.Li2.GV.C
    have hj := CatalanCore.Li2.Port.Li2.binom_JGV p a (CatalanCore.Li2.Port.Li2.nodeOf n μ)
      (logLeDraft p n (d := a) (by have := a.isLt; omega))
    simpa [omega, parameterWm] using! hj s.val (by omega)
  · simpa [omega, parameterWm] using!
      CatalanCore.Li2.Port.Li2.GV.C (tailDraft p lam e he h1 hratio hmu hn a b' a.isLt b'.isLt)

private lemma cmatDraft (p : ℕ) [Fact p.Prime] (lam e : ℚ) (he : 0 ≤ e) {n : ℕ} (hn : 1 ≤ n) (hmu : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ e)
    (i : CatalanCore.Li2.Port.Li2.Slot n) (b : Fin (2*n)) :
    CatalanCore.Li2.Port.Li2.GV p (parameterCmat lam n i b) (kappa p n e i) := by
  have hL : 0 ≤ L p n := Nat.cast_nonneg _
  rcases i with _ | ⟨μ, s⟩ | b'
  · apply CatalanCore.Li2.Port.Li2.GV.C
    have h2 := CatalanCore.Li2.Port.Li2.binomPoly_eval_int_VG p b 0
    simp only [Int.cast_zero] at h2
    simpa [kappa, parameterCmat] using! h2.neg
  · have hm : CatalanCore.Li2.Port.Li2.nodeOf n μ ∈ Finset.Icc 1 (4*n) := by
      simp only [CatalanCore.Li2.Port.Li2.nodeOf, Finset.mem_Icc]
      have := μ.isLt
      omega
    have hsum : CatalanCore.Li2.Port.Li2.GV p
        (∑ s' ∈ Finset.range 3,
          parameterKap lam n (CatalanCore.Li2.Port.Li2.nodeOf n μ) s.val s' *
            C (CatalanCore.Li2.Port.Li2.djet (CatalanCore.Li2.Port.Li2.binomPoly b) (CatalanCore.Li2.Port.Li2.nodeOf n μ) s'))
        (((s.val:ℚ) - 2) * (L p n)) := by
      apply CatalanCore.Li2.Port.Li2.GV.sum
      intro s' hs'
      have hs'2 : s' ≤ 2 := by simp at hs'; omega
      have hj := CatalanCore.Li2.Port.Li2.binom_JGV p b (CatalanCore.Li2.Port.Li2.nodeOf n μ)
        (logLeDraft p n (d := b) (by have := b.isLt; omega))
      refine ((kapDraft p lam e he hn hmu hm s.val s').mul
        (CatalanCore.Li2.Port.Li2.GV.C (hj s' hs'2))).mono (le_of_eq ?_)
      ring
    exact (CatalanCore.Li2.Port.Li2.GV.mul (CatalanCore.Li2.Port.Li2.GV.C
      (invPowDraft p lam e he hmu (CatalanCore.Li2.Port.Li2.nodeOf n μ))) hsum).mono
        (le_of_eq (by simp [kappa]))
  · simp only [parameterCmat, kappa]
    split_ifs
    · exact CatalanCore.Li2.Port.Li2.GV.C CatalanCore.Li2.Port.Li2.VG.one
    · exact CatalanCore.Li2.Port.Li2.GV.zero _

theorem parameterWm_Cmat_GV (p : ℕ) [Fact p.Prime] (z e : ℚ)
    (he : 0 ≤ e) (h1 : z ≠ 1) (hr : Port.Li2.VG p (z / (1 - z)) 0)
    (hmu : Port.Li2.VG p z⁻¹ e) {n : ℕ} (hn : 1 ≤ n) :
    (∀ a i, Port.Li2.GV p (parameterWm z n a i) (omega p n e i)) ∧
    (∀ i b, Port.Li2.GV p (parameterCmat z n i b) (kappa p n e i)) := by
  exact ⟨wmDraft p z e he hn h1 hr hmu, cmatDraft p z e he hn hmu⟩

private lemma thetaMonoDraft (p n : ℕ) (e : ℚ) (he : 0 ≤ e) :
    Monotone (theta p n e) := by
  have hbase : Monotone (fun i : ℕ => if i = 0 then 0 else min (n + 1 + (i - 1) / 3) (4 * n + 1)) := by
    intro i j hij
    dsimp only
    split_ifs with hi hj hj
    · exact le_rfl
    · exact Nat.zero_le _
    · omega
    · exact min_le_min (by have h := Nat.div_le_div_right (c := 3) (by omega : i - 1 ≤ j - 1); omega) le_rfl
  intro i j hij
  unfold theta
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hbase hij) he) _

private lemma thetaLeDraft (p n : ℕ) (e : ℚ) (he : 0 ≤ e) (hn : 1 ≤ n)
    (x : Port.Li2.Slot n) :
    theta p n e (Port.Li2.slotRank n x) ≤ omega p n e x + kappa p n e x := by
  have hL : 0 ≤ L p n := Nat.cast_nonneg _
  rcases x with _ | ⟨μ, s⟩ | b'
  · simp [theta, Port.Li2.slotRank, omega, kappa]
    linarith
  · simp only [theta, Port.Li2.slotRank, omega, kappa, Port.Li2.nodeOf]
    erw [if_neg (by omega)]
    have hdiv : (1 + 3 * μ.val + s.val - 1) / 3 = μ.val := by have := s.isLt; omega
    rw [hdiv]
    have h1 : ((min (n + 1 + μ.val) (4*n+1) : ℕ) : ℚ) ≤ ((n + 1 + μ.val : ℕ) : ℚ) := by
      exact_mod_cast min_le_left _ _
    have hw := mul_le_mul_of_nonneg_left h1 he
    push_cast at hw ⊢
    nlinarith
  · simp only [theta, Port.Li2.slotRank, omega, kappa]
    erw [if_neg (by omega)]
    have h1 : ((min (n + 1 + (1 + 9*n + b'.val - 1)/3) (4*n+1) : ℕ) : ℚ) ≤ ((4*n+1 : ℕ) : ℚ) := by
      exact_mod_cast min_le_right _ _
    have hw := mul_le_mul_of_nonneg_left h1 he
    nlinarith

private lemma thetaSumDraft (p n : ℕ) (e : ℚ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (2 * n), theta p n e i) =
      e * (Port.Li2.A2 n : ℚ) - 4 * n * L p n := by
  have h0 : theta p n e 0 = -2 * L p n := by simp [theta]
  have hterm : ∀ i ∈ Finset.range (2*n-1), theta p n e (i+1) =
      e * ((n + 1 + i/3 : ℕ) : ℚ) - 2 * L p n := by
    intro i hi
    have hi' : i < 2*n-1 := Finset.mem_range.mp hi
    simp only [theta, if_neg (by omega : i + 1 ≠ 0), Nat.add_sub_cancel]
    rw [min_eq_left (by omega)]
  rw [show 2*n = (2*n-1) + 1 by omega, Finset.sum_range_succ', h0,
    Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, Port.Li2.A2, Nat.cast_sum]
  rw [show ((2*n-1 : ℕ) : ℚ) = 2*(n:ℚ) - 1 by rw [Nat.cast_sub (by omega)]; push_cast; ring]
  ring

theorem theta_rank (p n : ℕ) (e : ℚ) (he : 0 ≤ e) (hn : 1 ≤ n) :
    Monotone (theta p n e) ∧ Function.Injective (Port.Li2.slotRank n) ∧
    (∀ x, theta p n e (Port.Li2.slotRank n x) ≤ omega p n e x + kappa p n e x) ∧
    (∑ i ∈ Finset.range (2 * n), theta p n e i) = e * (Port.Li2.A2 n : ℚ) - 4 * n * L p n := by
  exact ⟨thetaMonoDraft p n e he, Port.Li2.slotRank_injective n,
    thetaLeDraft p n e he hn, thetaSumDraft p n e hn⟩

theorem parameterQtilde_GV_den (p : ℕ) [Fact p.Prime] (z e : ℚ)
    (he : 0 ≤ e) (h0 : z ≠ 0) (h1 : z ≠ 1)
    (hr : Port.Li2.VG p (z / (1 - z)) 0) (hmu : Port.Li2.VG p z⁻¹ e)
    {n : ℕ} (hn : 1 ≤ n) :
    Port.Li2.GV p (ParameterFamily.Qtilde z n)
      (e * (Port.Li2.A2 n : ℚ) - 4 * n * L p n) := by
  obtain ⟨hmono, hinj, hweights, hsum⟩ := theta_rank p n e he hn
  obtain ⟨hW, hC⟩ := parameterWm_Cmat_GV p z e he h1 hr hmu hn
  rw [← hsum, ParameterFamily.Qtilde_eq_binomGram_det,
    parameterBinomGram_eq_mul z h0 h1]
  apply Port.Li2.det_mul_GV p (parameterWm z n) (parameterCmat z n)
    (omega p n e) (kappa p n e) hW hC
  intro f hf
  calc
    ∑ i ∈ Finset.range (2*n), theta p n e i
        ≤ ∑ b, theta p n e (Port.Li2.slotRank n (f b)) :=
      Port.Li2.sum_range_le_of_injective (theta p n e) hmono
        (fun b => Port.Li2.slotRank n (f b)) (hinj.comp hf)
    _ ≤ ∑ b, (omega p n e (f b) + kappa p n e (f b)) :=
      Finset.sum_le_sum fun b _ => hweights (f b)

private theorem A2_upper_draft (n : ℕ) (hn : 1 ≤ n) :
    3 * Port.Li2.A2 n ≤ 8 * n ^ 2 := by
  have hk : ∀ k ∈ Finset.range (2*n-1),
      3 * (n + 1 + k/3) ≤ 3*n + 3 + k := fun k _ => by omega
  have hs := Finset.sum_le_sum hk
  rw [← Finset.mul_sum] at hs
  have hsum : (∑ k ∈ Finset.range (2*n-1), (3*n+3+k)) =
      (2*n-1) * (3*n+3) + ∑ k ∈ Finset.range (2*n-1), k := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [hsum] at hs
  have hid := Finset.sum_range_id_mul_two (2*n-1)
  unfold Port.Li2.A2
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2*(1+t)-1 = 2*t+1 by omega] at hs hid ⊢
  rw [show 2*t+1-1 = 2*t by omega] at hid
  nlinarith

theorem denominator_rate (e : ℝ) :
    Tendsto (fun n : ℕ => e * (Port.Li2.A2 n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (8 * e / 3)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => (4 / 3 : ℝ) * (n : ℝ)⁻¹)
      atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hi using 1 <;> norm_num
  have hbounds : ∀ᶠ n : ℕ in atTop,
      0 ≤ 8 / 3 - (Port.Li2.A2 n : ℝ) / (n : ℝ) ^ 2 ∧
      8 / 3 - (Port.Li2.A2 n : ℝ) / (n : ℝ) ^ 2 ≤
        (4 / 3 : ℝ) * (n : ℝ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hd : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hne
    have hlo : 8 * (n : ℝ) ^ 2 ≤ 3 * (Port.Li2.A2 n : ℝ) + 4 * n := by
      exact_mod_cast Port.Li2.A2_lower n hn
    have hup : 3 * (Port.Li2.A2 n : ℝ) ≤ 8 * (n : ℝ) ^ 2 := by
      exact_mod_cast A2_upper_draft n hn
    constructor
    · rw [sub_nonneg, div_le_iff₀ hd]
      nlinarith
    · rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hd]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      field_simp [hne]
      nlinarith
  have he := squeeze_zero' (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2) hb
  have ha : Tendsto (fun n : ℕ => (Port.Li2.A2 n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (8 / 3)) := by
    convert ((tendsto_const_nhds (x := (8 / 3 : ℝ))).sub he) using 1 <;>
      first | (funext n; ring) | ring
  convert (tendsto_const_nhds.mul ha : Tendsto
    (fun n : ℕ => e * ((Port.Li2.A2 n : ℝ) / (n : ℝ) ^ 2))
      atTop (𝓝 (e * (8 / 3)))) using 1 <;> ring

end CatalanCore.Li2.Content

#print axioms CatalanCore.Li2.Content.parameterCst_PoleNode_TailC_VG
#print axioms CatalanCore.Li2.Content.parameterBhat_Kap_GV
#print axioms CatalanCore.Li2.Content.parameterWm_Cmat_GV
#print axioms CatalanCore.Li2.Content.theta_rank
#print axioms CatalanCore.Li2.Content.parameterQtilde_GV_den
#print axioms CatalanCore.Li2.Content.denominator_rate
