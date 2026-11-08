module

public import CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# Moved free row certificate (G30): `F_R + h <= cap` with a finitely supported anchor move `h`

kcost: no computation here; the evaluation of `Hlist` is priced in the data modules.

`h^i = -2 T(da^i, .) - S(dv^i, .)` (`barrierTrialT`, `barrierTrialS` of a scaled integer list). On `t = |x|`,
`z = 2t - 1`, `x = sigma t`, the lists `A_n = 2^n T_n(x)` and `E_n = 4^n x^n` are exact integer lists in the
basis `T_j(z)` (`Apair`, `Elist`; `mul2` multiplies by `2(1+z)`), `Hlist` is the weighted sum over a common
denominator `D Lc 4^K`, `close_of_round` rounds it to `Close dP`, and `RowCertMv` is `RowCert` with the extra
polynomial `cH`.  `movedRowCap_of_checks h` concludes `freeRow Trunc.exact 0 x + h x <= cap` on `rowDom`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.RowCertMoved

open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0 (Close)

/-- Coefficients of `Σ c_j T_{|j-1|}`. -/
def lowerZ : List ℤ → List ℤ
  | [] => []
  | [c0] => [0, c0]
  | c0 :: c1 :: rest => c1 :: (c0 + rest.headD 0) :: rest.tail

/-- Coefficients of `2 (1 + z) · Σ c_j T_j(z)`. -/
def mul2 (c : List ℤ) : List ℤ := addZ (addZ (smulZ 2 c) (0 :: c)) (lowerZ c)

theorem basis_one (z : ℝ) : basis 1 z = z := by
  simp [basis]

theorem two_z_mul (c : List ℤ) (k : ℕ) (hk : 1 ≤ k) (z : ℝ) :
    2 * z * rawSum c k z = rawSum c (k + 1) z + rawSum c (k - 1) z := by
  induction c generalizing k with
  | nil => simp
  | cons a t ih =>
    have hk1 : (1 : ℕ) ≤ k + 1 := by omega
    have h := basis_mul 1 k z
    rw [basis_one] at h
    have hn : (((1 : ℕ) : ℤ) - (k : ℤ)).natAbs = k - 1 := by
      have : (((1 : ℕ) : ℤ) - (k : ℤ)) = -((k - 1 : ℕ) : ℤ) := by omega
      rw [this, Int.natAbs_neg, Int.natAbs_natCast]
    rw [hn, show 1 + k = k + 1 from by omega] at h
    simp only [rawSum_cons]
    have h1 := ih (k + 1) hk1
    rw [show k + 1 - 1 = k from by omega] at h1
    rw [show k - 1 + 1 = k from by omega]
    calc 2 * z * ((a : ℝ) * basis k z + rawSum t (k + 1) z)
        = (a : ℝ) * (2 * z * basis k z) + 2 * z * rawSum t (k + 1) z := by ring
      _ = (a : ℝ) * (basis (k + 1) z + basis (k - 1) z) + (rawSum t (k + 1 + 1) z + rawSum t k z) := by
          rw [h1, h]
      _ = _ := by ring

theorem rawSum_mul2 (c : List ℤ) (z : ℝ) :
    rawSum (mul2 c) 0 z = 2 * (1 + z) * rawSum c 0 z := by
  have key : rawSum (0 :: c) 0 z + rawSum (lowerZ c) 0 z = 2 * z * rawSum c 0 z := by
    rcases c with _ | ⟨c0, _ | ⟨c1, rest⟩⟩
    · simp [lowerZ]
    · simp only [lowerZ, rawSum_cons, rawSum_nil, basis_zero]
      rw [basis_one]
      push_cast
      ring
    · have h2 : 2 * z * rawSum rest 2 z = rawSum rest 3 z + rawSum rest 1 z :=
        two_z_mul rest 2 (by omega) z
      have h22 : 2 * z * z = basis 2 z + 1 := by
        have := basis_mul 1 1 z
        simp [basis_one] at this
        linarith
      have hr1 : rawSum rest 1 z = ((rest.headD 0 : ℤ) : ℝ) * z + rawSum rest.tail 2 z := by
        rcases rest with _ | ⟨r0, rt⟩
        · simp
        · simp [rawSum_cons, basis_one]
      have h22c : (c1 : ℝ) * (2 * z * z) = c1 * (basis 2 z + 1) := by rw [h22]
      simp only [lowerZ, rawSum_cons, basis_zero, basis_one, Nat.reduceAdd]
      push_cast
      linarith [h2, h22c, hr1]
  simp only [mul2, rawSum_addZ, rawSum_smulZ]
  push_cast
  linarith


/-! ### The shifted variable and the two recursions

`x = σ (1 + z) / 2` (`σ = ±1`, `z = 2 t - 1`, so `x = σ t`).  `A_n = 2^n T_n(x)` and
`E_n = 4^n x^n` are integer lists in the basis `T_j(z)`. -/

/-- The shifted variable `x = σ (1 + z) / 2`. -/
noncomputable def xz (σ : ℤ) (z : ℝ) : ℝ := (σ : ℝ) * (1 + z) / 2

theorem basis_add_two (n : ℕ) (x : ℝ) :
    basis (n + 2) x = 2 * x * basis (n + 1) x - basis n x := by
  have := congrArg (Polynomial.eval x) (Polynomial.Chebyshev.T_add_two ℝ (n : ℤ))
  simpa [basis] using this

def AStep (σ : ℤ) (p : List ℤ × List ℤ) : List ℤ × List ℤ :=
  (p.2, addZ (smulZ σ (mul2 p.2)) (smulZ (-4) p.1))

/-- `(A_n, A_{n+1})`. -/
def Apair (σ : ℤ) : ℕ → List ℤ × List ℤ
  | 0 => ([1], [σ, σ])
  | n + 1 => AStep σ (Apair σ n)

theorem two_xz (σ : ℤ) (z : ℝ) : 2 * (σ : ℝ) * (1 + z) = 4 * xz σ z := by
  unfold xz; ring

theorem Apair_spec (σ : ℤ) (z : ℝ) : ∀ n : ℕ,
    rawSum (Apair σ n).1 0 z = 2 ^ n * basis n (xz σ z) ∧
    rawSum (Apair σ n).2 0 z = 2 ^ (n + 1) * basis (n + 1) (xz σ z)
  | 0 => by
    refine ⟨by simp [Apair], ?_⟩
    have e : rawSum [σ, σ] 0 z = σ + σ * z := by
      simp [rawSum_cons, basis_one]
    have e2 : (2 : ℝ) ^ (0 + 1) * basis (0 + 1) (xz σ z) = 2 * xz σ z := by
      simp [basis_one]
    simp only [Apair]
    rw [e, e2]
    unfold xz
    ring
  | n + 1 => by
    obtain ⟨h1, h2⟩ := Apair_spec σ z n
    refine ⟨by simpa [Apair, AStep] using h2, ?_⟩
    simp only [Apair, AStep, rawSum_addZ, rawSum_smulZ, rawSum_mul2]
    rw [h1, h2, basis_add_two n]
    have := two_xz σ z
    push_cast
    linear_combination (2 ^ (n + 1) * basis (n + 1) (xz σ z)) * this

/-- `E_n = 4^n x^n`. -/
def Elist (σ : ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => smulZ σ (mul2 (Elist σ n))

theorem Elist_spec (σ : ℤ) (z : ℝ) : ∀ n : ℕ, rawSum (Elist σ n) 0 z = 4 ^ n * xz σ z ^ n
  | 0 => by simp [Elist]
  | n + 1 => by
    simp only [Elist, rawSum_smulZ, rawSum_mul2, Elist_spec σ z n]
    have := two_xz σ z
    linear_combination (4 ^ n * xz σ z ^ n) * this

/-! ### The weighted sums -/

/-- `Σ_k w_k T_{k+1}(x) / (k+1)`, starting at index `k`. -/
noncomputable def refT : List ℤ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | w :: ws, k, x => (w : ℝ) * basis (k + 1) x / ((k : ℝ) + 1) + refT ws (k + 1) x

/-- `Σ_k w_k x^{k+1} / (k+1)`, starting at index `k`. -/
noncomputable def refS : List ℤ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | w :: ws, k, x => (w : ℝ) * x ^ (k + 1) / ((k : ℝ) + 1) + refS ws (k + 1) x

theorem refT_addZ : ∀ (a b : List ℤ) (k : ℕ) (x : ℝ), refT (addZ a b) k x = refT a k x + refT b k x
  | [], b, k, x => by simp [addZ, refT]
  | a :: t, [], k, x => by simp [addZ, refT]
  | a :: t, b :: r, k, x => by
    simp only [addZ, refT, refT_addZ t r (k + 1) x]
    push_cast
    ring

theorem refS_addZ : ∀ (a b : List ℤ) (k : ℕ) (x : ℝ), refS (addZ a b) k x = refS a k x + refS b k x
  | [], b, k, x => by simp [addZ, refS]
  | a :: t, [], k, x => by simp [addZ, refS]
  | a :: t, b :: r, k, x => by
    simp only [addZ, refS, refS_addZ t r (k + 1) x]
    push_cast
    ring

theorem refT_smul (c : ℤ) : ∀ (a : List ℤ) (k : ℕ) (x : ℝ), refT (smulZ c a) k x = c * refT a k x
  | [], k, x => by simp [smulZ, refT]
  | a :: t, k, x => by
    have ih := refT_smul c t (k + 1) x
    simp only [smulZ, List.map_cons, refT] at ih ⊢
    rw [ih]
    push_cast
    ring

theorem refS_smul (c : ℤ) : ∀ (a : List ℤ) (k : ℕ) (x : ℝ), refS (smulZ c a) k x = c * refS a k x
  | [], k, x => by simp [smulZ, refS]
  | a :: t, k, x => by
    have ih := refS_smul c t (k + 1) x
    simp only [smulZ, List.map_cons, refS] at ih ⊢
    rw [ih]
    push_cast
    ring

/-- `Σ_k w_k (Lc/(k+1)) 2^{2K-k-1} A_{k+1}`, running the state `(A_k, A_{k+1})`. -/
def accA (σ Lc : ℤ) (K : ℕ) : List ℤ → ℕ → List ℤ × List ℤ → List ℤ
  | [], _, _ => []
  | w :: ws, k, p =>
    addZ (smulZ (w * (Lc / ((k + 1 : ℕ) : ℤ)) * 2 ^ (2 * K - (k + 1))) p.2)
      (accA σ Lc K ws (k + 1) (AStep σ p))

/-- `Σ_k w_k (Lc/(k+1)) 4^{K-k-1} E_{k+1}`, running the state `E_k`. -/
def accE (σ Lc : ℤ) (K : ℕ) : List ℤ → ℕ → List ℤ → List ℤ
  | [], _, _ => []
  | w :: ws, k, e =>
    addZ (smulZ (w * (Lc / ((k + 1 : ℕ) : ℤ)) * 4 ^ (K - (k + 1))) (smulZ σ (mul2 e)))
      (accE σ Lc K ws (k + 1) (smulZ σ (mul2 e)))

theorem accA_spec (σ Lc : ℤ) (K : ℕ) (z : ℝ) :
    ∀ (ws : List ℤ) (k : ℕ), (∀ j, k < j → j ≤ k + ws.length → (j : ℤ) ∣ Lc) → k + ws.length ≤ K →
      rawSum (accA σ Lc K ws k (Apair σ k)) 0 z = (Lc : ℝ) * 4 ^ K * refT ws k (xz σ z)
  | [], k, _, _ => by simp [accA, refT]
  | w :: ws, k, hd, hK => by
    have hl : (w :: ws).length = ws.length + 1 := rfl
    rw [hl] at hd hK
    obtain ⟨q, hq⟩ := hd (k + 1) (by omega) (by omega)
    have ih := accA_spec σ Lc K z ws (k + 1)
      (fun j h1 h2 => hd j (by omega) (by omega)) (by omega)
    have h2 := (Apair_spec σ z k).2
    simp only [accA, rawSum_addZ, rawSum_smulZ]
    rw [show AStep σ (Apair σ k) = Apair σ (k + 1) from rfl, ih, h2]
    have hdiv : (Lc / ((k + 1 : ℕ) : ℤ)) = q := by
      rw [hq]; exact Int.mul_ediv_cancel_left _ (by positivity)
    rw [hdiv]
    simp only [refT]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hLc : (Lc : ℝ) = ((k : ℝ) + 1) * q := by
      have := congrArg (Int.cast : ℤ → ℝ) hq
      push_cast at this
      exact this
    have hp : (2 : ℝ) ^ (2 * K - (k + 1)) * 2 ^ (k + 1) = 4 ^ K := by
      rw [← pow_add, show 2 * K - (k + 1) + (k + 1) = 2 * K from by omega, pow_mul]
      norm_num
    have key : ((w * q * 2 ^ (2 * K - (k + 1)) : ℤ) : ℝ) * (2 ^ (k + 1) * basis (k + 1) (xz σ z)) =
        (w : ℝ) * q * 4 ^ K * basis (k + 1) (xz σ z) := by
      push_cast
      rw [← hp]
      ring
    have e1 : (Lc : ℝ) * 4 ^ K * ((w : ℝ) * basis (k + 1) (xz σ z) / ((k : ℝ) + 1)) =
        (w : ℝ) * q * 4 ^ K * basis (k + 1) (xz σ z) := by
      rw [hLc]
      field_simp
    linear_combination key - e1

theorem accE_spec (σ Lc : ℤ) (K : ℕ) (z : ℝ) :
    ∀ (ws : List ℤ) (k : ℕ) (e : List ℤ), (∀ j, k < j → j ≤ k + ws.length → (j : ℤ) ∣ Lc) →
      k + ws.length ≤ K → rawSum e 0 z = 4 ^ k * xz σ z ^ k →
      rawSum (accE σ Lc K ws k e) 0 z = (Lc : ℝ) * 4 ^ K * refS ws k (xz σ z)
  | [], k, e, _, _, _ => by simp [accE, refS]
  | w :: ws, k, e, hd, hK, he => by
    have hl : (w :: ws).length = ws.length + 1 := rfl
    rw [hl] at hd hK
    obtain ⟨q, hq⟩ := hd (k + 1) (by omega) (by omega)
    have he' : rawSum (smulZ σ (mul2 e)) 0 z = 4 ^ (k + 1) * xz σ z ^ (k + 1) := by
      rw [rawSum_smulZ, rawSum_mul2, he]
      have := two_xz σ z
      linear_combination (4 ^ k * xz σ z ^ k) * this
    have he'' : (σ : ℝ) * (2 * (1 + z) * (4 ^ k * xz σ z ^ k)) = 4 ^ (k + 1) * xz σ z ^ (k + 1) := by
      have := two_xz σ z
      linear_combination (4 ^ k * xz σ z ^ k) * this
    have ih := accE_spec σ Lc K z ws (k + 1) (smulZ σ (mul2 e))
      (fun j h1 h2 => hd j (by omega) (by omega)) (by omega) he'
    simp only [accE, rawSum_addZ, rawSum_smulZ]
    rw [ih, rawSum_mul2, he, he'']
    have hdiv : (Lc / ((k + 1 : ℕ) : ℤ)) = q := by
      rw [hq]; exact Int.mul_ediv_cancel_left _ (by positivity)
    rw [hdiv]
    simp only [refS]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hLc : (Lc : ℝ) = ((k : ℝ) + 1) * q := by
      have := congrArg (Int.cast : ℤ → ℝ) hq
      push_cast at this
      exact this
    have hp : (4 : ℝ) ^ (K - (k + 1)) * 4 ^ (k + 1) = 4 ^ K := by
      rw [← pow_add, show K - (k + 1) + (k + 1) = K from by omega]
    have key : ((w * q * 4 ^ (K - (k + 1)) : ℤ) : ℝ) * (4 ^ (k + 1) * xz σ z ^ (k + 1)) =
        (w : ℝ) * q * 4 ^ K * xz σ z ^ (k + 1) := by
      push_cast
      rw [← hp]
      ring
    have e1 : (Lc : ℝ) * 4 ^ K * ((w : ℝ) * xz σ z ^ (k + 1) / ((k : ℝ) + 1)) =
        (w : ℝ) * q * 4 ^ K * xz σ z ^ (k + 1) := by
      rw [hLc]
      field_simp
    linear_combination key - e1

/-- The Chebyshev list of `Σ w_k T_{k+1}(x)/(k+1) + Σ v_k x^{k+1}/(k+1)` at `x = σ(1+z)/2`, scaled by
`Lc 4^K`. -/
def Hlist (σ Lc : ℤ) (K : ℕ) (wT wS : List ℤ) : List ℤ :=
  addZ (accA σ Lc K wT 0 (Apair σ 0)) (accE σ Lc K wS 0 [1])

theorem rawSum_Hlist (σ Lc : ℤ) (K : ℕ) (z : ℝ) (wT wS : List ℤ)
    (hT : ∀ j, 0 < j → j ≤ wT.length → (j : ℤ) ∣ Lc) (hS : ∀ j, 0 < j → j ≤ wS.length → (j : ℤ) ∣ Lc)
    (hKT : wT.length ≤ K) (hKS : wS.length ≤ K) :
    rawSum (Hlist σ Lc K wT wS) 0 z =
      (Lc : ℝ) * 4 ^ K * (refT wT 0 (xz σ z) + refS wS 0 (xz σ z)) := by
  unfold Hlist
  rw [rawSum_addZ, accA_spec σ Lc K z wT 0 (fun j h1 h2 => hT j h1 (by omega)) (by omega),
    accE_spec σ Lc K z wS 0 [1] (fun j h1 h2 => hS j h1 (by omega)) (by omega) (by simp)]
  ring

/-! ### The bridge to `barrierTrialT`, `barrierTrialS` and the rounded `Close` -/

open OAI.InternalCatalan

/-- The finitely supported sequence of a scaled list (the same body as `UnsignedInstance.trialSeqOf`). -/
noncomputable def movSeq (l : List ℤ) (D : ℕ) : ℕ → ℝ := fun k => if k = 0 then 0 else (l.getD (k - 1) 0 : ℝ) / D

theorem refT_eq_sum : ∀ (l : List ℤ) (k : ℕ) (x : ℝ), refT l k x =
    ∑ i ∈ Finset.range l.length, (l.getD i 0 : ℝ) * basis (k + i + 1) x / ((k : ℝ) + i + 1)
  | [], k, x => by simp [refT]
  | w :: ws, k, x => by
    rw [refT, refT_eq_sum ws (k + 1) x, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show k + 1 + i + 1 = k + (i + 1) + 1 from by omega]
      push_cast
      ring_nf
    · simp

theorem refS_eq_sum : ∀ (l : List ℤ) (k : ℕ) (x : ℝ), refS l k x =
    ∑ i ∈ Finset.range l.length, (l.getD i 0 : ℝ) * x ^ (k + i + 1) / ((k : ℝ) + i + 1)
  | [], k, x => by simp [refS]
  | w :: ws, k, x => by
    rw [refS, refS_eq_sum ws (k + 1) x, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show k + 1 + i + 1 = k + (i + 1) + 1 from by omega]
      push_cast
      ring_nf
    · simp

theorem barrierTrialT_movSeq (l : List ℤ) (D : ℕ) (x : ℝ) :
    barrierTrialT (movSeq l D) x = refT l 0 x / D := by
  unfold barrierTrialT
  rw [tsum_eq_sum (s := Finset.range l.length)]
  · rw [refT_eq_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [movSeq, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
    simp only [basis, zero_add, Nat.cast_add, Nat.cast_one]
    push_cast
    ring
  · intro k hk
    have : l.getD k 0 = 0 := List.getD_eq_default _ _ (by simpa using hk)
    rw [List.getD_eq_getElem?_getD] at this
    simp [movSeq, this]

theorem barrierTrialS_movSeq (l : List ℤ) (D : ℕ) (x : ℝ) :
    barrierTrialS (movSeq l D) x = refS l 0 x / D := by
  unfold barrierTrialS
  rw [tsum_eq_sum (s := Finset.range l.length)]
  · rw [refS_eq_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [movSeq, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
    push_cast
    ring
  · intro k hk
    have : l.getD k 0 = 0 := List.getD_eq_default _ _ (by simpa using hk)
    rw [List.getD_eq_getElem?_getD] at this
    simp [movSeq, this]

theorem l1_le_of_abs : ∀ (l : List ℤ) (N : ℤ), (∀ a ∈ l, |a| ≤ N) → l1 l ≤ l.length * N
  | [], N, _ => by simp [l1]
  | a :: t, N, h => by
    have h1 := h a (by simp)
    have h2 := l1_le_of_abs t N (fun b hb => h b (by simp [hb]))
    simp only [l1, List.length_cons]
    push_cast
    nlinarith

theorem len_addZ' : ∀ (a b : List ℤ), (addZ a b).length = max a.length b.length
  | [], b => by simp [addZ]
  | a :: t, [] => by simp [addZ]
  | a :: t, b :: r => by
    simp only [addZ, List.length_cons, len_addZ' t r]
    omega

/-- The rounded list is close: `cH / dP` against `Hlist / (D Lc 4^K)`. -/
theorem close_of_round {σ : ℝ} {σz Lc : ℤ} {K : ℕ} {wT wS : List ℤ} {D dP : ℕ}
    (hσ : σ = (σz : ℝ)) (hdP : 0 < dP) (hD : 0 < D) (hLc : 0 < Lc)
    (hT : ∀ j, 0 < j → j ≤ wT.length → (j : ℤ) ∣ Lc) (hS : ∀ j, 0 < j → j ≤ wS.length → (j : ℤ) ∣ Lc)
    (hKT : wT.length ≤ K) (hKS : wS.length ≤ K) {cH : List ℤ}
    (hlen : (Hlist σz Lc K wT wS).length ≤ cH.length)
    (hr : ((addZ (smulZ ((D : ℤ) * Lc * 4 ^ K) cH) (smulZ (-(dP : ℤ)) (Hlist σz Lc K wT wS))).all
      (fun a => decide (|a| ≤ (D : ℤ) * Lc * 4 ^ K))) = true) :
    Close dP (fun t => (refT wT 0 (σ * t) + refS wS 0 (σ * t)) / D) cH ((cH.length : ℝ) / dP) := by
  intro t ht
  set N : ℤ := (D : ℤ) * Lc * 4 ^ K with hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℤ) < N := by rw [hN]; positivity
    exact_mod_cast this
  have hz : 2 * t - 1 ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hx : xz σz (2 * t - 1) = σ * t := by
    unfold xz; rw [hσ]; ring
  have hH := rawSum_Hlist σz Lc K (2 * t - 1) wT wS hT hS hKT hKS
  rw [hx] at hH
  have hdr : (0 : ℝ) < dP := by exact_mod_cast hdP
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hLr : (0 : ℝ) < Lc := by exact_mod_cast hLc
  have hfun : (refT wT 0 (σ * t) + refS wS 0 (σ * t)) / D =
      rawSum (Hlist σz Lc K wT wS) 0 (2 * t - 1) / N := by
    rw [hH, hN]
    push_cast
    field_simp
  beta_reduce
  rw [hfun]
  set Dl := addZ (smulZ N cH) (smulZ (-(dP : ℤ)) (Hlist σz Lc K wT wS)) with hDl
  have hall : ∀ a ∈ Dl, |a| ≤ N := fun a ha => by
    have := List.all_eq_true.1 hr a ha
    simpa using this
  have hl1 := l1_le_of_abs Dl N hall
  have hlenD : Dl.length ≤ cH.length := by
    rw [hDl, len_addZ']
    simp only [smulZ, List.length_map]
    omega
  have hrs := abs_rawSum_le Dl 0 hz
  have hsum : rawSum Dl 0 (2 * t - 1) = (N : ℝ) * rawSum cH 0 (2 * t - 1) -
      (dP : ℝ) * rawSum (Hlist σz Lc K wT wS) 0 (2 * t - 1) := by
    rw [hDl]; simp only [rawSum_addZ, rawSum_smulZ]; push_cast; ring
  have hb : |rawSum Dl 0 (2 * t - 1)| ≤ (cH.length : ℝ) * N := by
    refine hrs.trans ?_
    have : (l1 Dl : ℝ) ≤ ((Dl.length : ℤ) * N : ℤ) := by exact_mod_cast hl1
    refine this.trans ?_
    push_cast
    have : (Dl.length : ℝ) ≤ cH.length := by exact_mod_cast hlenD
    nlinarith
  rw [hsum] at hb
  have e : rawSum (Hlist σz Lc K wT wS) 0 (2 * t - 1) / N - rawSum cH 0 (2 * t - 1) / dP =
      -((N : ℝ) * rawSum cH 0 (2 * t - 1) - dP * rawSum (Hlist σz Lc K wT wS) 0 (2 * t - 1)) / (N * dP) := by
    field_simp
    ring
  rw [e, abs_div, abs_neg, abs_of_pos (mul_pos hNpos hdr), div_le_div_iff₀ (mul_pos hNpos hdr) hdr]
  nlinarith [hb, hNpos]

end CatalanMeasure.GenD.Signed.RouteI.RowCertMoved

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set MeasureTheory intervalIntegral
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.OrdHf (Cov Blk blkF sumF polK psiR bot mBlk sumEQ mc4)
open CatalanMeasure.Signed.ChebSquare

noncomputable section

theorem row_cap_mv {S : CapSource} (hS : S.Admissible) (σ : Sign) {dP : ℕ} (hdP : 0 < dP)
    {D R O C : ℝ → ℝ} {Lq cr wl eD eF eT eR eA eE eH : ℝ} {H : ℝ → ℝ} {cH : List ℤ} {AF AT : List QA} {cD cF cT cl r q : List ℤ}
    {K m lgs lgq : ℕ} {c : ℤ} {cap : ℝ} {dom : Set ℝ} (hdom : ∀ t ∈ dom, t ∈ Ioc (0 : ℝ) 1)
    (hdom2 : ∀ t ∈ dom, sgOf σ * t ≠ 0)
    (hOwn : ∀ t ∈ dom, avgL (S.gas σ) (rowK (sgOf σ * t)) ≤ D t + R t)
    (hOpp : ∀ t ∈ dom, avgL (S.gas (opp σ)) (rowK (sgOf σ * t)) ≤ Lq + O t)
    (hCol : ∀ t ∈ dom, -avgL (S.refCol 0) (colK (sgOf σ * t)) ≤ C t)
    (hRf : ∀ t ∈ dom, (2 - cr) * R t +
      (if σ = Sign.pos then S.reflPoly (sgOf σ * t) else 0) ≤ 0)
    (hAt : ∀ t ∈ dom, cr * R t + O t + C t + (11 / 29 - wl) * Real.log t +
      3 / 29 * Real.log (1 - sgOf σ * t) ≤ avQ false AF t + avQ true AT t)
    (hRad : ∀ t ∈ dom, S.radialA (Trunc.finite 384) σ (sgOf σ * t) -
      39 / 29 * Real.log (1 + t ^ 2) + wl * Real.log t ≤ rawSum cl 0 (2 * t - 1) / dP + eR)
    (hDir : Close dP D cD eD) (hF : Close dP (avQ false AF) cF eF)
    (hT : Close dP (avQ true AT) cT eT) (hH : Close dP H cH eH)
    (hAux : S.auxTail (Trunc.finite 384) σ ≤ eA)
    (hE : (if σ = Sign.pos then S.reflTail else 0) ≤ eE)
    (hs : (addZ (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) cH) r).length = 2 * m + 1)
    (hq : q.length = m + 1) (hgs : 2 * m + 1 ≤ 2 ^ lgs) (hgq : m + 1 ≤ 2 ^ lgq)
    (hK : kronEq K m lgs lgq (dP : ℤ) c (addZ (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) cH) r) q = true)
    (hb : 4 * (2 * (dP : ℤ) * l1 (addZ (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) cH) r) +
      2 * l1 q * l1 q) < CatalanMeasure.GenD.Signed.Davis.CircleCheb.pow2 K)
    (hc : 8 * (2 * (dP : ℤ) * |c|) < CatalanMeasure.GenD.Signed.Davis.CircleCheb.pow2 K)
    (hfin : ((c : ℝ) - (((r.headD 0 : ℤ) : ℝ) - ((l1 r.tail : ℤ) : ℝ))) / dP + (eD + eD) + eF + eT +
      eR + eA + eE + eH + Lq - kappa σ ≤ cap) :
    ∀ t ∈ dom, S.rowField (Trunc.finite 384) σ Flavor.free (some 0) (sgOf σ * t) + H t ≤ cap := by
  intro t ht
  have ht' := hdom t ht
  have hdr : (0 : ℝ) < dP := by exact_mod_cast hdP
  have hdZ : (0 : ℤ) < (dP : ℤ) := by exact_mod_cast hdP
  have hz : 2 * t - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have e0 := rowField_phys hS (Trunc.finite 384) σ (hdom2 t ht)
  have hAbs : |sgOf σ * t| = t := by
    rcases sgOf_cases σ with h | h <;> rw [h] <;> simp [abs_of_pos ht'.1]
  have hSq : (sgOf σ * t) ^ 2 = t ^ 2 := by
    rcases sgOf_cases σ with h | h <;> rw [h] <;> ring
  have hC := (((hDir.add hDir).add hF).add hT) t ht'
  have hHc := (abs_le.1 (hH t ht')).2
  set Pf := addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) cH with hPf
  have hk := kron_le hdZ hs hq hgs hgq hK hb hc (2 * t - 1)
  rw [rawSum_addZ, hPf, rawSum_addZ, rawSum_addZ] at hk
  have hrg := CatalanMeasure.GenD.Signed.RouteI.CompactCap.rawSum_ge r hz
  have a1 := abs_le.1 hC
  have o1 := hOwn t ht
  have o2 := hOpp t ht
  have o3 := hCol t ht
  have o4 := hRf t ht
  have o5 := hAt t ht
  have o6 := hRad t ht
  rw [e0]
  unfold rest
  rw [hAbs, hSq]
  have hk' : (rawSum (addZ (addZ (addZ cD cD) cF) cT) 0 (2 * t - 1) + rawSum cl 0 (2 * t - 1) + rawSum cH 0 (2 * t - 1)) / dP +
      (((r.headD 0 : ℤ) : ℝ) - ((l1 r.tail : ℤ) : ℝ)) / dP ≤ (c : ℝ) / dP := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hdr.le
  have hfin' := hfin
  rw [sub_div] at hfin'
  simp only [add_div] at hk'
  have hsplit : (if σ = Sign.pos then S.reflPoly (sgOf σ * t) + S.reflTail else 0) =
      (if σ = Sign.pos then S.reflPoly (sgOf σ * t) else 0) + (if σ = Sign.pos then S.reflTail else 0) := by
    split_ifs <;> simp
  rw [hsplit]
  set W := (if σ = Sign.pos then S.reflPoly (sgOf σ * t) else 0)
  set Er := (if σ = Sign.pos then S.reflTail else 0)
  have hlt : 11 / 29 * Real.log t = (11 / 29 - wl) * Real.log t + wl * Real.log t := by ring
  rw [hlt]
  have ev : avQ false AF t + avQ true AT t + (D t + D t) ≤
      rawSum (addZ (addZ (addZ cD cD) cF) cT) 0 (2 * t - 1) / dP + (eD + eD + eF + eT) := by
    have := a1.2
    linarith
  linarith

structure RowCertMv (σ : Sign) (dom : Set ℝ) (cap : ℝ) (H : ℝ → ℝ) where
  dP : ℕ
  hdP : 0 < dP
  hdom : ∀ t ∈ dom, t ∈ Ioc (0 : ℝ) 1
  cr : ℚ
  hcr : 0 ≤ cr
  wl : ℚ
  Go : List GS
  Gs : List GS
  Gq : List GS
  Gc : List GS
  qR : List ℚ
  qO : List (ℚ × ℚ)
  q0 : ℚ × ℚ
  qC : List (ℚ × ℚ)
  LF : List QA
  LT : List QA
  cD : List ℤ
  cF : List ℤ
  cT : List ℤ
  cl : List ℤ
  cH : List ℤ
  r : List ℤ
  q : List ℤ
  K : ℕ
  m : ℕ
  lgs : ℕ
  lgq : ℕ
  c : ℤ
  Lq : ℝ
  eD : ℝ
  eF : ℝ
  eT : ℝ
  eR : ℝ
  eA : ℝ
  eE : ℝ
  eH : ℝ
  bindO : ∀ F : ℝ → ℝ, evC (capSource.gas σ) F =
    evS ((Go ++ Gs).map segR) (fun y => sgOf σ * F (sgOf σ * y))
  bindQ : ∀ F : ℝ → ℝ, evC (capSource.gas (opp σ)) F =
    evS (Gq.map segR) (fun y => -sgOf σ * F (-sgOf σ * y))
  bindC : ∀ F : ℝ → ℝ, evC (capSource.refCol 0) F =
    evS (Gc.map segR) (fun y => sgOf σ * F (sgOf σ * y))
  keyO : ∀ g ∈ (Go ++ Gs).map segR, 2 ≤ g.lo ∧ g.lo < g.hi
  keyQ : ∀ g ∈ Gq.map segR, 2 ≤ g.lo ∧ g.lo < g.hi
  posS : ∀ g ∈ Gs.map segR, 0 ≤ g.rho
  chkR : reflB (Go ++ Gs) qR = true
  chkO : oppB Gq qO = true
  chkC : colB Gc (q0 :: qC) = true
  hLq : pint (Gq.map segR) (fun y => Real.log (YCell.physX y)) ≤ Lq
  hRf : ∀ t ∈ dom, (2 - (cr : ℝ)) * pint ((Go ++ Gs).map segR)
      (fun y => Real.log |1 - YCell.physX y * t|) +
    (if σ = Sign.pos then capSource.reflPoly (sgOf σ * t) else 0) ≤ 0
  hLog : ∀ t ∈ dom, (11 / 29 - (wl : ℝ)) * Real.log t + 3 / 29 * Real.log (1 - sgOf σ * t) ≤
    avQ false LF t + avQ true LT t
  hRad : ∀ t ∈ dom, capSource.radialA (Trunc.finite 384) σ (sgOf σ * t) -
      39 / 29 * Real.log (1 + t ^ 2) + (wl : ℝ) * Real.log t ≤
    rawSum cl 0 (2 * t - 1) / dP + eR
  hDir : Close dP (fun t => pint (Go.map segR) fun y => Real.log |t - YCell.physX y|) cD eD
  hF : Close dP (avQ false (reflL cr (Go ++ Gs) qR ++ oppL Gq qO ++ colL 0 Gc (q0 :: qC) ++ LF))
    cF eF
  hT : Close dP (avQ true LT) cT eT
  hH : Close dP H cH eH
  hAux : capSource.auxTail (Trunc.finite 384) σ ≤ eA
  hE : (if σ = Sign.pos then capSource.reflTail else 0) ≤ eE
  hs : (addZ (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) cH) r).length = 2 * m + 1
  hq : q.length = m + 1
  hgs : 2 * m + 1 ≤ 2 ^ lgs
  hgq : m + 1 ≤ 2 ^ lgq
  hK : kronEq K m lgs lgq (dP : ℤ) c (addZ (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) cH) r) q = true
  hb : 4 * (2 * (dP : ℤ) * l1 (addZ (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) cH) r) +
    2 * l1 q * l1 q) < CatalanMeasure.GenD.Signed.Davis.CircleCheb.pow2 K
  hc : 8 * (2 * (dP : ℤ) * |c|) < CatalanMeasure.GenD.Signed.Davis.CircleCheb.pow2 K
  hfin : ((c : ℝ) - (((r.headD 0 : ℤ) : ℝ) - ((l1 r.tail : ℤ) : ℝ))) / dP + (eD + eD) + eF + eT +
    eR + eA + eE + eH + Lq - kappa σ ≤ cap

theorem RowCertMv.le {σ : Sign} {dom : Set ℝ} {cap : ℝ} {H : ℝ → ℝ} (R : RowCertMv σ dom cap H) :
    ∀ t ∈ dom, capSource.rowField (Trunc.finite 384) σ Flavor.free (some 0) (sgOf σ * t) + H t ≤ cap := by
  have hsg := sgOf_cases σ
  have hneg : ∀ t ∈ dom, sgOf σ * t ≠ 0 := by
    intro t ht
    have := (R.hdom t ht).1
    rcases hsg with h | h <;> rw [h] <;> simp [this.ne']
  have hbO := R.bindO
  rw [List.map_append] at hbO
  have hkO := R.keyO
  rw [List.map_append] at hkO
  refine row_cap_mv capSource_admissible σ R.hdP R.hdom hneg
    (D := fun t => pint (R.Go.map segR) fun y => Real.log |t - YCell.physX y|)
    (R := fun t => pint ((R.Go ++ R.Gs).map segR) fun y => Real.log |1 - YCell.physX y * t|)
    (O := fun t => pint (R.Gq.map segR) fun y => Real.log (1 + y * t + t ^ 2))
    (C := fun t => -pint (R.Gc.map segR) (colK t)) (Lq := R.Lq) (cr := R.cr) (wl := R.wl)
    (AF := reflL R.cr (R.Go ++ R.Gs) R.qR ++ oppL R.Gq R.qO ++ colL 0 R.Gc (R.q0 :: R.qC) ++ R.LF)
    (AT := R.LT) ?_ ?_ ?_ R.hRf ?_ R.hRad R.hDir R.hF R.hT R.hH R.hAux R.hE R.hs R.hq R.hgs R.hgq R.hK
    R.hb R.hc R.hfin
  · intro t ht
    obtain ⟨h0, h1⟩ := R.hdom t ht
    have := own_part hsg (gas_sides σ) hbO hkO R.posS h0 h1
    rw [← List.map_append] at this
    exact this
  · intro t ht
    obtain ⟨h0, _⟩ := R.hdom t ht
    have hl : ∀ c ∈ capSource.gas (opp σ), 2 ≤ c.lo ∨ c.hi ≤ -2 := gas_sides _
    rw [opp_part hsg hl R.bindQ R.keyQ h0]
    linarith [R.hLq]
  · intro t ht
    obtain ⟨h0, _⟩ := R.hdom t ht
    rw [avg_col hsg R.bindC h0]
  · intro t ht
    obtain ⟨h0, h1⟩ := R.hdom t ht
    have a := refl_bound R.cr R.hcr h0 h1 _ _ R.chkR
    have b := opp_bound h0 h1 _ _ R.chkO
    have c := col_bound h0 h1 _ _ _ 0 R.chkC
    have d := R.hLog t ht
    simp only [avQ_append]
    simp only [Rat.cast_zero, mul_zero, zero_mul, add_zero] at c
    linarith

/-- **The moved free row from the two certificates** (`R0` at `H = h0`, `R1` at `H = h0 + h1`). -/
theorem movedRowCap_of_checks (h : ℝ → ℝ) {cap : ℝ}
    (P : RowCertMv Sign.pos (Ioo (0 : ℝ) 1) cap (fun t => h (sgOf Sign.pos * t)))
    (N : RowCertMv Sign.neg (Ioc (0 : ℝ) 1) cap (fun t => h (sgOf Sign.neg * t))) :
    ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + h x ≤ cap := by
  intro x hx
  obtain ⟨he, h0, h1⟩ := x_eq_sg_abs (σ := signOf x) hx rfl
  have hle := CompactSource.rowField_exact_le capSource capSource_admissible 384 (signOf x) Flavor.free
    (some 0) h1
  show capSource.rowField Trunc.exact (signOf x) Flavor.free (some 0) x + h x ≤ _
  refine (add_le_add_left hle _).trans ?_
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · have hs : signOf x = Sign.neg := by simp [signOf, b]
    rw [hs] at he ⊢
    have := N.le |x| ⟨h0, h1⟩
    beta_reduce at this
    rwa [← he] at this
  · have hs : signOf x = Sign.pos := by simp [signOf, not_lt.2 a.le]
    rw [hs] at he ⊢
    have := P.le |x| ⟨h0, by rw [abs_of_pos a]; exact b⟩
    beta_reduce at this
    rwa [← he] at this

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
