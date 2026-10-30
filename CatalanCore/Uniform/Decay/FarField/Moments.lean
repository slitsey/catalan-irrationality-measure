module

public import CatalanCore.Uniform.Decay.NearCells.Cell

@[expose] public section
set_option Elab.async false

/-!
# Exact moments of a piecewise-polynomial measure (lane D, package D15)

A piece `P` is the measure `w · dens(t) dt` carried by `A + t (B - A)`, `t ∈ [0,1]`.
Its moment about `c` of order `k` is `∫ dens(t) (A + t(B-A) - c)^k dt`.  Everything below is
computed from the rational data by structural recursion over Gaussian rationals `CQ`.

* `Tm a j = ∫ t^j dens` (rational);
* `pieceMoms P c K` the list of the moments of orders `1..K`, `momList ps c K` the `w`-weighted sum;
* `momList_getD`: the `k`-th entry (as a complex number) is `∑_P w_P ∫ dens (p(t) - c)^k dt`.
-/

namespace CatalanCore.Uniform.Decay.FarField

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.NearCells

/-- `∫_0^1 t^j dens(t) dt` for the density with coefficient list `a`. -/
def Tm (a : List ℚ) (j : ℕ) : ℚ :=
  ∑ i ∈ range (a.length - 1 + 1), coeffs a i / ((i : ℚ) + j + 1)

theorem integral_dens_pow (a : List ℚ) (j : ℕ) :
    ∫ t in (0 : ℝ)..1, ratPoly a t * t ^ j = (Tm a j : ℝ) := by
  unfold ratPoly Tm
  have : ∀ t : ℝ, (∑ i ∈ range (a.length - 1 + 1), ((coeffs a i : ℚ) : ℝ) * t ^ i) * t ^ j
      = ∑ i ∈ range (a.length - 1 + 1), ((coeffs a i : ℚ) : ℝ) * t ^ (i + j) := by
    intro t; rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  simp
  ring

/-! ### The moment of one piece -/

/-- Powers `cur, cur·a, ..., cur·a^(n-1)`. -/
def powsFrom (a cur : CQ) : ℕ → List CQ
  | 0 => []
  | n + 1 => cur :: powsFrom a (CQ.mul cur a) n

theorem powsFrom_getD (a : CQ) : ∀ (n : ℕ) (cur : CQ) (i : ℕ), i < n →
    ((powsFrom a cur n).getD i CQ.zero).toC = cur.toC * a.toC ^ i
  | 0, _, i, h => by omega
  | n + 1, cur, 0, _ => by simp [powsFrom]
  | n + 1, cur, i + 1, h => by
    have := powsFrom_getD a n (CQ.mul cur a) i (by omega)
    simp only [powsFrom, List.getD_cons_succ]
    rw [this, CQ.toC_mul]; ring

/-- `∑_{j ≤ k} C(k,j) T_j u^(k-j) v^j` from the power lists `u`, `v` and the list `T`. -/
def momRow (u v : List CQ) (T : List ℚ) (k : ℕ) : CQ :=
  CQ.sumTo (fun j => CQ.smul ((k.choose j : ℚ) * T.getD j 0)
    (CQ.mul (u.getD (k - j) CQ.zero) (v.getD j CQ.zero))) (k + 1)

/-- The moments of orders `1..K` of the piece (unweighted). -/
def pieceMoms (P : WP) (c : CQ) (K : ℕ) : List CQ :=
  let u := powsFrom (CQ.sub P.A c) CQ.one (K + 1)
  let v := powsFrom (CQ.sub P.B P.A) CQ.one (K + 1)
  let T := (List.range (K + 1)).map (Tm P.a)
  (List.range K).map fun k => momRow u v T (k + 1)

/-- The semantic moment of order `k` of `P` about `c`. -/
noncomputable def momSem (P : WP) (c : ℂ) (k : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1, ((ratPoly P.a t : ℝ) : ℂ) *
    (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC) - c) ^ k

theorem mom_integral (a : List ℚ) (u V : ℂ) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, ((ratPoly a t : ℝ) : ℂ) * (u + (t : ℂ) * V) ^ k
      = ∑ j ∈ range (k + 1), (k.choose j : ℂ) * (Tm a j : ℂ) * u ^ (k - j) * V ^ j := by
  have hexp : ∀ t : ℝ, ((ratPoly a t : ℝ) : ℂ) * (u + (t : ℂ) * V) ^ k
      = ∑ j ∈ range (k + 1), ((ratPoly a t * t ^ j : ℝ) : ℂ) *
          ((k.choose j : ℂ) * u ^ (k - j) * V ^ j) := by
    intro t
    rw [add_comm, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  simp_rw [hexp]
  have hc : Continuous fun t : ℝ => ratPoly a t := continuous_ratPoly a
  rw [intervalIntegral.integral_finsetSum (fun j _ => by
    apply Continuous.intervalIntegrable
    have := hc
    fun_prop)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, integral_dens_pow]
  push_cast
  ring

theorem momSem_eq (P : WP) (c : ℂ) (k : ℕ) :
    momSem P c k = ∑ j ∈ range (k + 1), (k.choose j : ℂ) * (Tm P.a j : ℂ) *
      (P.A.toC - c) ^ (k - j) * (P.B.toC - P.A.toC) ^ j := by
  unfold momSem
  rw [← mom_integral]
  refine intervalIntegral.integral_congr fun t _ => ?_
  congr 2
  ring

theorem momRow_toC (P : WP) (c : CQ) (K k : ℕ) (hk : k ≤ K) :
    (momRow (powsFrom (CQ.sub P.A c) CQ.one (K + 1)) (powsFrom (CQ.sub P.B P.A) CQ.one (K + 1))
      ((List.range (K + 1)).map (Tm P.a)) k).toC = momSem P c.toC k := by
  unfold momRow
  rw [momSem_eq, CQ.toC_sumTo]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < k + 1 := Finset.mem_range.1 hj
  rw [CQ.toC_smul, CQ.toC_mul, powsFrom_getD _ _ _ _ (by omega), powsFrom_getD _ _ _ _ (by omega)]
  have hT : (List.map (Tm P.a) (List.range (K + 1))).getD j 0 = Tm P.a j := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, show j < K + 1 by omega]
  rw [hT, CQ.toC_one, CQ.toC_sub, CQ.toC_sub]
  push_cast
  ring

theorem pieceMoms_getD (P : WP) (c : CQ) (K k : ℕ) (hk : k < K) :
    ((pieceMoms P c K).getD k CQ.zero).toC = momSem P c.toC (k + 1) := by
  unfold pieceMoms
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  exact momRow_toC P c K (k + 1) (by omega)

/-! ### Weighted sums -/

/-- Entrywise sum of two lists of complex rationals (padding with zero). -/
def addCL : List CQ → List CQ → List CQ
  | [], l => l
  | l, [] => l
  | x :: xs, y :: ys => CQ.add x y :: addCL xs ys

theorem addCL_getD : ∀ (l1 l2 : List CQ) (i : ℕ),
    ((addCL l1 l2).getD i CQ.zero).toC = (l1.getD i CQ.zero).toC + (l2.getD i CQ.zero).toC
  | [], l, i => by simp [addCL, CQ.toC_zero]
  | x :: xs, [], i => by cases i <;> simp [addCL, CQ.toC_zero]
  | x :: xs, y :: ys, 0 => by simp [addCL, CQ.toC_add]
  | x :: xs, y :: ys, i + 1 => by
    simp only [addCL, List.getD_cons_succ]
    exact addCL_getD xs ys i

/-- The weighted moments `μ_k = ∑_P w_P m_{P,k}`, `k = 1..K` (entry `k - 1`). -/
def momList (ps : List WP) (c : CQ) (K : ℕ) : List CQ :=
  ps.foldr (fun P acc => addCL ((pieceMoms P c K).map (CQ.smul P.w)) acc) (List.replicate K CQ.zero)

theorem momList_getD (ps : List WP) (c : CQ) (K k : ℕ) (hk : k < K) :
    ((momList ps c K).getD k CQ.zero).toC
      = (ps.map fun P => (P.w : ℂ) * momSem P c.toC (k + 1)).sum := by
  induction ps with
  | nil => simp [momList, List.getD_eq_getElem?_getD, List.getElem?_replicate, hk, CQ.toC_zero]
  | cons P ps ih =>
    have h1 : momList (P :: ps) c K
        = addCL ((pieceMoms P c K).map (CQ.smul P.w)) (momList ps c K) := rfl
    rw [h1, addCL_getD, ih]
    have hlen : k < (pieceMoms P c K).length := by simp [pieceMoms, hk]
    have h2 : (((pieceMoms P c K).map (CQ.smul P.w)).getD k CQ.zero).toC
        = (P.w : ℂ) * momSem P c.toC (k + 1) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen]
      simp only [Option.map_some, Option.getD_some]
      rw [CQ.toC_smul]
      congr 1
      rw [← pieceMoms_getD P c K k hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
      rfl
    rw [h2]; simp

end CatalanCore.Uniform.Decay.FarField
