module

public import CatalanCore.Star.Leonard.ChainDS
public import CatalanCore.Star.Leonard.NuClosed
public import CatalanCore.Star.Leonard.GoodF0

/-!
# The diagonal-step ratio in closed form (package H7, (B1))

`uu m n S θ = u(Ã_{θ,S}, Π c_S)`.  The explicit diagonal step `ds_explicit` gives

`uu (S+1) (θ-1) = uu S θ · Rinv`,   `Rinv = κ · ∏_{j<n-1} ((θ+K-1-j)/(θ+j))^{2(n-1-j)}`

with `κ` an explicit product of integers (`ℓ`-unit).  The `θ`-part is the finite product identity
`Id1`; all the intermediate factors with negative shifts cancel.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

/-! ### `τ`, `σ` at the chain points: a constant times two linear factors -/

/-- constant part of `l(y) = -τ(-θ-y)` -/
noncomputable def clc (m S K : ℕ) (y : ℤ) : ℚ :=
  (1 - (y : ℚ)) * (∏ i ∈ range (m + 1), ((S : ℚ) + 2 * (i : ℚ) + 1 - (y : ℚ))) /
    ∏ i ∈ range m, ((S : ℚ) + 2 * ((i : ℚ) + 1) - (y : ℚ))

/-- constant part of `r(y) = -σ(-θ-y-1)` -/
noncomputable def crc (m S K : ℕ) (y : ℤ) : ℚ :=
  -(y : ℚ) * (∏ i ∈ range m, ((S : ℚ) + 2 * ((i : ℚ) + 1) - (y : ℚ) - 1)) /
    ∏ i ∈ range (m - 1), ((S : ℚ) + 2 * ((i : ℚ) + 1) - (y : ℚ))

lemma neg_tau_at (K m S : ℕ) (θ : ℚ) (y : ℤ) :
    -tau K m S θ (-θ - (y : ℚ)) =
      clc m S K y * ((θ + (y : ℚ) - 1) * (θ + (K : ℚ) - 1 + (y : ℚ))) := by
  have hQ : Qf m S θ (-θ - (y : ℚ)) = ∏ i ∈ range (m + 1), ((S : ℚ) + 2 * (i : ℚ) + 1 - (y : ℚ)) :=
    Finset.prod_congr rfl fun i _ => by ring
  have hP : Pe m S θ (-θ - (y : ℚ)) = ∏ i ∈ range m, ((S : ℚ) + 2 * ((i : ℚ) + 1) - (y : ℚ)) :=
    Finset.prod_congr rfl fun i _ => by ring
  unfold tau clc pp
  rw [hQ, hP]
  ring

lemma neg_sigma_at (K m S : ℕ) (θ : ℚ) (y : ℤ) :
    -sigma K m S θ (-θ - (y : ℚ) - 1) =
      crc m S K y * ((θ + (y : ℚ)) * (θ + (K : ℚ) + (y : ℚ))) := by
  have hQ : Qo m S θ (-θ - (y : ℚ) - 1) =
      ∏ i ∈ range (m - 1), ((S : ℚ) + 2 * ((i : ℚ) + 1) - (y : ℚ)) :=
    Finset.prod_congr rfl fun i _ => by ring
  have hP : Pe m S θ (-θ - (y : ℚ) - 1) =
      ∏ i ∈ range m, ((S : ℚ) + 2 * ((i : ℚ) + 1) - (y : ℚ) - 1) :=
    Finset.prod_congr rfl fun i _ => by ring
  unfold sigma crc pp
  rw [hQ, hP]
  ring

/-! ### The leading-coefficient products split into constant and `θ`-part -/

noncomputable def dnC (m S K n : ℕ) (y0 : ℤ) : ℚ :=
  ∏ k ∈ range n, ∏ j ∈ range k, clc m S K (y0 - (j : ℤ))

noncomputable def dnT (K n : ℕ) (θ : ℚ) (y0 : ℤ) : ℚ :=
  ∏ k ∈ range n, ∏ j ∈ range k,
    ((θ + ((y0 - (j : ℤ) : ℤ) : ℚ) - 1) * (θ + (K : ℚ) - 1 + ((y0 - (j : ℤ) : ℤ) : ℚ)))

noncomputable def upC (m S K n : ℕ) (y1 : ℤ) : ℚ :=
  ∏ k ∈ range n, ∏ j ∈ range k, crc m S K (y1 + (j : ℤ))

noncomputable def upT (K n : ℕ) (θ : ℚ) (y1 : ℤ) : ℚ :=
  ∏ k ∈ range n, ∏ j ∈ range k,
    ((θ + ((y1 + (j : ℤ) : ℤ) : ℚ)) * (θ + (K : ℚ) + ((y1 + (j : ℤ) : ℤ) : ℚ)))

lemma lprodDown_eq (m n S : ℕ) (θ : ℚ) (y0 : ℤ) :
    lprodDown m n S θ y0 = dnC m S (m + n) n y0 * dnT (m + n) n θ y0 := by
  unfold lprodDown dnC dnT
  rw [Fin.prod_univ_eq_prod_range (fun k => ∏ j ∈ range k,
    (-tau (m + n) m S θ (-θ - (((y0 - (j : ℤ) : ℤ) : ℤ) : ℚ)))) n]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact neg_tau_at (m + n) m S θ (y0 - (j : ℤ))

lemma lprodUp_eq (m n S : ℕ) (θ : ℚ) (y1 : ℤ) :
    lprodUp m n S θ y1 = upC m S (m + n) n y1 * upT (m + n) n θ y1 := by
  unfold lprodUp upC upT
  rw [Fin.prod_univ_eq_prod_range (fun k => ∏ j ∈ range k,
    (-sigma (m + n) m S θ (-θ - (((y1 + (j : ℤ) : ℤ) : ℤ) : ℚ) - 1))) n]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact neg_sigma_at (m + n) m S θ (y1 + (j : ℤ))

/-! ### `cauFac` splits into a constant, the `Y`-part and the chain part -/

lemma cauFac_split {m n : ℕ} (θ : ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ) :
    cauFac θ (Fin.addCases a b : Fin (m + n) → ℚ) =
      cnum (Fin.addCases a b : Fin (m + n) → ℚ) /
        ((∏ i : Fin (m + n), ∏ j : Fin m, (θ + ((i : ℕ) : ℚ) + a j)) *
          ∏ i : Fin (m + n), ∏ j : Fin n, (θ + ((i : ℕ) : ℚ) + b j)) := by
  unfold cauFac cnum
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_add]
  simp

/-! ### The `θ`-identity of the diagonal step -/

section Id1

variable (K : ℕ) (θ : ℚ)

/-- `∏_{k<n} ∏_{j<k} (θ-j-1)(θ+K-1-j)` -/
noncomputable def Lp1 (n : ℕ) : ℚ := ∏ k ∈ range n, ∏ j ∈ range k, ((θ - j - 1) * (θ + K - 1 - j))
/-- `∏_{k<n} ∏_{j<k} (θ+j)(θ+K+j)` -/
noncomputable def Mp1 (n : ℕ) : ℚ := ∏ k ∈ range n, ∏ j ∈ range k, ((θ + j) * (θ + K + j))
/-- `∏_{i<K} ∏_{j<n} (θ+i+j)/(θ+i-j)` -/
noncomputable def Ph1 (n : ℕ) : ℚ := ∏ i ∈ range K, ∏ j ∈ range n, ((θ + i + j) / (θ + i - j))
noncomputable def Tp1 (n : ℕ) : ℚ :=
  ∏ j ∈ range n, ((θ + K - 1 - j) / (θ + j)) ^ (2 * (n - 1 - j))

variable (hθ0 : 0 < θ) (hθ : Gen θ)

include hθ in
lemma gen_int (z : ℤ) : θ + (z : ℚ) ≠ 0 := hθ z

lemma tele_div (u : ℕ → ℚ) (hu : ∀ j, u j ≠ 0) (n : ℕ) :
    ∏ j ∈ range n, (u (j + 1) / u j) = u n / u 0 := by
  induction n with
  | zero => simp [div_self (hu 0)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have := hu n; have := hu 0
    field_simp

include hθ hθ0 in
lemma pochr_ratio (n : ℕ) : ∀ K : ℕ, ∏ i ∈ range K, ((θ + i + n) / (θ + i - n)) =
    ∏ j ∈ range n, ((θ + K + j) * (θ + K - 1 - j) / ((θ + j) * (θ - 1 - j))) := by
  have hne : ∀ z : ℤ, θ + (z : ℚ) ≠ 0 := hθ
  have hp : ∀ j : ℕ, θ + (j : ℚ) ≠ 0 := fun j => lin_pos0 hθ0 j
  intro K
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, add_zero]
    symm
    refine Finset.prod_eq_one fun j _ => ?_
    have h2 : θ - 1 - (j : ℚ) ≠ 0 := by
      have := hne (-1 - (j : ℤ)); push_cast at this; intro h; apply this; linear_combination h
    have h1 := hp j
    field_simp
  | succ K ih =>
    rw [Finset.prod_range_succ, ih]
    have hu : ∀ j : ℕ, θ + (K : ℚ) + (j : ℚ) ≠ 0 := fun j => by
      have : θ + (K : ℚ) + (j : ℚ) = θ + (((K + j : ℕ)) : ℚ) := by push_cast; ring
      rw [this]; exact hp _
    have hw : ∀ j : ℕ, θ + (K : ℚ) - (j : ℚ) ≠ 0 := fun j => by
      have := hne ((K : ℤ) - (j : ℤ)); push_cast at this; intro h; apply this; linear_combination h
    have hw1 : ∀ j : ℕ, θ + (K : ℚ) - 1 - (j : ℚ) ≠ 0 := fun j => by
      have := hne ((K : ℤ) - 1 - (j : ℤ)); push_cast at this; intro h; apply this; linear_combination h
    have h2 : ∀ j : ℕ, θ - 1 - (j : ℚ) ≠ 0 := fun j => by
      have := hne (-1 - (j : ℤ)); push_cast at this; intro h; apply this; linear_combination h
    -- the product of the ratios telescopes
    have key : ∏ j ∈ range n, ((θ + ((K + 1 : ℕ) : ℚ) + j) * (θ + ((K + 1 : ℕ) : ℚ) - 1 - j) /
        ((θ + j) * (θ - 1 - j))) =
        (∏ j ∈ range n, ((θ + K + j) * (θ + K - 1 - j) / ((θ + j) * (θ - 1 - j)))) *
          ((θ + K + n) / (θ + K - n)) := by
      have hr : ∀ j ∈ range n, ((θ + ((K + 1 : ℕ) : ℚ) + j) * (θ + ((K + 1 : ℕ) : ℚ) - 1 - j) /
          ((θ + j) * (θ - 1 - j))) =
          ((θ + K + j) * (θ + K - 1 - j) / ((θ + j) * (θ - 1 - j))) *
            (((θ + K + ((j + 1 : ℕ) : ℚ)) / (θ + K + (j : ℚ))) *
              ((θ + K - (j : ℚ)) / (θ + K - ((j + 1 : ℕ) : ℚ)))) := by
        intro j _
        have h3 := hu j
        have h4 := hw1 j
        have h5 := hp j
        have h6 := h2 j
        push_cast
        have h7 : θ + (K : ℚ) - ((j : ℚ) + 1) ≠ 0 := by intro h; apply h4; linear_combination h
        field_simp
        ring
      rw [Finset.prod_congr rfl hr, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      congr 1
      have e1 := tele_div (fun j : ℕ => θ + (K : ℚ) + (j : ℚ)) hu n
      have e2 := tele_div (fun j : ℕ => θ + (K : ℚ) - (j : ℚ)) hw n
      have e3 : ∏ j ∈ range n, ((θ + (K : ℚ) - (j : ℚ)) / (θ + (K : ℚ) - ((j + 1 : ℕ) : ℚ))) =
          (θ + (K : ℚ) - ((0 : ℕ) : ℚ)) / (θ + (K : ℚ) - (n : ℚ)) := by
        have : ∏ j ∈ range n, ((θ + (K : ℚ) - (j : ℚ)) / (θ + (K : ℚ) - ((j + 1 : ℕ) : ℚ))) =
            ∏ j ∈ range n, ((θ + (K : ℚ) - ((j + 1 : ℕ) : ℚ)) / (θ + (K : ℚ) - (j : ℚ)))⁻¹ :=
          Finset.prod_congr rfl fun j _ => (inv_div _ _).symm
        rw [this, Finset.prod_inv_distrib]
        rw [e2, inv_div]
      rw [e1, e3]
      have h0 : θ + (K : ℚ) + ((0 : ℕ) : ℚ) ≠ 0 := hu 0
      have h00 : θ + (K : ℚ) - ((0 : ℕ) : ℚ) ≠ 0 := hw 0
      have hn : θ + (K : ℚ) - (n : ℚ) ≠ 0 := hw n
      simp only [Nat.cast_zero, add_zero, sub_zero] at h0 h00 ⊢
      field_simp
    rw [key]

include hθ hθ0 in
lemma step_id (n : ℕ) :
    (∏ j ∈ range n, ((θ - j - 1) * (θ + K - 1 - j))) / (∏ j ∈ range n, ((θ + j) * (θ + K + j))) *
      ∏ i ∈ range K, ((θ + i + n) / (θ + i - n)) =
    ∏ j ∈ range n, ((θ + K - 1 - j) / (θ + j)) ^ 2 := by
  have hne : ∀ z : ℤ, θ + (z : ℚ) ≠ 0 := hθ
  rw [pochr_ratio θ hθ0 hθ n K, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : θ + (j : ℚ) ≠ 0 := lin_pos0 hθ0 j
  have h2 : θ - 1 - (j : ℚ) ≠ 0 := by
    have := hne (-1 - (j : ℤ)); push_cast at this; intro h; apply this; linear_combination h
  have h3 : θ + (K : ℚ) + (j : ℚ) ≠ 0 := by
    have : θ + (K : ℚ) + (j : ℚ) = θ + (((K + j : ℕ)) : ℚ) := by push_cast; ring
    rw [this]; exact lin_pos0 hθ0 _
  have h2' : θ - (j : ℚ) - 1 ≠ 0 := by intro h; apply h2; linear_combination h
  field_simp
  ring

include hθ hθ0 in
theorem Id1 (n : ℕ) : Lp1 K θ n / Mp1 K θ n * Ph1 K θ n = Tp1 K θ n := by
  induction n with
  | zero => simp [Lp1, Mp1, Ph1, Tp1]
  | succ n ih =>
    have hL : Lp1 K θ (n + 1) = Lp1 K θ n * ∏ j ∈ range n, ((θ - j - 1) * (θ + K - 1 - j)) := by
      unfold Lp1; rw [Finset.prod_range_succ]
    have hM : Mp1 K θ (n + 1) = Mp1 K θ n * ∏ j ∈ range n, ((θ + j) * (θ + K + j)) := by
      unfold Mp1; rw [Finset.prod_range_succ]
    have hP : Ph1 K θ (n + 1) = Ph1 K θ n * ∏ i ∈ range K, ((θ + i + n) / (θ + i - n)) := by
      unfold Ph1
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [Finset.prod_range_succ]
    have hT : Tp1 K θ (n + 1) = Tp1 K θ n * ∏ j ∈ range n, ((θ + K - 1 - j) / (θ + j)) ^ 2 := by
      unfold Tp1
      rw [Finset.prod_range_succ, ← Finset.prod_mul_distrib]
      simp only [Nat.add_sub_cancel, Nat.sub_self, mul_zero, pow_zero, mul_one]
      refine Finset.prod_congr rfl fun j hj => ?_
      have := Finset.mem_range.1 hj
      rw [← pow_add]; congr 1; omega
    have hMn : Mp1 K θ n ≠ 0 := by
      unfold Mp1
      refine Finset.prod_ne_zero_iff.2 fun k _ => Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero ?_ ?_
      · exact lin_pos0 hθ0 j
      · have : θ + (K : ℚ) + (j : ℚ) = θ + (((K + j : ℕ)) : ℚ) := by push_cast; ring
        rw [this]; exact lin_pos0 hθ0 _
    have hg : (∏ j ∈ range n, ((θ + j) * (θ + K + j))) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (lin_pos0 hθ0 j) (by
        have : θ + (K : ℚ) + (j : ℚ) = θ + (((K + j : ℕ)) : ℚ) := by push_cast; ring
        rw [this]; exact lin_pos0 hθ0 _)
    rw [hL, hM, hP, hT, ← step_id K θ hθ0 hθ n, ← ih]
    field_simp

end Id1

end CatalanCore.Star.Leonard
