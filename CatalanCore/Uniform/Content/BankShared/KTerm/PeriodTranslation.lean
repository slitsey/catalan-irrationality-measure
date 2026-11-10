module

public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodWindow
public import CatalanCore.Uniform.Content.BankShared.KTerm.Periodic

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! Generic periodic translation of D1x and PRE prices; moved unchanged from the bank consumer. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid
  CatalanCore.Basic Filter Finset Polynomial CatalanCore.Uniform.Content.BankShared.Check

/-! #### (T1) -/

theorem kMn_shift (r p m r' m' δ : ℕ) (k : ℕ → ℕ) : ∀ (l : List KExpr) (a a2 : KExpr),
    (∀ x ∈ l, x.evalN r' p m' k = x.evalN r p m k + δ) → a2.evalN r' p m' k = a.evalN r p m k + δ →
    (kMn a2 l).evalN r' p m' k = (kMn a l).evalN r p m k + δ
  | [], a, a2, _, ha => ha
  | y :: l, a, a2, hl, ha => by
    have hy := hl y (by simp)
    apply kMn_shift r p m r' m' δ k l (.mn a y) (.mn a2 y) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    simp only [KExpr.evalN, ha, hy]
    omega

theorem kMx_shift (r p m r' m' δ : ℕ) (k : ℕ → ℕ) : ∀ (l : List KExpr) (a a2 : KExpr),
    (∀ x ∈ l, x.evalN r' p m' k = x.evalN r p m k + δ) → a2.evalN r' p m' k ≤ a.evalN r p m k + δ →
    (a.evalN r p m k + δ ≤ a2.evalN r' p m' k ∨ ∃ x ∈ l, a.evalN r p m k ≤ x.evalN r p m k) →
    (kMx a2 l).evalN r' p m' k = (kMx a l).evalN r p m k + δ
  | [], a, a2, _, h1, h2 => by
    rcases h2 with h2 | ⟨x, hx, _⟩
    · exact le_antisymm h1 h2
    · exact absurd hx (by simp)
  | y :: l, a, a2, hl, h1, h2 => by
    have hy := hl y (by simp)
    apply kMx_shift r p m r' m' δ k l (.mx a y) (.mx a2 y) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    · simp only [KExpr.evalN, hy]; omega
    · rcases h2 with h2 | ⟨x, hx, hax⟩
      · left; simp only [KExpr.evalN, hy]; omega
      · rcases List.mem_cons.1 hx with rfl | hxl
        · left; simp only [KExpr.evalN, hy]; omega
        · by_cases hya : a.evalN r p m k ≤ y.evalN r p m k
          · left; simp only [KExpr.evalN, hy]; omega
          · right
            exact ⟨x, hxl, by simp only [KExpr.evalN]; omega⟩

theorem kPoleHis_shift (r p m r' m' δ : ℕ) (k : ℕ → ℕ) (hap : p * (r' / p) = p * (r / p) + δ) :
    ∀ (js : List ℕ) (i : ℕ), ∀ x ∈ kPoleHis i js, x.evalN r' p m' k = x.evalN r p m k + δ
  | [], _ => fun x hx => absurd hx (by simp [kPoleHis])
  | j :: js, i => by
    intro x hx
    simp only [kPoleHis, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [KExpr.evalN]; omega
    · exact kPoleHis_shift r p m r' m' δ k hap js (i + 1) x hx

theorem kPoleLos_shift (r p m r' m' δ : ℕ) (k : ℕ → ℕ) (hr : r' = r + δ) (hap : p * (r' / p) = p * (r / p) + δ) :
    ∀ (js : List ℕ) (i : ℕ), ∀ x ∈ kPoleLos i js, x.evalN r' p m' k = x.evalN r p m k + δ
  | [], _ => fun x hx => absurd hx (by simp [kPoleLos])
  | j :: js, i => by
    intro x hx
    simp only [kPoleLos, List.mem_cons] at hx
    rcases hx with rfl | hx
    · by_cases hj : j = 0
      · simp only [hj, ite_true, KExpr.evalN]; omega
      · simp only [hj, ite_false, KExpr.evalN]; omega
    · exact kPoleLos_shift r p m r' m' δ k hr hap js (i + 1) x hx

/-- **(T1) for the prefix branches**: moving the index by `a t` along the lattice shift of order `t` adds `t K_c p`,
`K_c = 2 b + 2 a`, to the price, at every point. -/
theorem pre_cov (a b t ν j0 j1 j2 r p m : ℕ) (kv : ℕ → ℕ) :
    (kbrPre (ν + a * t) j0 [j1, j2]).τ.evalN (r + t * b * p) p (m + t * a * p) kv =
      (kbrPre ν j0 [j1, j2]).τ.evalN r p m kv + t * (2 * b + 2 * a) * p := by
  have hap : p * ((r + t * b * p) / p) = p * (r / p) + t * b * p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · rw [show r + t * b * p = r + (t * b) * p by ring, Nat.add_mul_div_right _ _ hp]; ring
  have e1 : (ν + a * t) * p = ν * p + t * a * p := by ring
  have e2 : t * (2 * b + 2 * a) * p = 2 * (t * b * p) + 2 * (t * a * p) := by ring
  have e3 : m + t * a * p - (ν + a * t) * p = m - ν * p := by rw [e1]; omega
  have hN : (kNn (ν + a * t)).evalN (r + t * b * p) p (m + t * a * p) kv =
      (kNn ν).evalN r p m kv + t * b * p := by
    simp only [kNn, KExpr.evalN, e3]; omega
  have hhi : (kPreHi (ν + a * t) j0 [j1, j2]).evalN (r + t * b * p) p (m + t * a * p) kv =
      (kPreHi ν j0 [j1, j2]).evalN r p m kv + t * b * p := by
    unfold kPreHi
    refine kMn_shift r p m _ _ _ kv _ _ _ ?_ hN
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp only [KExpr.evalN]; omega
    · simp only [KExpr.evalN]; omega
    · exact kPoleHis_shift r p m _ _ _ kv hap _ _ x hx
  have hlo : (kPreLo (ν + a * t) j0 [j1, j2]).evalN (r + t * b * p) p (m + t * a * p) kv =
      (kPreLo ν j0 [j1, j2]).evalN r p m kv + t * b * p := by
    unfold kPreLo
    refine kMx_shift r p m _ _ _ kv _ _ _ ?_ ?_ ?_
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · (simp only [KExpr.evalN])
      · simp only [KExpr.evalN]; omega
      · exact kPoleLos_shift r p m _ _ _ kv rfl hap _ _ x hx
    · simp only [KExpr.evalN, kNn]; omega
    · by_cases hc : p ≤ r + 2 * (m - ν * p)
      · left; simp only [KExpr.evalN, kNn, e3]; omega
      · right
        exact ⟨.vr, by simp, by simp only [KExpr.evalN, kNn]; omega⟩
  have hu : (kPreHi ν j0 [j1, j2]).evalN r p m kv ≤ r + 2 * (m - ν * p) := by
    have := (kMn_le r p m kv (.add .vr .vp :: .add .ap (.smul (j0 + 1) .vp) :: kPoleHis 0 [j1, j2]) (kNn ν)).1
    simpa [kPreHi, kNn, KExpr.evalN] using this
  have hl : r ≤ (kPreLo ν j0 [j1, j2]).evalN r p m kv := by
    have := (kMx_ge r p m kv (.vr :: .add .ap (.smul j0 .vp) :: kPoleLos 0 [j1, j2]) (.tsub (kNn ν) .vp)).2 .vr
      (by simp)
    simpa [kPreLo, KExpr.evalN] using this
  simp only [kbrPre, KExpr.evalN, hhi, hlo]
  omega

/-- **(T1) for `D1x`**. -/
theorem d1x_cov (b a t r p m : ℕ) (kv : ℕ → ℕ) :
    kD1xE.evalN (r + t * b * p) p (m + t * a * p) kv = kD1xE.evalN r p m kv + t * (2 * b + 2 * a) * p := by
  have e2 : t * (2 * b + 2 * a) * p = 2 * (t * b * p) + 2 * (t * a * p) := by ring
  have hm : (m + t * a * p) % p = m % p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · rw [show t * a * p = (t * a) * p by ring, Nat.add_mul_mod_self_right]
  have hle : min (m % p) (p - m % p) ≤ m := (min_le_left _ _).trans (Nat.mod_le _ _)
  simp only [kD1xE, KExpr.evalN, hm]
  omega

/-! #### The translation of the base catalogue -/

/-- The branch `D1x` (no conditions, debit `0`). -/
def kbD1xB : KBranch := ⟨kD1xE, [], 0⟩

/-- `br` is a prefix branch `PRE(ν, j₀, j₁, j₂)`. -/
def IsPre (br : KBranch) : Prop := ∃ x : ℕ × ℕ × ℕ × ℕ, br = kbrPre x.1 x.2.1 [x.2.2.1, x.2.2.2]

open Classical in
/-- The translation of a branch: a prefix branch has its index moved by `a t`, every other branch is fixed. -/
noncomputable def preRho (a t : ℕ) (br : KBranch) : KBranch :=
  if h : IsPre br then kbrPre (h.choose.1 + a * t) h.choose.2.1 [h.choose.2.2.1, h.choose.2.2.2] else br

theorem preRho_pre {a t : ℕ} {br : KBranch} (h : IsPre br) :
    ∃ x : ℕ × ℕ × ℕ × ℕ, br = kbrPre x.1 x.2.1 [x.2.2.1, x.2.2.2] ∧
      preRho a t br = kbrPre (x.1 + a * t) x.2.1 [x.2.2.1, x.2.2.2] :=
  ⟨h.choose, h.choose_spec, by unfold preRho; rw [dif_pos h]⟩

theorem d1x_not_pre : ¬ IsPre kbD1xB := by
  rintro ⟨x, hx⟩
  have := congrArg KBranch.τ hx
  simp [kbD1xB, kD1xE, kbrPre] at this

theorem preRho_d1x (a t : ℕ) : preRho a t kbD1xB = kbD1xB := by
  unfold preRho; rw [dif_neg d1x_not_pre]

/-- The translation instance of the prefix layer on a base catalogue made of `D1x` and prefix branches. -/
noncomputable def preTransl (b a Ω : ℕ) (kb : List KBranch) (hkb : ∀ br ∈ kb, br = kbD1xB ∨ IsPre br) :
    Transl b a (2 * b + 2 * a) Ω kb where
  ρ := preRho a
  debit t br := by
    unfold preRho
    split_ifs with h
    · obtain ⟨x, hx⟩ := h
      have h0 : br.debit = 0 := by rw [hx]; rfl
      rw [h0]; rfl
    · rfl
  price t br hbr r p m kv := by
    rcases hkb br hbr with rfl | h
    · rw [preRho_d1x]; exact d1x_cov b a t r p m kv
    · obtain ⟨x, hx, hρ⟩ := preRho_pre (a := a) (t := t) h
      rw [hρ, hx]; exact pre_cov a b t x.1 x.2.1 x.2.2.1 x.2.2.2 r p m kv
  cond t br hbr r p m kv _ _ cd hcd := by
    rcases hkb br hbr with rfl | h
    · rw [preRho_d1x] at hcd; simp [kbD1xB] at hcd
    · obtain ⟨x, hx, hρ⟩ := preRho_pre (a := a) (t := t) h
      rw [hρ] at hcd; simp [kbrPre] at hcd

/-- Identity translation of the singleton D1x catalogue, at every lattice scale. -/
def d1xTranslation (b a Ω : ℕ) : Transl b a (2 * b + 2 * a) Ω [kbD1xB] where
  ρ _ br := br
  debit _ _ := rfl
  price n br hbr r p m kv := by
    simp only [List.mem_singleton] at hbr
    subst br
    exact d1x_cov b a n r p m kv
  cond n br hbr r p m kv _ _ cd hcd := by
    simp only [List.mem_singleton] at hbr
    subst br
    simp [kbD1xB] at hcd

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.d1x_cov
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.pre_cov
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.preTransl
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.d1xTranslation
