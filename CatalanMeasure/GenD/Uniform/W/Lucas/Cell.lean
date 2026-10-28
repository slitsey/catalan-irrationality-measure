module
public import CatalanMeasure.GenD.Uniform.W.Lucas.Family
public import CatalanMeasure.GenD.Uniform.W.Lucas.PolyFam
public import CatalanMeasure.GenD.Uniform.W.Lucas.Transfer
@[expose] public section
set_option Elab.async false

/-!
# Rational J-affine cells and the interval form of Theorem A

`ACell`: one rational cell `(S; Jlo..Jhi; blocks k0..k0+K-1; integer profile y)` for which
`D(J) = PhiTm(J,S-1;y) - PhiTm(J,S;y)` is affine in `J` on `[Jlo, Jhi]`:
`D(J) = D(Jlo) + (J - Jlo)(D(Jlo+1) - D(Jlo))` (checked over `ℚ` by `decide +kernel`).

`cellA_le_nullity` : for an interval `[lo, hi)` of positions all of whose columns lie in the cell and
whose pair offsets `< hi - dh` stay inside the rows (`dh = h - p`, `p ≤ h ≤ q`, `2 dh < p`):
`dh + (hi - lo) ≤ ν + p` for every prime `p` coprime to the modulus.
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.LStar
  CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.MTGlue
noncomputable section

/-- One J-affine rational cell of Theorem A. `Ub`, `Jb` bound the moment tables. -/
structure ACell where
  Ub : ℕ
  Jb : ℕ
  S : ℕ
  Jlo : ℕ
  Jhi : ℕ
  K : ℕ
  k0 : ℤ
  y : ℕ → ℤ
  ky : ℕ
  hS : 2 ≤ S ∧ S + 3 ≤ Ub
  hJ : 1 ≤ Jlo ∧ Jlo + 1 ≤ Jhi ∧ Jhi < Jb
  hky : ky < K

/-- `D(J) = PhiTm(J, S-1; y) - PhiTm(J, S; y)` over `ℚ`. -/
def ACell.D (c : ACell) (J : ℕ) : ℚ :=
  Q.PhiQ (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) J (c.S - 1) -
    Q.PhiQ (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) J c.S

/-- The affine equations of a cell. -/
def ACell.Affine (c : ACell) : Prop :=
  ∀ J ∈ List.range' c.Jlo (c.Jhi + 1 - c.Jlo),
    c.D J = c.D c.Jlo + (((J : ℤ) - c.Jlo : ℤ) : ℚ) * (c.D (c.Jlo + 1) - c.D c.Jlo)

/-- The bad-prime integer of a cell. -/
def ACell.modulus (c : ACell) : ℕ := ZmB c.Ub c.Jb * (c.y c.ky).natAbs

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem ACell.units (c : ACell) (h : Nat.Coprime p c.modulus) : BUnits c.Ub c.Jb p :=
  BUnits.of_coprime (Nat.Coprime.coprime_dvd_right (dvd_mul_right (ZmB c.Ub c.Jb) _) h)

theorem ACell.z_ne (c : ACell) (h : Nat.Coprime p c.modulus) :
    zprof p c.K c.y ≠ 0 := by
  intro h0
  have h1 : ((c.y c.ky : ℤ) : ZMod p) = 0 := congrFun h0 ⟨c.ky, c.hky⟩
  have h2 : (p : ℤ) ∣ c.y c.ky := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1
  have h3 : p ∣ (c.y c.ky).natAbs := Int.natCast_dvd.mp h2
  have h4 : p ∣ c.modulus := by
    unfold ACell.modulus
    exact h3.mul_left _
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl h4)

theorem ACell.D_mem (c : ACell) (hm : BUnits c.Ub c.Jb p) {J : ℕ} (hJ : J < c.Jb) :
    c.D J ∈ unitSub p := by
  have hS := c.hS
  have hA := phiQ_mem hm (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) hJ
    (by omega : c.S - 1 + 3 ≤ c.Ub)
  have hB := phiQ_mem hm (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) hJ
    (by omega : c.S + 3 ≤ c.Ub)
  exact Subring.sub_mem _ hA hB

/-- The slope of the cell: `res D(Jlo + 1) - res D(Jlo)`. -/
def ACell.beta (c : ACell) (p : ℕ) [Fact p.Prime] : ZMod p :=
  palindromicRatResidue p (c.D (c.Jlo + 1)) - palindromicRatResidue p (c.D c.Jlo)

/-- The intercept of the cell: `res D(Jlo) - Jlo β`. -/
def ACell.alpha (c : ACell) (p : ℕ) [Fact p.Prime] : ZMod p :=
  palindromicRatResidue p (c.D c.Jlo) - (c.Jlo : ZMod p) * c.beta p

/-- The cell difference `ψ(S-1) - ψ(S)` is `α + β J` on the digits of the cell. -/
theorem ACell.psi_diff (c : ACell) (hA : c.Affine) (hm : BUnits c.Ub c.Jb p) {H J : ℕ}
    (hJ : c.Jlo ≤ J ∧ J ≤ c.Jhi) (hH : c.S + 3 ≤ H) :
    (profY p c.K c.k0).psi H J (((c.S - 1 : ℕ) : ℤ)) (zprof p c.K c.y) -
      (profY p c.K c.k0).psi H J ((c.S : ℕ) : ℤ) (zprof p c.K c.y) =
      c.alpha p + c.beta p * (J : ZMod p) := by
  have hJb : J < c.Jb := by have := c.hJ.2.2; omega
  have hS := c.hS
  have hJ1 : c.Jlo + 1 < c.Jb := by have := c.hJ.2.2; have := c.hJ.2.1; omega
  rw [psiY_eqB hm c.K c.k0 c.y hJb (by omega) (by omega),
    psiY_eqB hm c.K c.k0 c.y hJb (by omega) hH]
  have hA1 := phiQ_mem hm (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) hJb
    (by omega : c.S - 1 + 3 ≤ c.Ub)
  have hB1 := phiQ_mem hm (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) hJb
    (by omega : c.S + 3 ≤ c.Ub)
  have h1 := res_sub (p := p) hA1 hB1
  rw [← h1.2]
  have hmem : J ∈ List.range' c.Jlo (c.Jhi + 1 - c.Jlo) := by
    rw [List.mem_range'_1]; omega
  have he := hA J hmem
  -- lift to the unit subring
  let u : ℕ → unitSub p := fun I => if h : I < c.Jb then ⟨c.D I, c.D_mem hm h⟩ else 0
  have hu : ∀ I, I < c.Jb → (u I : ℚ) = c.D I := fun I h => by simp [u, h]
  have hid : u J = u c.Jlo + (((J : ℤ) - c.Jlo : ℤ) : unitSub p) * (u (c.Jlo + 1) - u c.Jlo) := by
    apply Subtype.ext
    have h0 : c.Jlo < c.Jb := by omega
    simp only [AddMemClass.coe_add, MulMemClass.coe_mul, AddSubgroupClass.coe_sub,
      hu J hJb, hu c.Jlo h0, hu (c.Jlo + 1) hJ1]
    rw [he]
    simp
  have hres := congrArg (resHom p) hid
  simp only [map_add, map_mul, map_sub, map_intCast, resHom_apply] at hres
  have h0 : c.Jlo < c.Jb := by omega
  simp only [hu J hJb, hu c.Jlo h0, hu (c.Jlo + 1) hJ1] at hres
  have hcast : (((J : ℤ) - c.Jlo : ℤ) : ZMod p) = (J : ZMod p) - (c.Jlo : ZMod p) := by
    push_cast; ring
  rw [hcast] at hres
  unfold ACell.D at hres
  unfold ACell.alpha ACell.beta ACell.D
  rw [hres]
  ring

theorem digit_bounds (hp : 0 < p) {Jlo Jhi ℓ b L j : ℕ} (hJlo : 1 ≤ Jlo) (hℓ : ℓ < p)
    (h1 : (Jlo - 1) * p + ℓ < b) (h2 : L ≤ (Jhi + 1) * p + ℓ) (hj1 : b ≤ j) (hj2 : j < L)
    (hjl : j % p = ℓ) : Jlo ≤ j / p ∧ j / p ≤ Jhi := by
  have hdm := Nat.div_add_mod j p
  rw [hjl] at hdm
  constructor
  · by_contra hc
    have : j / p ≤ Jlo - 1 := by omega
    have := Nat.mul_le_mul_left p this
    nlinarith
  · by_contra hc
    have : Jhi + 1 ≤ j / p := by omega
    have := Nat.mul_le_mul_left p this
    nlinarith

theorem good_of_ends {K D : ℕ} (k0 : ℤ)
    (hlow : -(P.g N : ℤ) ≤ k0 * p - (D : ℤ))
    (hup : (k0 + (K : ℤ) - 1) * p + (D : ℤ) < (P.n N : ℤ) - P.g N) (d : Fin D) (k : Fin K) :
    Good P N p k0 d k := by
  have hp0 : (0 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).pos.le
  have hk : (k : ℕ) + 1 ≤ K := k.isLt
  have hd := d.isLt
  have e1 : k0 * p ≤ (k0 + (k : ℕ)) * p := by nlinarith
  have e2 : (k0 + (k : ℕ)) * p ≤ (k0 + (K : ℤ) - 1) * p := by
    apply mul_le_mul_of_nonneg_right _ hp0
    have : ((k : ℕ) : ℤ) + 1 ≤ K := by exact_mod_cast hk
    linarith
  unfold Good InRange cen
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast <;> nlinarith

theorem sub_one_pow_p : ((X - 1 : (ZMod p)[X])) ^ p = X ^ p - 1 := by
  rw [sub_pow_char, one_pow]

set_option maxHeartbeats 1600000 in
/-- **The kernel family of Theorem A for an interval of positions.** -/
theorem cellA_family (hP : Admissible P) (hN : 0 < N) (hH : P.H N < p ^ 2)
    (hpq : p ≤ P.q N) (hph : p ≤ P.h N) (hhq : P.h N ≤ P.q N) (hdh : 2 * (P.h N - p) < p)
    (c : ACell) (hc : c.Affine) (hcop : Nat.Coprime p c.modulus) {lo hi : ℕ} (hlh : lo ≤ hi)
    (hhi : hi ≤ p) (hdhi : P.h N - p ≤ hi) (hDp : hi - (P.h N - p) ≤ (p - 1) / 2)
    (hlow : -(P.g N : ℤ) ≤ c.k0 * p - ((hi - (P.h N - p) : ℕ) : ℤ))
    (hup : (c.k0 + (c.K : ℤ) - 1) * p + ((hi - (P.h N - p) : ℕ) : ℤ) < (P.n N : ℤ) - P.g N)
    (hwin : ∀ e, lo ≤ e → e < hi →
      c.S * p + e + 1 ≤ P.H N ∧ P.H N ≤ (c.S + 1) * p + e ∧
      (c.Jlo - 1) * p + (P.H N - 1 - e - c.S * p) < P.b N ∧
      P.L N ≤ (c.Jhi + 1) * p + (P.H N - 1 - e - c.S * p)) :
    (P.h N - p) + (hi - lo) ≤ nullity P N p + p := by
  classical
  have hm := c.units hcop
  have hp2 := hm.hp2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  set dh := P.h N - p with hdhdef
  set D := hi - dh with hDdef
  have hdhp : dh ≤ p := by omega
  -- the atom space
  let Pm : famSpace p dh lo hi →ₗ[ZMod p] (ZMod p)[X] :=
    (degreeLT (ZMod p) dh).subtype.comp (famSpace p dh lo hi).subtype
  let Gm : famSpace p dh lo hi →ₗ[ZMod p] (ZMod p)[X] := (gOf p).comp Pm
  have hPdeg : ∀ a, (Pm a).degree < (dh : WithBot ℕ) := fun a =>
    Polynomial.mem_degreeLT.mp a.1.2
  have hdvd : ∀ a, (X - 1 : (ZMod p)[X]) ^ dh ∣ Gm a := fun a => dvd_gOf hdh (Pm a) (hPdeg a)
  have hGsupp : ∀ a e, (Gm a).coeff e ≠ 0 → lo ≤ e ∧ e < hi := fun a e he =>
    gOf_coeff_supp a e he
  have hGdeg : ∀ a, (Gm a).degree < (hi : WithBot ℕ) := by
    intro a
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro e he
    by_contra hne
    have := hGsupp a e hne
    omega
  have hGinj : ∀ a, Gm a = 0 → a = 0 := by
    intro a ha
    have h0 : Pm a = 0 := gOf_injective hdhp (Pm a) (hPdeg a) ha
    have : a.1 = 0 := Subtype.ext h0
    exact Subtype.ext this
  -- division by (X-1)^dh
  have hne : ((X - 1 : (ZMod p)[X]) ^ dh) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero 1)
  let M : (ZMod p)[X] →ₗ[ZMod p] (ZMod p)[X] := LinearMap.mulLeft (ZMod p) ((X - 1 : (ZMod p)[X]) ^ dh)
  have hMinj : Function.Injective M := fun a b h => mul_left_cancel₀ hne h
  let eM := LinearEquiv.ofInjective M hMinj
  have hmemM : ∀ a, Gm a ∈ LinearMap.range M := by
    intro a
    obtain ⟨t, ht⟩ := hdvd a
    exact ⟨t, by simp [M, ht]⟩
  let σL : famSpace p dh lo hi →ₗ[ZMod p] (ZMod p)[X] :=
    eM.symm.toLinearMap.comp (LinearMap.codRestrict (LinearMap.range M) Gm hmemM)
  have hσ : ∀ a, (X - 1 : (ZMod p)[X]) ^ dh * σL a = Gm a := by
    intro a
    have h2 : M (eM.symm ⟨Gm a, hmemM a⟩) = Gm a := by
      have := congrArg Subtype.val (eM.apply_symm_apply ⟨Gm a, hmemM a⟩)
      simpa [eM] using this
    exact h2
  have hσdeg : ∀ a, σL a ∈ degreeLT (ZMod p) D := by
    intro a
    rw [Polynomial.mem_degreeLT]
    by_cases h0 : σL a = 0
    · rw [h0]; exact WithBot.bot_lt_coe D
    · have hG := hGdeg a
      rw [← hσ a, Polynomial.degree_mul, Polynomial.degree_pow] at hG
      have h1 : (X - 1 : (ZMod p)[X]).degree = 1 := by
        have : (X - 1 : (ZMod p)[X]) = X - C 1 := by simp
        rw [this]; exact Polynomial.degree_X_sub_C 1
      rw [h1] at hG
      rw [Polynomial.degree_eq_natDegree h0] at hG ⊢
      simp only [nsmul_eq_mul, mul_one] at hG
      have : dh + (σL a).natDegree < hi := by exact_mod_cast hG
      have : (σL a).natDegree < D := by omega
      exact_mod_cast this
  let ψC : famSpace p dh lo hi →ₗ[ZMod p] degreeLT (ZMod p) D :=
    LinearMap.codRestrict _ σL hσdeg
  let wm : famSpace p dh lo hi →ₗ[ZMod p] (Fin D → ZMod p) :=
    (uBasisEquiv hp2 D).symm.toLinearMap.comp ψC
  have hwm : Function.Injective wm := by
    intro a b hab
    have h1 : ψC a = ψC b := (uBasisEquiv hp2 D).symm.injective hab
    have h2 : σL a = σL b := congrArg Subtype.val h1
    have h3 : Gm a = Gm b := by rw [← hσ a, ← hσ b, h2]
    have h4 : Gm (a - b) = 0 := (LinearMap.map_sub Gm a b).trans (by rw [h3, sub_self])
    exact sub_eq_zero.mp (hGinj _ h4)
  have hrel : ∀ a, (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D (wm a) = (X ^ p - 1) * Gm a := by
    intro a
    have : uComb p D (wm a) = σL a := uBasisEquiv_symm_comb hp2 D (ψC a)
    have hh : P.h N = p + dh := by omega
    rw [this, hh, pow_add, sub_one_pow_p, ← hσ a]
    ring
  have hsupp : ∀ a e, (Gm a).coeff e ≠ 0 → e < hi := fun a e he => (hGsupp a e he).2
  have hcoef : ∀ a e, e < p → (Gm a).coeff e = (Pm a).eval (e : ZMod p) := by
    intro a e he
    simp only [Gm, LinearMap.comp_apply, gOf_coeff, if_pos he]
  have hPdeg' : ∀ a, (Pm a).degree < ((P.q N - p : ℕ) : WithBot ℕ) := by
    intro a
    refine lt_of_lt_of_le (hPdeg a) ?_
    exact_mod_cast (by omega : dh ≤ P.q N - p)
  have hgood : ∀ (d : Fin D) (k : Fin c.K), Good P N p c.k0 d k := fun d k =>
    good_of_ends c.k0 hlow hup d k
  have hz := c.z_ne hcop
  have hS := c.hS
  have hcellp : ∀ a : famSpace p dh lo hi, ∀ j, P.b N ≤ j → j < P.L N →
      (Gm a).coeff (idxRes (P.H N) p (j % p)) ≠ 0 →
      psiLin p c.K c.k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p) - 1) (zprof p c.K c.y) -
        psiLin p c.K c.k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p)) (zprof p c.K c.y) =
        c.alpha p + c.beta p * ((j / p : ℕ) : ZMod p) := by
      intro a j hj1 hj2 hne'
      have hjH : j < P.H N := lt_of_lt_of_le hj2 (by
        have : P.H N = P.L N + P.g N + P.h N := by simp [Parameters.H, Parameters.C]
        omega)
      set ℓ := j % p with hℓdef
      set e0 := idxRes (P.H N) p ℓ with he0def
      have hℓ : ℓ < p := Nat.mod_lt _ hp0
      have he0 := idxRes_lt hp0 (P.H N) ℓ
      have hidx := idx_eq hp0 (P.H N) ℓ
      rw [← he0def] at hidx
      have hrng : lo ≤ e0 ∧ e0 < hi := hGsupp a _ hne'
      obtain ⟨w1, w2, w3, w4⟩ := hwin e0 hrng.1 hrng.2
      obtain ⟨Sp, hSp⟩ : ∃ Sp, Sp = c.S * p := ⟨_, rfl⟩
      obtain ⟨Sp1, hSp1⟩ : ∃ Sp1, Sp1 = (c.S + 1) * p := ⟨_, rfl⟩
      have hSp1' : Sp1 = Sp + p := by rw [hSp, hSp1]; ring
      rw [← hSp] at w1 w3 w4
      rw [← hSp1] at w2
      set ℓe := P.H N - 1 - e0 - Sp with hℓe
      have hℓe_lt : ℓe < p := by omega
      have hq1 : (idxQuo (P.H N) p ℓ) = (c.S : ℤ) ∧ ℓ = ℓe := by
        have hSpz : (Sp : ℤ) = (c.S : ℤ) * p := by rw [hSp]; push_cast; ring
        have h5 : ((idxQuo (P.H N) p ℓ) - c.S) * (p : ℤ) = (ℓe : ℤ) - ℓ := by
          have this' : (ℓe : ℤ) = (P.H N : ℤ) - 1 - e0 - Sp := by omega
          linear_combination (-1 : ℤ) * hidx - this' + hSpz
        have := Thin.no_mult _ _ (by exact_mod_cast hp0) (by omega) (by omega) h5
        omega
      obtain ⟨hq1a, hq1b⟩ := hq1
      have hdig := digit_bounds hp0 c.hJ.1 hℓ (by rw [hq1b]; exact w3) (by
          rw [hq1b]; exact w4) hj1 hj2 rfl
      have e1 : idxQuo (P.H N) p (j % p) - 1 = ((c.S - 1 : ℕ) : ℤ) := by
        rw [hq1a]; push_cast [Nat.cast_sub (by omega : 1 ≤ c.S)]; ring
      rw [e1, hq1a]
      exact c.psi_diff hc hm hdig (by
        have : c.S * p + 1 ≤ P.H N := by omega
        nlinarith [hS.1, (Fact.out : p.Prime).two_le])
  have key := lucas_fam_le_nullity (A := famSpace p dh lo hi) hP hN hp2 hH hpq c.k0 (zprof p c.K c.y) hz (by omega) hgood
    wm hwm Gm Pm hi hrel hsupp hhi (by omega) hcoef hPdeg' (c.alpha p) (c.beta p) hcellp
  have hfr := finrank_famSpace_ge (dh := dh) hlh hhi (p := p)
  omega

#print axioms cellA_family
end
end CatalanMeasure.GenD.Uniform.W.Lucas
