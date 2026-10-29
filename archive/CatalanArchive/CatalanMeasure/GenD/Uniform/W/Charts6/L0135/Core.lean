module
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0135.Base
public import CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Unique146
public import CatalanMeasure.GenD.Uniform.W.Charts6.DomHigh
public import CatalanMeasure.GenD.Uniform.W.Charts3.GraphJets
public import CatalanMeasure.GenD.Uniform.W.Charts6.Unit13
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Uniform.W.Charts6.L0135
section Part0
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-! ### Insertion of the 37 packet coordinates into the 49 profile coordinates -/

def iotaN (c : ℕ) : ℕ :=
  if c < 33 then 4 * (c / 3) + 1 + c % 3 else if c = 33 then 45 else if c = 34 then 46
  else if c = 35 then 47 else 48

def iotaF (c : Fin 37) : Fin 49 := ⟨iotaN c.val, by have := c.isLt; unfold iotaN; split_ifs <;> omega⟩

theorem iotaF_inj : Function.Injective iotaF := by decide +kernel

def insL (p : ℕ) [Fact p.Prime] : (Fin 37 → ZMod p) →ₗ[ZMod p] (Fin 49 → ZMod p) :=
  LinearMap.pi fun c => ∑ c' : Fin 37, if iotaF c' = c then LinearMap.proj c' else 0

theorem insL_apply (y : Fin 37 → Fp) (c : Fin 49) :
    insL p y c = ∑ c' : Fin 37, if iotaF c' = c then y c' else 0 := by
  simp only [insL, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c' _ => ?_
  split_ifs <;> simp

theorem ins_iota (y : Fin 37 → Fp) (c' : Fin 37) : insL p y (iotaF c') = y c' := by
  rw [insL_apply, Finset.sum_eq_single c']
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (iotaF_inj h)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ins_not (y : Fin 37 → Fp) (c : Fin 49) (h : ∀ c', iotaF c' ≠ c) : insL p y c = 0 := by
  rw [insL_apply]
  exact Finset.sum_eq_zero fun c' _ => by rw [if_neg (h c')]

theorem polx_ins (X : Fin p → Fin 37 → Fp) (c' : Fin 37) :
    polx (fun e => insL p (X e)) (iotaF c') = polx X c' := by
  unfold polx
  exact Finset.sum_congr rfl fun e _ => by simp only [ins_iota]

theorem polx_ins_zero (X : Fin p → Fin 37 → Fp) (c : Fin 49) (h : ∀ c', iotaF c' ≠ c) :
    polx (fun e => insL p (X e)) c = 0 := by
  unfold polx
  exact Finset.sum_eq_zero fun e _ => by simp [ins_not (X e) c h]


/-! ### The jets -/

def jetP (N p : ℕ) [Fact p.Prime] (g k : ℕ) :
    (Fin p → Fin pk.d → ZMod p) →ₗ[ZMod p] (Fin pk.d → ZMod p) :=
  match g with
  | 0 => Charts3.taylorJet (m := p) (d := pk.d) (-1) k
  | 1 => jet0 k
  | 2 => jet0 (wd N p 1 + k)
  | 3 => Charts3.taylorJet (m := p) (d := pk.d) 1 k
  | 4 => Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 3 + k)
  | 5 => Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 3 + wd N p 4 + k)
  | 6 => jetInf k
  | 7 => jetInf (wd N p 6 + k)
  | 8 => jetInf (wd N p 6 + wd N p 7 + k)
  | 9 => jetInf (wd N p 6 + wd N p 7 + wd N p 8 + k)
  | _ => jetInf (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + k)

/-- The jet kernel hypothesis. -/
def JetKer (N p : ℕ) [Fact p.Prime] (x : Fin p → Fin pk.d → ZMod p) : Prop :=
  ∀ g : Fin pk.charts.length, ∀ k : Fin (wNat g N p),
    chartMap pk (pk.chart g) p pk.n (jetP N p g k x) = 0

/-- The atoms as `37`-coordinate vectors. -/
abbrev Xr (x : Fin p → Fin pk.d → ZMod p) : Fin p → Fin 37 → ZMod p :=
  fun e => emb pk p 37 (x e)

theorem vanish_hasRow (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (k : ℕ)
    (hk : k < wd N p g) (r : List ℤ) (hr : hasRow g r = true) :
    ∑ c : Fin 37, ((r.getD c 0 : ℤ) : Fp) * emb pk p 37 (jetP N p g k x) c = 0 := by
  have hg' : g < pk.charts.length := by rw [pk_len]; exact hg
  have h := hker ⟨g, hg'⟩ ⟨k, hk⟩
  have hrows := chart_rows (⟨g, hg'⟩ : Fin pk.charts.length)
  have hmem : r ∈ oRows g := List.contains_iff_mem.mp hr
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < (pk.chart ⟨g, hg'⟩).rows.length := by rw [hrows]; exact hi
  have := CatalanMeasure.GenD.Uniform.W.Charts4.row_of_chart (K := 37) _ h i hi'
  convert this using 2
  rw [Mx, hrows, List.getD_eq_getElem _ _ hi, hir]

theorem sum_unitL (c0 : Fin 37) (f : Fin 37 → Fp) :
    ∑ c : Fin 37, (((unitL c0).getD c 0 : ℤ) : Fp) * f c = f c0 := by
  have : ∀ c : Fin 37, ((unitL c0).getD c 0 : ℤ) = if c = c0 then 1 else 0 := by
    intro c
    unfold unitL
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [Fin.ext_iff, c.isLt]
  simp_rw [this]
  simp

theorem sum_diff2L (a b : Fin 37) (hab : a ≠ b) (f : Fin 37 → Fp) :
    ∑ c : Fin 37, (((diff2L a b).getD c 0 : ℤ) : Fp) * f c = f a - 2 * f b := by
  have : ∀ c : Fin 37, ((diff2L a b).getD c 0 : ℤ) =
      (if c = a then 1 else 0) - (if c = b then 2 else 0) := by
    intro c
    unfold diff2L
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [Fin.ext_iff, c.isLt]
  simp_rw [this]
  push_cast
  simp [sub_mul, Finset.sum_sub_distrib]

theorem sum_neg2L (c0 : Fin 37) (f : Fin 37 → Fp) :
    ∑ c : Fin 37, (((neg2L c0).getD c 0 : ℤ) : Fp) * f c = -2 * f c0 := by
  have : ∀ c : Fin 37, ((neg2L c0).getD c 0 : ℤ) = if c = c0 then -2 else 0 := by
    intro c
    unfold neg2L
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [Fin.ext_iff, c.isLt]
  simp_rw [this]
  simp

theorem sum_unitN (a : ℕ) (ha : a < 37) (f : Fin 37 → Fp) :
    ∑ c : Fin 37, (((unitL a).getD c 0 : ℤ) : Fp) * f c = f ⟨a, ha⟩ := sum_unitL ⟨a, ha⟩ f

theorem getD_map_range (f : ℕ → ℤ) (c : Fin 37) : ((List.range 33).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem sum_virtBL (f : Fin 37 → Fp) :
    ∑ c : Fin 37, ((virtBL.getD c 0 : ℤ) : Fp) * f c = f 0 - f 2 + f 33 := by
  have : ∀ c : Fin 37, (virtBL.getD c 0 : ℤ) =
      (unitL 0).getD c 0 - (unitL 2).getD c 0 + (unitL 33).getD c 0 := by
    intro c
    unfold virtBL unitL
    rw [getD_map_range, getD_map_range, getD_map_range, getD_map_range]
  simp_rw [this]
  push_cast
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_unitN 0 (by norm_num), sum_unitN 2 (by norm_num), sum_unitN 33 (by norm_num)]
  rfl

theorem sum_virtTL (f : Fin 37 → Fp) :
    ∑ c : Fin 37, ((virtTL.getD c 0 : ℤ) : Fp) * f c = f 30 + f 32 := by
  have : ∀ c : Fin 37, (virtTL.getD c 0 : ℤ) = (unitL 30).getD c 0 + (unitL 32).getD c 0 := by
    intro c
    unfold virtTL unitL
    rw [getD_map_range, getD_map_range, getD_map_range]
  simp_rw [this]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, sum_unitN 30 (by norm_num), sum_unitN 32 (by norm_num)]
  rfl

/-! ### Jet extraction -/

theorem vtaylor_unit (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (a : Fp)
    (o : ℕ) (hjet : ∀ k, jetP N p g k = Charts3.taylorJet (m := p) (d := pk.d) a (o + k)) (c : Fin 37)
    (hrow : hasRow g (unitL c) = true) :
    ∀ k < wd N p g, (taylor a (polx (Xr x) c)).coeff (o + k) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (unitL c) hrow
  rw [hjet k, sum_unitL, emb_taylorJet, taylorJet_coord] at this
  exact this

theorem vtaylor_diff (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (a : Fp)
    (o : ℕ) (hjet : ∀ k, jetP N p g k = Charts3.taylorJet (m := p) (d := pk.d) a (o + k)) (c d : Fin 37)
    (hcd : c ≠ d) (hrow : hasRow g (diff2L c d) = true) :
    ∀ k < wd N p g, (taylor a (polx (Xr x) c - 2 * polx (Xr x) d)).coeff (o + k) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (diff2L c d) hrow
  rw [hjet k, sum_diff2L c d hcd, emb_taylorJet, taylorJet_coord, taylorJet_coord] at this
  rw [Pilot146O.taylor_coeff_sub2]; exact this

theorem vtaylor_neg2 (hp2 : p ≠ 2) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11)
    (a : Fp) (o : ℕ) (hjet : ∀ k, jetP N p g k = Charts3.taylorJet (m := p) (d := pk.d) a (o + k))
    (c : Fin 37) (hrow : hasRow g (neg2L c) = true) :
    ∀ k < wd N p g, (taylor a (polx (Xr x) c)).coeff (o + k) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (neg2L c) hrow
  rw [hjet k, sum_neg2L, emb_taylorJet, taylorJet_coord] at this
  have h2 : (-2 : Fp) ≠ 0 := by
    intro h
    have : (2 : Fp) = 0 := by linear_combination -h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast this)
    have hpp := (Fact.out : p.Prime)
    have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this
    exact hp2 this
  exact (mul_eq_zero.mp this).resolve_left h2

theorem vinf_unit (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11)
    (o : ℕ) (hjet : ∀ k, jetP N p g k = jetInf (o + k)) (hb : o + wd N p g ≤ p) (c : Fin 37)
    (hrow : hasRow g (unitL c) = true) :
    ∀ k < wd N p g, (polx (Xr x) c).coeff (p - 1 - (o + k)) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (unitL c) hrow
  rw [hjet k, sum_unitL, emb_jetInf, jetInf_coord, if_pos (by omega)] at this
  exact this

theorem vinf_virtB (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (o : ℕ)
    (hjet : ∀ k, jetP N p g k = jetInf (o + k)) (hb : o + wd N p g ≤ p)
    (hrow : hasRow g virtBL = true) :
    ∀ k < wd N p g, (polx (Xr x) 0 - polx (Xr x) 2 + polx (Xr x) 33).coeff (p - 1 - (o + k)) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk virtBL hrow
  rw [hjet k, sum_virtBL, emb_jetInf, jetInf_coord, jetInf_coord, jetInf_coord, if_pos (by omega),
    if_pos (by omega), if_pos (by omega)] at this
  rw [coeff_add, coeff_sub]; exact this

theorem vinf_virtT (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (o : ℕ)
    (hjet : ∀ k, jetP N p g k = jetInf (o + k)) (hb : o + wd N p g ≤ p)
    (hrow : hasRow g virtTL = true) :
    ∀ k < wd N p g, (polx (Xr x) 30 + polx (Xr x) 32).coeff (p - 1 - (o + k)) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk virtTL hrow
  rw [hjet k, sum_virtTL, emb_jetInf, jetInf_coord, jetInf_coord, if_pos (by omega),
    if_pos (by omega)] at this
  rw [coeff_add]; exact this

end
end Part0

section Part1
section Part0
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-! ### Chains -/

section chains

theorem chainCF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 37)
    (h3 : hasRow 3 (unitL c) = true) (h4 : hasRow 4 (unitL c) = true) (h5 : hasRow 5 (unitL c) = true) :
    ∀ j < 3 * N, (taylor 1 (polx (Xr x) c)).coeff j = 0 := by
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 3 + k) := by
    intro k; simp [jetP]
  have hj5 : ∀ k, jetP N p 5 k =
      Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 3 + wd N p 4 + k) := by
    intro k; simp [jetP]
  have := Pilot146O.chain3 (Q := fun j => (taylor 1 (polx (Xr x) c)).coeff j = 0)
    (a := wd N p 3) (b := wd N p 4) (c := wd N p 5)
    (fun k hk => by simpa using vtaylor_unit x hker 3 (by norm_num) 1 0 hj3 c h3 k hk)
    (vtaylor_unit x hker 4 (by norm_num) 1 (wd N p 3) hj4 c h4)
    (vtaylor_unit x hker 5 (by norm_num) 1 (wd N p 3 + wd N p 4) hj5 c h5)
  intro j hj
  exact this j (by have := wd3 hW; have := wd4 hW; have := wd5 hW; have := hW.2.1; have := hW.2.2.1
                   have := hW.2.2.2; omega)

theorem chainAE1 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 37)
    (h3 : hasRow 3 (unitL c) = true) :
    ∀ j < wd N p 3, (taylor 1 (polx (Xr x) c)).coeff j = 0 := by
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  intro j hj
  simpa using vtaylor_unit x hker 3 (by norm_num) 1 0 hj3 c h3 j hj

theorem chainDiff (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c d : Fin 37)
    (hcd : c ≠ d) (h0 : hasRow 0 (diff2L c d) = true) :
    ∀ j < (p - 1) / 2, (taylor (-1) (polx (Xr x) c - 2 * polx (Xr x) d)).coeff j = 0 := by
  have hj0 : ∀ k, jetP N p 0 k = Charts3.taylorJet (m := p) (d := pk.d) (-1) (0 + k) := by
    intro k; simp [jetP]
  intro j hj
  have := vtaylor_diff x hker 0 (by norm_num) (-1) 0 hj0 c d hcd h0 j (by rw [wd0 hW]; exact hj)
  simpa using this

theorem chainNeg2 (hW : Win N p) (hp2 : p ≠ 2) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 37)
    (h0 : hasRow 0 (neg2L c) = true) :
    ∀ j < (p - 1) / 2, (taylor (-1) (0 - 2 * polx (Xr x) c)).coeff j = 0 := by
  have hj0 : ∀ k, jetP N p 0 k = Charts3.taylorJet (m := p) (d := pk.d) (-1) (0 + k) := by
    intro k; simp [jetP]
  intro j hj
  have := vtaylor_neg2 hp2 x hker 0 (by norm_num) (-1) 0 hj0 c h0 j (by rw [wd0 hW]; exact hj)
  rw [Pilot146O.taylor_coeff_sub2]
  simp only [zero_add] at this
  simp [this]

theorem chainInf1 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 37)
    (h6 : hasRow 6 (unitL c) = true) :
    ∀ j < wd N p 6, (polx (Xr x) c).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have := wd6 hW; have := hW.2.1; have := hW.2.2.1; have := hW.1; have := hW.2.2.2
  intro j hj
  simpa using vinf_unit x hker 6 (by norm_num) 0 hj6 (by omega) c h6 j hj

theorem chainInf2 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 37)
    (h6 : hasRow 6 (unitL c) = true) (h7 : hasRow 7 (unitL c) = true) :
    ∀ j < wd N p 6 + wd N p 7, (polx (Xr x) c).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := hW.2.1; have := hW.2.2.1; have := hW.1; have := hW.2.2.2
  exact Pilot146O.chain2 (Q := fun j => (polx (Xr x) c).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 6 (by norm_num) 0 hj6 (by omega) c h6 k hk)
    (vinf_unit x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) c h7)

theorem chainInf3 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 37)
    (h6 : hasRow 6 (unitL c) = true) (h7 : hasRow 7 (unitL c) = true) (h8 : hasRow 8 (unitL c) = true) :
    ∀ j < wd N p 6 + wd N p 7 + wd N p 8, (polx (Xr x) c).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 6 + wd N p 7 + k) := by intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := wd8 hW; have := hW.2.1; have := hW.2.2.1; have := hW.1; have := hW.2.2.2
  exact Pilot146O.chain3 (Q := fun j => (polx (Xr x) c).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 6 (by norm_num) 0 hj6 (by omega) c h6 k hk)
    (vinf_unit x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) c h7)
    (vinf_unit x hker 8 (by norm_num) (wd N p 6 + wd N p 7) hj8 (by omega) c h8)

theorem chainVB (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10,
      (polx (Xr x) 0 - polx (Xr x) 2 + polx (Xr x) 33).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 6 + wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have hj10 : ∀ k, jetP N p 10 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + k) := by
    intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := wd8 hW; have := wd9 hW; have := wd10 hW
  have := hW.2.1; have := hW.2.2.1; have := hW.1; have := hW.2.2.2
  obtain ⟨r6, r7, r8, r9, r10⟩ := inf_virtB
  exact Pilot146O.chain5 (Q := fun j =>
      (polx (Xr x) 0 - polx (Xr x) 2 + polx (Xr x) 33).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_virtB x hker 6 (by norm_num) 0 hj6 (by omega) r6 k hk)
    (vinf_virtB x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) r7)
    (vinf_virtB x hker 8 (by norm_num) (wd N p 6 + wd N p 7) hj8 (by omega) r8)
    (vinf_virtB x hker 9 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8) hj9 (by omega) r9)
    (vinf_virtB x hker 10 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9) hj10 (by omega) r10)

theorem chainVT (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9,
      (polx (Xr x) 30 + polx (Xr x) 32).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 6 + wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := wd8 hW; have := wd9 hW; have := hW.2.1; have := hW.2.2.1
  have := hW.1
  obtain ⟨r6, r7, r8, r9⟩ := inf_virtT
  exact Pilot146O.chain4 (Q := fun j => (polx (Xr x) 30 + polx (Xr x) 32).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_virtT x hker 6 (by norm_num) 0 hj6 (by omega) r6 k hk)
    (vinf_virtT x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) r7)
    (vinf_virtT x hker 8 (by norm_num) (wd N p 6 + wd N p 7) hj8 (by omega) r8)
    (vinf_virtT x hker 9 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8) hj9 (by omega) r9)

end chains

/-! ### Coordinates of the reduced atoms -/

theorem idx_val {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (k : Fin b) (u : Fin 4) :
    ((ckEquiv hK).symm (Sum.inl (k, u))).val = 4 * k.val + u.val :=
  Pilot146O.ck_inl_val hK k u

theorem iotaF_val (c : Fin 37) : (iotaF c).val = iotaN c.val := rfl

theorem iota_not_AF (k : ℕ) (hk : k < 11) (c' : Fin 37) : (iotaF c').val ≠ 4 * k := by
  rw [iotaF_val]; unfold iotaN; have := c'.isLt; split_ifs <;> omega

theorem iota_not_ZF (c' : Fin 37) : (iotaF c').val ≠ 44 := by
  rw [iotaF_val]; unfold iotaN; have := c'.isLt; split_ifs <;> omega

theorem iota_blk (k : ℕ) (hk : k < 11) (u : ℕ) (hu : u < 3) :
    iotaN (3 * k + u) = 4 * k + 1 + u := by
  unfold iotaN; split_ifs <;> omega

end
end Part0

section Part1
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- The reduced profile-coordinate atoms of the jet kernel. -/
abbrev X' (hW : Win N p) (x : Fin p → Fin pk.d → Fp) : Fin p → Fin 49 → Fp :=
  fun e => projExtras (hKp hW) (insL p (emb pk p 37 (x e)))

theorem poly_AE (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (k : Fin (bN dsg N p)) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inl (k, 1))) = polx (Xr x) ⟨3 * k.val, by
      have := k.isLt; have h10 := geom_bN hW; omega⟩ := by
  have hk : k.val < 11 := by have := k.isLt; have h10 := geom_bN hW; omega
  have e : (ckEquiv (hKp hW)).symm (Sum.inl (k, 1)) = iotaF ⟨3 * k.val, by omega⟩ := by
    apply Fin.ext
    rw [idx_val, iotaF_val]
    show 4 * k.val + _ = iotaN (3 * k.val)
    have := iota_blk k.val hk 0 (by norm_num)
    simp only [add_zero] at this
    rw [this]; first | rfl | omega | simp
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k 1), e]
  exact polx_ins (fun e => emb pk p 37 (x e)) _

theorem poly_CF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (k : Fin (bN dsg N p)) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inl (k, 2))) = polx (Xr x) ⟨3 * k.val + 1, by
      have := k.isLt; have h10 := geom_bN hW; omega⟩ := by
  have hk : k.val < 11 := by have := k.isLt; have h10 := geom_bN hW; omega
  have e : (ckEquiv (hKp hW)).symm (Sum.inl (k, 2)) = iotaF ⟨3 * k.val + 1, by omega⟩ := by
    apply Fin.ext
    rw [idx_val, iotaF_val]
    show 4 * k.val + _ = iotaN (3 * k.val + 1)
    rw [iota_blk k.val hk 1 (by norm_num)]; first | rfl | omega | simp
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k 2), e]
  exact polx_ins (fun e => emb pk p 37 (x e)) _

theorem poly_CE (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (k : Fin (bN dsg N p)) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inl (k, 3))) = polx (Xr x) ⟨3 * k.val + 2, by
      have := k.isLt; have h10 := geom_bN hW; omega⟩ := by
  have hk : k.val < 11 := by have := k.isLt; have h10 := geom_bN hW; omega
  have e : (ckEquiv (hKp hW)).symm (Sum.inl (k, 3)) = iotaF ⟨3 * k.val + 2, by omega⟩ := by
    apply Fin.ext
    rw [idx_val, iotaF_val]
    show 4 * k.val + _ = iotaN (3 * k.val + 2)
    rw [iota_blk k.val hk 2 (by norm_num)]; first | rfl | omega | simp
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k 3), e]
  exact polx_ins (fun e => emb pk p 37 (x e)) _

theorem poly_AF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (k : Fin (bN dsg N p)) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inl (k, 0))) = 0 := by
  have hk : k.val < 11 := by have := k.isLt; have h10 := geom_bN hW; omega
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k 0)]
  apply polx_ins_zero
  intro c' h
  have := iota_not_AF k.val hk c'
  rw [h, idx_val] at this
  simp at this

theorem poly_ZE (hW : Win N p) (x : Fin p → Fin pk.d → Fp) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inr (Sum.inl 1))) = polx (Xr x) 33 := by
  have e : (ckEquiv (hKp hW)).symm (Sum.inr (Sum.inl 1)) = iotaF 33 := by
    apply Fin.ext
    rw [Pilot146O.ck_Z_val, iotaF_val]
    have hb := geom_bN hW
    simp [iotaN, hb]
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_Z _ 1), e]
  exact polx_ins (fun e => emb pk p 37 (x e)) _

theorem poly_ZF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inr (Sum.inl 0))) = 0 := by
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_Z _ 0)]
  apply polx_ins_zero
  intro c' h
  have := iota_not_ZF c'
  rw [h, Pilot146O.ck_Z_val] at this
  have hb := geom_bN hW
  simp [hb] at this

set_option maxHeartbeats 4000000 in
theorem hdom_135 (hW : Win N p) (hp2 : p ≠ 2) (hn : 1 ≤ dsg.n N)
    (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∃ c : Fin (dsg.n N) → Fp, Theta (P := dsg) (N := N) hp2 hn (hKp hW) c = X' hW x := by
  have hb10 : bN dsg N p = 11 := geom_b hW
  have hb : 0 < bN dsg N p := by rw [hb10]; norm_num
  have hrN : dsg.h N % p = 3 * N := geom_hmod hW
  have hN20 : 20 ≤ N := hW.1
  have h69 : 69 * N < 13 * p := hW.2.1
  have h16 : 3 * p ≤ 16 * N := hW.2.2.1
  have hodd : p % 2 = 1 := hW.2.2.2
  have hk10 : ∀ k : Fin (bN dsg N p), k.val < 11 := fun k => by have := k.isLt; omega
  refine exists_rows_of_orders_high hp2 hn (hKp hW) hb (X' hW x) ?hX ?hr0 ?hrh ?hFA ?hFZ
    (8 * N - p) (56 * N - 10 * p - 1) ?hlob ?hlot ?hA ?hC ?hZ ?hVb ?hVt
  case hX =>
    intro e j
    show projExtras _ _ _ = 0
    rw [projExtras_apply, if_pos ⟨j, by simp⟩]
  case hr0 => rw [hrN]; omega
  case hrh => rw [hrN]; omega
  case hFA => exact fun k => poly_AF hW x k
  case hFZ => exact poly_ZF hW x
  case hlob => rw [hrN, geom_ja hW]; omega
  case hlot => rw [hrN, geom_rho hW]; omega
  case hA =>
    intro k
    have hk := hk10 k
    constructor
    · intro j hj
      rw [hrN] at hj
      rw [poly_AE hW x k]
      exact chainAE1 hW x hker _ (by simpa using pt1_AE ⟨k.val, hk⟩) j (by rw [wd3 hW]; omega)
    · intro i hi
      rw [hrN] at hi
      rw [poly_AE hW x k]
      have h6 := wd6 hW; have h7 := wd7 hW
      have := inf_AE ⟨k.val, hk⟩
      exact Pilot146O.coeff_of_inf _ (polx_degree _ _) (wd N p 6 + wd N p 7) (3 * N) (by omega) (by omega)
        (fun j hj => chainInf2 hW x hker _ (by simpa using this.1) (by simpa using this.2) j hj) i hi
  case hC =>
    intro k
    have hk := hk10 k
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hrN] at hj
      rw [poly_CF hW x k]
      have := pt1_CF ⟨k.val, hk⟩
      exact chainCF hW x hker _ (by simpa using this.1) (by simpa using this.2.1) (by simpa using this.2.2) j hj
    · intro j hj
      rw [poly_CF hW x k, poly_CE hW x k]
      exact chainDiff hW x hker _ _ (by intro h; have := congrArg Fin.val h; simp at this)
        (by simpa using ptm1_C ⟨k.val, hk⟩) j hj
    · intro i hi
      rw [hrN] at hi
      rw [poly_CE hW x k]
      have h6 := wd6 hW; have h7 := wd7 hW; have h8 := wd8 hW
      have := inf_CE ⟨k.val, hk⟩
      exact Pilot146O.coeff_of_inf _ (polx_degree _ _) (wd N p 6 + wd N p 7 + wd N p 8) (3 * N - 1) (by omega) (by omega)
        (fun j hj => chainInf3 hW x hker _ (by simpa using this.1) (by simpa using this.2.1)
          (by simpa using this.2.2) j hj) i hi
  case hZ =>
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hrN] at hj
      rw [poly_ZE hW x]
      exact chainAE1 hW x hker _ (by simpa using pt1_ZE) j (by rw [wd3 hW]; omega)
    · intro i hi
      rw [hrN] at hi
      rw [poly_ZE hW x]
      have h6 := wd6 hW; have h7 := wd7 hW
      exact Pilot146O.coeff_of_inf _ (polx_degree _ _) (wd N p 6 + wd N p 7) (3 * N) (by omega) (by omega)
        (fun j hj => chainInf2 hW x hker _ (by simpa using inf_ZE.1) (by simpa using inf_ZE.2) j hj) i hi
    · intro j hj
      rw [poly_ZF hW x, poly_ZE hW x]
      exact chainNeg2 hW hp2 x hker _ (by simpa using ptm1_Z) j hj
  case hVb =>
    intro i hi
    have e0 : ∀ h, (⟨3 * (⟨0, hb⟩ : Fin (bN dsg N p)).val, h⟩ : Fin 37) = 0 := fun h => Fin.ext (by simp)
    have e2 : ∀ h, (⟨3 * (⟨0, hb⟩ : Fin (bN dsg N p)).val + 2, h⟩ : Fin 37) = 2 := fun h => Fin.ext (by simp)
    rw [poly_AE hW x ⟨0, hb⟩, poly_CE hW x ⟨0, hb⟩, poly_ZE hW x]
    simp only [e0, e2]
    have h6 := wd6 hW; have h7 := wd7 hW; have h8 := wd8 hW; have h9 := wd9 hW; have h10 := wd10 hW
    exact Pilot146O.coeff_of_inf _ (lt_of_le_of_lt (degree_add_le _ _) (max_lt
        (lt_of_le_of_lt (degree_sub_le _ _) (max_lt (polx_degree _ _) (polx_degree _ _))) (polx_degree _ _)))
      (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10) (8 * N - p) (by omega) (by omega)
      (fun j hj => chainVB hW x hker j hj) i hi
  case hVt =>
    intro i hi
    rw [poly_AE hW x ⟨bN dsg N p - 1, by omega⟩, poly_CE hW x ⟨bN dsg N p - 1, by omega⟩]
    have h6 := wd6 hW; have h7 := wd7 hW; have h8 := wd8 hW; have h9 := wd9 hW
    have e1 : (⟨3 * (bN dsg N p - 1), by omega⟩ : Fin 37) = 30 := by
      apply Fin.ext; simp only; omega
    have e3 : (⟨3 * (bN dsg N p - 1) + 2, by omega⟩ : Fin 37) = 32 := by
      apply Fin.ext; simp only; omega
    simp only [e1, e3]
    exact Pilot146O.coeff_of_inf _ (lt_of_le_of_lt (degree_add_le _ _) (max_lt (polx_degree _ _) (polx_degree _ _)))
      (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9) (56 * N - 10 * p - 1) (by omega) (by omega)
      (fun j hj => chainVT hW x hker j hj) i hi

end
end Part1

end Part1

section Part2
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx emb_injective not_dvd_delta)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- The graph functional `jet_0` (coordinate 34). -/
def low135 (p : ℕ) [Fact p.Prime] : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj (34 : Fin 37)).comp (emb pk p 37)

theorem low135_apply (y : Fin pk.d → Fp) : low135 p y = emb pk p 37 y 34 := rfl

theorem hG_135 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∃ G : Fp[X], G.degree < ((dsg.q N % p : ℕ) : WithBot ℕ) ∧
      ∀ e : Fin p, G.eval ((((dsg.H N : ℤ) - 1 - e : ℤ)) : Fp) = low135 p (x e) := by
  have hq := geom_qmod hW
  have h3 := wd3 hW; have h4 := wd4 hW
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 3 + k) := by
    intro k; simp [jetP]
  have hv : ∀ g, g < 11 → (hasRow g (unitL 34) = true) → ∀ k, k < wd N p g →
      low135 p (jetP N p g k x) = 0 := by
    intro g hg hr k hk
    have := vanish_hasRow x hker g hg k hk (unitL 34) hr
    have e := sum_unitL (34 : Fin 37) (emb pk p 37 (jetP N p g k x))
    exact e.symm.trans this
  have hchain := Pilot146O.chain2 (Q := fun j => low135 p (Charts3.taylorJet (m := p) (d := pk.d) 1 j x) = 0)
    (a := wd N p 3) (b := wd N p 4)
    (fun k hk => by have := hv 3 (by norm_num) pt1_jet0.1 k hk; rw [hj3 k] at this; simpa using this)
    (fun k hk => by have := hv 4 (by norm_num) pt1_jet0.2 k hk; rw [hj4 k] at this; exact this)
  have := hG_of_taylor (low135 p) (((dsg.H N : ℤ) - 1 : ℤ) : Fp) (dsg.q N % p)
    (by have := hW.2.1; have := hW.1; omega) x (fun k hk => hchain k (by have := hW.2.2.2; omega))
  obtain ⟨G, hGd, hGe⟩ := this
  refine ⟨G, hGd, fun e => ?_⟩
  rw [← hGe e]
  congr 1
  push_cast
  ring

/-! ### Unique graph -/

theorem jet0_emb (x : Fin p → Fin pk.d → Fp) (k : ℕ) (hk : k < p) (c : Fin 37) :
    emb pk p 37 (jet0 k x) c = emb pk p 37 (x ⟨k, hk⟩) c := by
  rw [emb_jet0, jet0_coord]
  exact polx_coeff (Xr x) c ⟨k, hk⟩

theorem rowsum_aux (r : List ℤ) (y : Fin 37 → Fp) (hy : ∀ c : Fin 37, c.val < 34 → y c = 0) :
    ∑ c : Fin 37, ((r.getD c 0 : ℤ) : Fp) * y c =
      ((r.getD 34 0 : ℤ) : Fp) * y 34 + ((r.getD 35 0 : ℤ) : Fp) * y 35 + ((r.getD 36 0 : ℤ) : Fp) * y 36 := by
  have h : ∀ c : Fin 37, ((r.getD c 0 : ℤ) : Fp) * y c =
      (if c = 34 then ((r.getD 34 0 : ℤ) : Fp) * y 34 else 0) +
      (if c = 35 then ((r.getD 35 0 : ℤ) : Fp) * y 35 else 0) +
      (if c = 36 then ((r.getD 36 0 : ℤ) : Fp) * y 36 else 0) := by
    intro c
    by_cases hc : c.val < 34
    · have h1 : c ≠ 34 := fun h => by rw [h] at hc; simp at hc
      have h2 : c ≠ 35 := fun h => by rw [h] at hc; simp at hc
      have h3 : c ≠ 36 := fun h => by rw [h] at hc; simp at hc
      rw [if_neg h1, if_neg h2, if_neg h3, hy c hc]; simp
    · have : c = 34 ∨ c = 35 ∨ c = 36 := by
        rcases (by have := c.isLt; omega : c.val = 34 ∨ c.val = 35 ∨ c.val = 36) with h | h | h
        · left; exact Fin.ext h
        · right; left; exact Fin.ext h
        · right; right; exact Fin.ext h
      rcases this with rfl | rfl | rfl <;> simp
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

theorem raw_vanish (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (r : List ℤ)
    (hr : hasRow g r = true) (jt k : ℕ) (hk : k < wd N p g) (hjet : jetP N p g k = jet0 jt) (hj : jt < p)
    (hs : ∀ c : Fin 37, c.val < 34 → emb pk p 37 (x ⟨jt, hj⟩) c = 0) :
    ((r.getD 34 0 : ℤ) : Fp) * emb pk p 37 (x ⟨jt, hj⟩) 34 +
      ((r.getD 35 0 : ℤ) : Fp) * emb pk p 37 (x ⟨jt, hj⟩) 35 +
      ((r.getD 36 0 : ℤ) : Fp) * emb pk p 37 (x ⟨jt, hj⟩) 36 = 0 := by
  have v := vanish_hasRow x hker g hg k hk r hr
  rw [hjet] at v
  rw [← rowsum_aux r _ hs, ← v]
  exact (Finset.sum_congr rfl fun c _ => by rw [jet0_emb x jt hj c]).symm

/-- A raw row: contains its row, `ρ_34 | 2310^40`, `ρ_34 ≠ 0`, `ρ_35 = c13 * ρ_34`, `ρ_36 = c1 * ρ_34`. -/
def rawRowOK (g i : ℕ) (c13 c1 : ℤ) : Bool :=
  hasRow g ((oRows g).getD i []) && decide (((oRows g).getD i []).getD 34 0 ∣ 30030 ^ 40) &&
    decide (((oRows g).getD i []).getD 34 0 ≠ 0) &&
    decide (((oRows g).getD i []).getD 35 0 = c13 * ((oRows g).getD i []).getD 34 0) &&
    decide (((oRows g).getD i []).getD 36 0 = c1 * ((oRows g).getD i []).getD 34 0)

set_option maxRecDepth 100000 in
theorem raw_ok : rawRowOK 1 0 0 0 = true ∧ rawRowOK 1 11 1 0 = true ∧ rawRowOK 1 12 0 1 = true ∧
    rawRowOK 2 0 0 1 = true := by decide +kernel

theorem chainJet0 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 3 + wd N p 4, (taylor 1 (polx (Xr x) 34)).coeff j = 0 := by
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 3 + k) := by
    intro k; simp [jetP]
  exact Pilot146O.chain2 (Q := fun j => (taylor 1 (polx (Xr x) 34)).coeff j = 0)
    (fun k hk => by simpa using vtaylor_unit x hker 3 (by norm_num) 1 0 hj3 34 pt1_jet0.1 k hk)
    (vtaylor_unit x hker 4 (by norm_num) 1 (wd N p 3) hj4 34 pt1_jet0.2)

theorem chainLow13 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10,
      (polx (Xr x) 35).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 6 + wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have hj10 : ∀ k, jetP N p 10 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + k) := by
    intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := wd8 hW; have := wd9 hW; have := wd10 hW
  have := hW.2.1; have := hW.2.2.1; have := hW.1; have := hW.2.2.2
  obtain ⟨r6, r7, r8, r9, r10⟩ := inf_low13
  exact Pilot146O.chain5 (Q := fun j => (polx (Xr x) 35).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 6 (by norm_num) 0 hj6 (by omega) 35 r6 k hk)
    (vinf_unit x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) 35 r7)
    (vinf_unit x hker 8 (by norm_num) (wd N p 6 + wd N p 7) hj8 (by omega) 35 r8)
    (vinf_unit x hker 9 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8) hj9 (by omega) 35 r9)
    (vinf_unit x hker 10 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9) hj10 (by omega) 35 r10)

theorem chainLow1 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 6, (polx (Xr x) 36).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have := wd6 hW; have := hW.2.1; have := hW.2.2.1; have := hW.1
  intro j hj
  simpa using vinf_unit x hker 6 (by norm_num) 0 hj6 (by omega) 36 inf_low1 j hj

theorem slot_zero (hW : Win N p) (x : Fin p → Fin pk.d → Fp)
    (hproj : ∀ e, projExtras (hKp hW) (insL p (emb pk p 37 (x e))) = 0) (e : Fin p) (c : Fin 37)
    (hc : c.val < 34) : emb pk p 37 (x e) c = 0 := by
  have h0 := congrFun (hproj e) (iotaF c)
  rw [projExtras_apply] at h0
  have hne : ¬ isExtra (hKp hW) (iotaF c) := by
    rintro ⟨j, hj⟩
    have h := Pilot146O.ck_X_val (hKp hW) j
    have hc' : iotaF c = (ckEquiv (hKp hW)).symm (Sum.inr (Sum.inr j)) := by rw [← hj]; simp
    have hb : bN dsg N p = 11 := geom_b hW
    have hv : (iotaF c).val = bN dsg N p * 4 + 2 + j.val := by rw [hc']; exact h
    rw [iotaF_val] at hv
    unfold iotaN at hv
    have := j.isLt
    split_ifs at hv <;> omega
  rw [if_neg hne, ins_iota] at h0
  exact h0

set_option maxHeartbeats 4000000 in
theorem hinj_135 (hW : Win N p) (hpD : ¬ (p : ℤ) ∣ pk.D) (x : Fin p → Fin pk.d → Fp)
    (hker : JetKer N p x)
    (hproj : ∀ e, projExtras (hKp hW) (insL p (emb pk p 37 (x e))) = 0) : x = 0 := by
  have h11 : 13 < p := by have := hW.2.1; have := hW.1; omega
  have hslot := slot_zero hW x hproj
  have w1 := wd1 hW; have w2 := wd2 hW; have w3 := wd3 hW; have w4 := wd4 hW
  have w6 := wd6 hW; have w7 := wd7 hW; have w8 := wd8 hW; have w9 := wd9 hW; have w10 := wd10 hW
  have hp6 := hW.2.1; have hp6' := hW.2.2.1; have hN := hW.1; have hodd := hW.2.2.2
  obtain ⟨r1a, r1g13, r1g1, r2g⟩ := raw_ok
  simp only [rawRowOK, Bool.and_eq_true, decide_eq_true_eq] at r1a r1g13 r1g1 r2g
  obtain ⟨⟨⟨⟨hr1a, d1a⟩, n1a⟩, e13a⟩, e1a⟩ := r1a
  obtain ⟨⟨⟨⟨hr1g13, d1g13⟩, n1g13⟩, e13g13⟩, e1g13⟩ := r1g13
  obtain ⟨⟨⟨⟨hr1g1, d1g1⟩, n1g1⟩, e13g1⟩, e1g1⟩ := r1g1
  obtain ⟨⟨⟨⟨hr2g, d2g⟩, n2g⟩, e13g2⟩, e1g2⟩ := r2g
  -- low1 (36) vanishes on e ≥ w1, low13 (35) on e ≥ 8N - p
  have h36 : ∀ e : Fin p, wd N p 1 ≤ e.val → emb pk p 37 (x e) 36 = 0 := by
    intro e he
    have := Pilot146O.coeff_of_inf (polx (Xr x) 36) (polx_degree _ _) (wd N p 6) (wd N p 1)
      (by omega) (by omega) (fun j hj => chainLow1 hW x hker j hj) e.val he
    have h2 := polx_coeff (Xr x) 36 e
    rw [this] at h2
    exact h2.symm
  have h35 : ∀ e : Fin p, 8 * N - p ≤ e.val → emb pk p 37 (x e) 35 = 0 := by
    intro e he
    have := Pilot146O.coeff_of_inf (polx (Xr x) 35) (polx_degree _ _)
      (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10) (8 * N - p) (by omega) (by omega)
      (fun j hj => chainLow13 hW x hker j hj) e.val he
    have h2 := polx_coeff (Xr x) 35 e
    rw [this] at h2
    exact h2.symm
  -- jet_0 vanishes for e < w1 + w2
  have h34 : ∀ e : Fin p, e.val < wd N p 1 + wd N p 2 → emb pk p 37 (x e) 34 = 0 := by
    intro e he
    by_cases h1 : e.val < wd N p 1
    · have v := raw_vanish x hker 1 (by norm_num) _ hr1a e.val e.val h1 (by simp [jetP]) e.isLt
        (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e13a, e1a] at v; simp only [zero_mul, Int.cast_zero, add_zero] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ d1a h11
      exact (mul_eq_zero.mp v).resolve_left hu
    · have v := raw_vanish x hker 2 (by norm_num) _ hr2g (e.val) (e.val - wd N p 1) (by omega)
        (by simp [jetP]; congr 1; omega) e.isLt (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e13g2, e1g2, h36 e (by omega)] at v
      simp only [mul_zero, add_zero, zero_mul, Int.cast_zero, zero_add] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ d2g h11
      exact (mul_eq_zero.mp v).resolve_left hu
  have hf34 : polx (Xr x) 34 = 0 := by
    refine Pilot146O.poly_zero_of_orders _ (p - 3 * N) (3 * N) (wd N p 1 + wd N p 2) (polx_degree _ _)
      (by omega) (by omega) ?_ ?_
    · have h1 : (X - 1 : Fp[X]) = X - C 1 := by simp
      rw [h1, pow_dvd_iff_taylor]
      intro k hk
      exact chainJet0 hW x hker k (by omega)
    · intro e he
      have hep : e < p := by omega
      have := polx_coeff (Xr x) 34 ⟨e, hep⟩
      simp only at this
      rw [this]
      exact h34 ⟨e, hep⟩ he
  have h34' : ∀ e : Fin p, emb pk p 37 (x e) 34 = 0 := by
    intro e
    have := polx_coeff (Xr x) 34 e
    rw [hf34] at this
    simpa using this.symm
  have h35' : ∀ e : Fin p, emb pk p 37 (x e) 35 = 0 := by
    intro e
    by_cases he : wd N p 1 ≤ e.val
    · exact h35 e (by omega)
    · have h1 : e.val < wd N p 1 := by omega
      have v := raw_vanish x hker 1 (by norm_num) _ hr1g13 e.val e.val h1 (by simp [jetP]) e.isLt
        (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e13g13, e1g13, h34' e] at v
      simp only [mul_zero, zero_add, Int.cast_mul, Int.cast_one, one_mul, Int.cast_zero, zero_mul, add_zero] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ d1g13 h11
      have hu' : (((((oRows 1).getD 11 []).getD 35 0 : ℤ)) : Fp) ≠ 0 := by
        rw [e13g13]; simpa using hu
      exact (mul_eq_zero.mp v).resolve_left hu'
  have h36' : ∀ e : Fin p, emb pk p 37 (x e) 36 = 0 := by
    intro e
    by_cases he : wd N p 1 ≤ e.val
    · exact h36 e he
    · have h1 : e.val < wd N p 1 := by omega
      have v := raw_vanish x hker 1 (by norm_num) _ hr1g1 e.val e.val h1 (by simp [jetP]) e.isLt
        (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e13g1, e1g1, h34' e] at v
      simp only [mul_zero, zero_add, Int.cast_mul, Int.cast_one, one_mul, Int.cast_zero, zero_mul, add_zero] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ d1g1 h11
      have hu' : (((((oRows 1).getD 12 []).getD 36 0 : ℤ)) : Fp) ≠ 0 := by
        rw [e1g1]; simpa using hu
      exact (mul_eq_zero.mp v).resolve_left hu'
  have hinjE : Function.Injective (emb pk p 37) :=
    emb_injective CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.pk_sound rfl (not_dvd_delta hpD)
  funext e
  apply hinjE
  funext c
  simp only [Pi.zero_apply, map_zero]
  show emb pk p 37 (x e) c = 0
  have hc := c.isLt
  by_cases h1 : c.val < 34
  · exact hslot e c h1
  · have : c = 34 ∨ c = 35 ∨ c = 36 := by
      rcases (by omega : c.val = 34 ∨ c.val = 35 ∨ c.val = 36) with h | h | h
      · left; exact Fin.ext h
      · right; left; exact Fin.ext h
      · right; right; exact Fin.ext h
    rcases this with rfl | rfl | rfl
    · exact h34' e
    · exact h35' e
    · exact h36' e

end
end Part2

end CatalanMeasure.GenD.Uniform.W.Charts6.L0135
