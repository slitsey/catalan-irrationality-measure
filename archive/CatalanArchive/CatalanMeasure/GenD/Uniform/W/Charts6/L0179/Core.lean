module
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0179.Base
public import CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Unique146
public import CatalanMeasure.GenD.Uniform.W.Charts6.DomVLow
public import CatalanMeasure.GenD.Uniform.W.Charts3.GraphJets
public import CatalanMeasure.GenD.Uniform.W.Charts6.Unit13
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Uniform.W.Charts6.L0179
section Part0
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- The packet coordinates are the profile coordinates (`K = 28`): the insertion is the identity. -/
def insL (p : ℕ) [Fact p.Prime] : (Fin 28 → ZMod p) →ₗ[ZMod p] (Fin 28 → ZMod p) := LinearMap.id

theorem insL_apply (y : Fin 28 → Fp) : insL p y = y := rfl

def jetP (N p : ℕ) [Fact p.Prime] (g k : ℕ) :
    (Fin p → Fin pk.d → ZMod p) →ₗ[ZMod p] (Fin pk.d → ZMod p) :=
  match g with
  | 0 => Charts3.taylorJet (m := p) (d := pk.d) (-1) k
  | 1 => jet0 k
  | 2 => jet0 (wd N p 1 + k)
  | 3 => jet0 (wd N p 1 + wd N p 2 + k)
  | 4 => Charts3.taylorJet (m := p) (d := pk.d) 1 k
  | 5 => Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 4 + k)
  | 6 => Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 4 + wd N p 5 + k)
  | 7 => jetInf k
  | 8 => jetInf (wd N p 7 + k)
  | 9 => jetInf (wd N p 7 + wd N p 8 + k)
  | 10 => jetInf (wd N p 7 + wd N p 8 + wd N p 9 + k)
  | _ => jetInf (wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10 + k)

/-- The jet kernel hypothesis. -/
def JetKer (N p : ℕ) [Fact p.Prime] (x : Fin p → Fin pk.d → ZMod p) : Prop :=
  ∀ g : Fin pk.charts.length, ∀ k : Fin (wNat g N p),
    chartMap pk (pk.chart g) p pk.n (jetP N p g k x) = 0

/-- The atoms as `28`-coordinate vectors. -/
abbrev Xr (x : Fin p → Fin pk.d → ZMod p) : Fin p → Fin 28 → ZMod p :=
  fun e => emb pk p 28 (x e)

theorem vanish_hasRow (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 12) (k : ℕ)
    (hk : k < wd N p g) (r : List ℤ) (hr : hasRow g r = true) :
    ∑ c : Fin 28, ((r.getD c 0 : ℤ) : Fp) * emb pk p 28 (jetP N p g k x) c = 0 := by
  have hg' : g < pk.charts.length := by rw [pk_len]; exact hg
  have h := hker ⟨g, hg'⟩ ⟨k, hk⟩
  have hrows := chart_rows (⟨g, hg'⟩ : Fin pk.charts.length)
  have hmem : r ∈ oRows g := List.contains_iff_mem.mp hr
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < (pk.chart ⟨g, hg'⟩).rows.length := by rw [hrows]; exact hi
  have := CatalanMeasure.GenD.Uniform.W.Charts4.row_of_chart (K := 28) _ h i hi'
  convert this using 2
  rw [Mx, hrows, List.getD_eq_getElem _ _ hi, hir]

theorem getD_map_range (f : ℕ → ℤ) (c : Fin 28) : ((List.range 28).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem sum_unitL (c0 : Fin 28) (f : Fin 28 → Fp) :
    ∑ c : Fin 28, (((unitL c0).getD c 0 : ℤ) : Fp) * f c = f c0 := by
  have : ∀ c : Fin 28, ((unitL c0).getD c 0 : ℤ) = if c = c0 then 1 else 0 := by
    intro c
    unfold unitL
    rw [getD_map_range]
    simp [Fin.ext_iff]
  simp_rw [this]
  simp

theorem sum_unitN (a : ℕ) (ha : a < 28) (f : Fin 28 → Fp) :
    ∑ c : Fin 28, (((unitL a).getD c 0 : ℤ) : Fp) * f c = f ⟨a, ha⟩ := sum_unitL ⟨a, ha⟩ f

theorem sum_diff2L (a b : Fin 28) (hab : a ≠ b) (f : Fin 28 → Fp) :
    ∑ c : Fin 28, (((diff2L a b).getD c 0 : ℤ) : Fp) * f c = f a - 2 * f b := by
  have : ∀ c : Fin 28, ((diff2L a b).getD c 0 : ℤ) =
      (if c = a then 1 else 0) - (if c = b then 2 else 0) := by
    intro c
    unfold diff2L
    rw [getD_map_range]
    simp [Fin.ext_iff]
  simp_rw [this]
  push_cast
  simp [sub_mul, Finset.sum_sub_distrib]

theorem sum_virtEL (f : Fin 28 → Fp) :
    ∑ c : Fin 28, ((virtEL.getD c 0 : ℤ) : Fp) * f c = f 1 - f 3 + f 25 := by
  have : ∀ c : Fin 28, (virtEL.getD c 0 : ℤ) =
      (unitL 1).getD c 0 - (unitL 3).getD c 0 + (unitL 25).getD c 0 := by
    intro c
    unfold virtEL unitL
    rw [getD_map_range, getD_map_range, getD_map_range, getD_map_range]
  simp_rw [this]
  push_cast
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_unitN 1 (by norm_num), sum_unitN 3 (by norm_num), sum_unitN 25 (by norm_num)]
  rfl

theorem sum_virtFL (f : Fin 28 → Fp) :
    ∑ c : Fin 28, ((virtFL.getD c 0 : ℤ) : Fp) * f c = f 0 - f 2 + f 24 := by
  have : ∀ c : Fin 28, (virtFL.getD c 0 : ℤ) =
      (unitL 0).getD c 0 - (unitL 2).getD c 0 + (unitL 24).getD c 0 := by
    intro c
    unfold virtFL unitL
    rw [getD_map_range, getD_map_range, getD_map_range, getD_map_range]
  simp_rw [this]
  push_cast
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_unitN 0 (by norm_num), sum_unitN 2 (by norm_num), sum_unitN 24 (by norm_num)]
  rfl

theorem sum_virtTL (f : Fin 28 → Fp) :
    ∑ c : Fin 28, ((virtTL.getD c 0 : ℤ) : Fp) * f c = f 21 + f 23 := by
  have : ∀ c : Fin 28, (virtTL.getD c 0 : ℤ) = (unitL 21).getD c 0 + (unitL 23).getD c 0 := by
    intro c
    unfold virtTL unitL
    rw [getD_map_range, getD_map_range, getD_map_range]
  simp_rw [this]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, sum_unitN 21 (by norm_num), sum_unitN 23 (by norm_num)]
  rfl

/-! ### Jet extraction -/

theorem vtaylor_unit (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 12) (a : Fp)
    (o : ℕ) (hjet : ∀ k, jetP N p g k = Charts3.taylorJet (m := p) (d := pk.d) a (o + k)) (c : Fin 28)
    (hrow : hasRow g (unitL c) = true) :
    ∀ k < wd N p g, (taylor a (polx (Xr x) c)).coeff (o + k) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (unitL c) hrow
  rw [hjet k, sum_unitL, emb_taylorJet, taylorJet_coord] at this
  exact this

theorem vtaylor_diff (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 12) (a : Fp)
    (o : ℕ) (hjet : ∀ k, jetP N p g k = Charts3.taylorJet (m := p) (d := pk.d) a (o + k)) (c d : Fin 28)
    (hcd : c ≠ d) (hrow : hasRow g (diff2L c d) = true) :
    ∀ k < wd N p g, (taylor a (polx (Xr x) c - 2 * polx (Xr x) d)).coeff (o + k) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (diff2L c d) hrow
  rw [hjet k, sum_diff2L c d hcd, emb_taylorJet, taylorJet_coord, taylorJet_coord] at this
  rw [Pilot146O.taylor_coeff_sub2]; exact this

theorem vinf_unit (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 12)
    (o : ℕ) (hjet : ∀ k, jetP N p g k = jetInf (o + k)) (hb : o + wd N p g ≤ p) (c : Fin 28)
    (hrow : hasRow g (unitL c) = true) :
    ∀ k < wd N p g, (polx (Xr x) c).coeff (p - 1 - (o + k)) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (unitL c) hrow
  rw [hjet k, sum_unitL, emb_jetInf, jetInf_coord, if_pos (by omega)] at this
  exact this

theorem vinf_virtF (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 12) (o : ℕ)
    (hjet : ∀ k, jetP N p g k = jetInf (o + k)) (hb : o + wd N p g ≤ p)
    (hrow : hasRow g virtFL = true) :
    ∀ k < wd N p g, (polx (Xr x) 0 - polx (Xr x) 2 + polx (Xr x) 24).coeff (p - 1 - (o + k)) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk virtFL hrow
  rw [hjet k, sum_virtFL, emb_jetInf, jetInf_coord, jetInf_coord, jetInf_coord, if_pos (by omega),
    if_pos (by omega), if_pos (by omega)] at this
  rw [coeff_add, coeff_sub]; exact this

theorem vinf_virtT (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 12) (o : ℕ)
    (hjet : ∀ k, jetP N p g k = jetInf (o + k)) (hb : o + wd N p g ≤ p)
    (hrow : hasRow g virtTL = true) :
    ∀ k < wd N p g, (polx (Xr x) 21 + polx (Xr x) 23).coeff (p - 1 - (o + k)) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk virtTL hrow
  rw [hjet k, sum_virtTL, emb_jetInf, jetInf_coord, jetInf_coord, if_pos (by omega),
    if_pos (by omega)] at this
  rw [coeff_add]; exact this

/-- The `E_zero` row at the point `0`: coefficient `o + k` of the combination vanishes. -/
theorem v0_virtE (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 12) (o : ℕ)
    (hjet : ∀ k, jetP N p g k = jet0 (o + k)) (hb : o + wd N p g ≤ p)
    (hrow : hasRow g virtEL = true) :
    ∀ k < wd N p g, (polx (Xr x) 1 - polx (Xr x) 3 + polx (Xr x) 25).coeff (o + k) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk virtEL hrow
  rw [hjet k, sum_virtEL, emb_jet0, jet0_coord, jet0_coord, jet0_coord] at this
  rw [coeff_add, coeff_sub]; exact this

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

section chains

theorem chainAF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 28)
    (h4 : hasRow 4 (unitL c) = true) (h5 : hasRow 5 (unitL c) = true) (h6 : hasRow 6 (unitL c) = true) :
    ∀ j < 3 * N + (p - 1) / 2, (taylor 1 (polx (Xr x) c)).coeff j = 0 := by
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj5 : ∀ k, jetP N p 5 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 4 + k) := by
    intro k; simp [jetP]
  have hj6 : ∀ k, jetP N p 6 k =
      Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 4 + wd N p 5 + k) := by
    intro k; simp [jetP]
  have := Pilot146O.chain3 (Q := fun j => (taylor 1 (polx (Xr x) c)).coeff j = 0)
    (a := wd N p 4) (b := wd N p 5) (c := wd N p 6)
    (fun k hk => by simpa using vtaylor_unit x hker 4 (by norm_num) 1 0 hj4 c h4 k hk)
    (vtaylor_unit x hker 5 (by norm_num) 1 (wd N p 4) hj5 c h5)
    (vtaylor_unit x hker 6 (by norm_num) 1 (wd N p 4 + wd N p 5) hj6 c h6)
  intro j hj
  exact this j (by have := wd4 hW; have := wd5 hW; have := wd6 hW; have := hW.2.1; have := hW.2.2.1
                   have := hW.2.2.2; omega)

theorem chainCF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 28)
    (h4 : hasRow 4 (unitL c) = true) :
    ∀ j < 3 * N, (taylor 1 (polx (Xr x) c)).coeff j = 0 := by
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  intro j hj
  simpa using vtaylor_unit x hker 4 (by norm_num) 1 0 hj4 c h4 j (by rw [wd4 hW]; exact hj)

theorem chainDiff (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c d : Fin 28)
    (hcd : c ≠ d) (h0 : hasRow 0 (diff2L c d) = true) :
    ∀ j < (p - 1) / 2, (taylor (-1) (polx (Xr x) c - 2 * polx (Xr x) d)).coeff j = 0 := by
  have hj0 : ∀ k, jetP N p 0 k = Charts3.taylorJet (m := p) (d := pk.d) (-1) (0 + k) := by
    intro k; simp [jetP]
  intro j hj
  have := vtaylor_diff x hker 0 (by norm_num) (-1) 0 hj0 c d hcd h0 j (by rw [wd0 hW]; exact hj)
  simpa using this

theorem chainInf2 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 28)
    (h7 : hasRow 7 (unitL c) = true) (h8 : hasRow 8 (unitL c) = true) :
    ∀ j < wd N p 7 + wd N p 8, (polx (Xr x) c).coeff (p - 1 - j) = 0 := by
  have hj7 : ∀ k, jetP N p 7 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 7 + k) := by intro k; simp [jetP]
  have := wd7 hW; have := wd8 hW; have := hW.2.1; have := hW.2.2.1; have := hW.1; have := hW.2.2.2
  exact Pilot146O.chain2 (Q := fun j => (polx (Xr x) c).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 7 (by norm_num) 0 hj7 (by omega) c h7 k hk)
    (vinf_unit x hker 8 (by norm_num) (wd N p 7) hj8 (by omega) c h8)

theorem chainInf3 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (c : Fin 28)
    (h7 : hasRow 7 (unitL c) = true) (h8 : hasRow 8 (unitL c) = true) (h9 : hasRow 9 (unitL c) = true) :
    ∀ j < wd N p 7 + wd N p 8 + wd N p 9, (polx (Xr x) c).coeff (p - 1 - j) = 0 := by
  have hj7 : ∀ k, jetP N p 7 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have := wd7 hW; have := wd8 hW; have := wd9 hW; have := hW.2.1; have := hW.2.2.1; have := hW.1
  have := hW.2.2.2
  exact Pilot146O.chain3 (Q := fun j => (polx (Xr x) c).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 7 (by norm_num) 0 hj7 (by omega) c h7 k hk)
    (vinf_unit x hker 8 (by norm_num) (wd N p 7) hj8 (by omega) c h8)
    (vinf_unit x hker 9 (by norm_num) (wd N p 7 + wd N p 8) hj9 (by omega) c h9)

/-- `E_zero`: the combination vanishes at the point `0` to order `p` (groups 1, 2, 3). -/
theorem chainVE (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < p, (polx (Xr x) 1 - polx (Xr x) 3 + polx (Xr x) 25).coeff j = 0 := by
  have hj1 : ∀ k, jetP N p 1 k = jet0 (0 + k) := by intro k; simp [jetP]
  have hj2 : ∀ k, jetP N p 2 k = jet0 (wd N p 1 + k) := by intro k; simp [jetP]
  have hj3 : ∀ k, jetP N p 3 k = jet0 (wd N p 1 + wd N p 2 + k) := by intro k; simp [jetP]
  have := wd1 hW; have := wd2 hW; have := wd3 hW; have := hW.2.1; have := hW.2.2.1; have := hW.1
  have := hW.2.2.2
  obtain ⟨r1, r2, r3⟩ := pt0_vE
  have key := Pilot146O.chain3 (Q := fun j => (polx (Xr x) 1 - polx (Xr x) 3 + polx (Xr x) 25).coeff j = 0)
    (fun k hk => by simpa using v0_virtE x hker 1 (by norm_num) 0 hj1 (by omega) r1 k hk)
    (v0_virtE x hker 2 (by norm_num) (wd N p 1) hj2 (by omega) r2)
    (v0_virtE x hker 3 (by norm_num) (wd N p 1 + wd N p 2) hj3 (by omega) r3)
  intro j hj
  exact key j (by omega)

theorem chainVF (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 7, (polx (Xr x) 0 - polx (Xr x) 2 + polx (Xr x) 24).coeff (p - 1 - j) = 0 := by
  have hj7 : ∀ k, jetP N p 7 k = jetInf (0 + k) := by intro k; simp [jetP]
  have := wd7 hW; have := hW.2.1; have := hW.2.2.1; have := hW.1
  intro j hj
  simpa using vinf_virtF x hker 7 (by norm_num) 0 hj7 (by omega) inf_virtF j hj

theorem chainVT (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10,
      (polx (Xr x) 21 + polx (Xr x) 23).coeff (p - 1 - j) = 0 := by
  have hj7 : ∀ k, jetP N p 7 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have hj10 : ∀ k, jetP N p 10 k = jetInf (wd N p 7 + wd N p 8 + wd N p 9 + k) := by intro k; simp [jetP]
  have := wd7 hW; have := wd8 hW; have := wd9 hW; have := wd10 hW; have := hW.2.1; have := hW.2.2.1
  have := hW.1; have := hW.2.2.2
  obtain ⟨r7, r8, r9, r10⟩ := inf_virtT
  exact Pilot146O.chain4 (Q := fun j => (polx (Xr x) 21 + polx (Xr x) 23).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_virtT x hker 7 (by norm_num) 0 hj7 (by omega) r7 k hk)
    (vinf_virtT x hker 8 (by norm_num) (wd N p 7) hj8 (by omega) r8)
    (vinf_virtT x hker 9 (by norm_num) (wd N p 7 + wd N p 8) hj9 (by omega) r9)
    (vinf_virtT x hker 10 (by norm_num) (wd N p 7 + wd N p 8 + wd N p 9) hj10 (by omega) r10)

end chains

end
end Part0

section Part1
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- The atoms of the jet kernel with the graph coordinates forgotten. -/
abbrev X' (hW : Win N p) (x : Fin p → Fin pk.d → Fp) : Fin p → Fin 28 → Fp :=
  fun e => projExtras (hKp hW) (emb pk p 28 (x e))

theorem poly_blk (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (k : Fin (bN dsg N p)) (u : Fin 4) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inl (k, u))) = polx (Xr x) ⟨4 * k.val + u.val, by
      have h1 := k.isLt; have h2 := u.isLt; have h6 := geom_bN hW; omega⟩ := by
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k u)]
  congr 1
  exact Fin.ext (Pilot146O.ck_inl_val _ k u)

theorem poly_Z (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (z : Fin 2) :
    polx (X' hW x) ((ckEquiv (hKp hW)).symm (Sum.inr (Sum.inl z))) = polx (Xr x) ⟨24 + z.val, by
      have := z.isLt; omega⟩ := by
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_Z _ z)]
  congr 1
  apply Fin.ext
  rw [Pilot146O.ck_Z_val]
  have hb := geom_bN hW
  simp [hb]

set_option maxHeartbeats 4000000 in
theorem hdom_179 (hW : Win N p) (hp2 : p ≠ 2) (hn : 1 ≤ dsg.n N)
    (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∃ c : Fin (dsg.n N) → Fp, Theta (P := dsg) (N := N) hp2 hn (hKp hW) c = X' hW x := by
  have hb6 : bN dsg N p = 6 := geom_bN hW
  have hb : 0 < bN dsg N p := by rw [hb6]; norm_num
  have hrN : dsg.h N % p = 3 * N := geom_hmod hW
  have hN20 : 20 ≤ N := hW.1
  have h11 : 11 * N < 1 * p := hW.2.1
  have h78 : 7 * p ≤ 78 * N := hW.2.2.1
  have hodd : p % 2 = 1 := hW.2.2.2
  have hk6 : ∀ k : Fin (bN dsg N p), k.val < 6 := fun k => by have := k.isLt; omega
  have hdeg3 : ∀ (A B C : Fp[X]), A.degree < p → B.degree < p → C.degree < p →
      (A - B + C).degree < p := fun A B C hA hB hC =>
    lt_of_le_of_lt (degree_add_le _ _) (max_lt
      (lt_of_le_of_lt (degree_sub_le _ _) (max_lt hA hB)) hC)
  refine exists_rows_of_orders_vlow hp2 hn (hKp hW) hb (X' hW x) ?hX ?hr0 ?hrh (8 * N)
    (56 * N - 1 - 5 * p) ?hlob ?hlobp ?hlot ?hA ?hC ?hZ ?hVbE ?hVbF ?hVt
  case hX =>
    intro e j
    show projExtras _ _ _ = 0
    rw [projExtras_apply, if_pos ⟨j, by simp⟩]
  case hr0 => rw [hrN]; omega
  case hrh => rw [hrN]; omega
  case hlob => rw [hrN, geom_ja hW]; omega
  case hlobp => omega
  case hlot => rw [hrN, geom_rho hW]; omega
  case hA =>
    intro k
    have hk := hk6 k
    constructor
    · intro j hj
      rw [hrN] at hj
      rw [poly_blk hW x k 0]
      have := pt1_AF ⟨k.val, hk⟩
      exact chainAF hW x hker ⟨4 * k.val + (0 : Fin 4).val, by omega⟩ (by simpa using this.1)
        (by simpa using this.2.1) (by simpa using this.2.2) j hj
    · intro i hi
      rw [hrN] at hi
      rw [poly_blk hW x k 1]
      have := inf_AE ⟨k.val, hk⟩
      have h7 := wd7 hW; have h8 := wd8 hW
      exact Pilot146O.coeff_of_inf _ (polx_degree _ _) (wd N p 7 + wd N p 8) (3 * N) (by omega) (by omega)
        (fun j hj => chainInf2 hW x hker _ (by simpa using this.1) (by simpa using this.2) j hj) i hi
  case hC =>
    intro k
    have hk := hk6 k
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hrN] at hj
      rw [poly_blk hW x k 2]
      exact chainCF hW x hker _ (by simpa using pt1_CF ⟨k.val, hk⟩) j hj
    · intro j hj
      rw [poly_blk hW x k 2, poly_blk hW x k 3]
      exact chainDiff hW x hker _ _ (by intro h; have := congrArg Fin.val h; simp at this)
        (by simpa using ptm1_C ⟨k.val, hk⟩) j hj
    · intro i hi
      rw [hrN] at hi
      rw [poly_blk hW x k 3]
      have h7 := wd7 hW; have h8 := wd8 hW; have h9 := wd9 hW
      have := inf_CE ⟨k.val, hk⟩
      exact Pilot146O.coeff_of_inf _ (polx_degree _ _) (wd N p 7 + wd N p 8 + wd N p 9) (3 * N - 1)
        (by omega) (by omega)
        (fun j hj => chainInf3 hW x hker _ (by simpa using this.1) (by simpa using this.2.1)
          (by simpa using this.2.2) j hj) i hi
  case hZ =>
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hrN] at hj
      rw [poly_Z hW x 0]
      exact chainAF hW x hker _ (by simpa using pt1_ZF.1) (by simpa using pt1_ZF.2.1)
        (by simpa using pt1_ZF.2.2) j hj
    · intro i hi
      rw [hrN] at hi
      rw [poly_Z hW x 1]
      have h7 := wd7 hW; have h8 := wd8 hW
      exact Pilot146O.coeff_of_inf _ (polx_degree _ _) (wd N p 7 + wd N p 8) (3 * N) (by omega) (by omega)
        (fun j hj => chainInf2 hW x hker _ (by simpa using inf_ZE.1) (by simpa using inf_ZE.2) j hj) i hi
    · intro j hj
      rw [poly_Z hW x 0, poly_Z hW x 1]
      exact chainDiff hW x hker _ _ (by intro h; have := congrArg Fin.val h; simp at this)
        (by simpa using ptm1_Z) j hj
  case hVbE =>
    intro i
    have e1 : ∀ h, (⟨4 * (⟨0, hb⟩ : Fin (bN dsg N p)).val + (1 : Fin 4).val, h⟩ : Fin 28) = 1 :=
      fun h => Fin.ext (by simp)
    have e3 : ∀ h, (⟨4 * (⟨0, hb⟩ : Fin (bN dsg N p)).val + (3 : Fin 4).val, h⟩ : Fin 28) = 3 :=
      fun h => Fin.ext (by simp)
    have e25 : ∀ h, (⟨24 + (1 : Fin 2).val, h⟩ : Fin 28) = 25 := fun h => Fin.ext (by simp)
    rw [poly_blk hW x ⟨0, hb⟩ 1, poly_blk hW x ⟨0, hb⟩ 3, poly_Z hW x 1]
    simp only [e1, e3, e25]
    by_cases hi' : i < p
    · exact chainVE hW x hker i hi'
    · exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
        (hdeg3 _ _ _ (polx_degree _ _) (polx_degree _ _) (polx_degree _ _)) (by exact_mod_cast not_lt.mp hi'))
  case hVbF =>
    intro i hi
    have e0 : ∀ h, (⟨4 * (⟨0, hb⟩ : Fin (bN dsg N p)).val + (0 : Fin 4).val, h⟩ : Fin 28) = 0 :=
      fun h => Fin.ext (by simp)
    have e2 : ∀ h, (⟨4 * (⟨0, hb⟩ : Fin (bN dsg N p)).val + (2 : Fin 4).val, h⟩ : Fin 28) = 2 :=
      fun h => Fin.ext (by simp)
    have e24 : ∀ h, (⟨24 + (0 : Fin 2).val, h⟩ : Fin 28) = 24 := fun h => Fin.ext (by simp)
    rw [poly_blk hW x ⟨0, hb⟩ 0, poly_blk hW x ⟨0, hb⟩ 2, poly_Z hW x 0]
    simp only [e0, e2, e24]
    have h7 := wd7 hW
    exact Pilot146O.coeff_of_inf _ (hdeg3 _ _ _ (polx_degree _ _) (polx_degree _ _) (polx_degree _ _))
      (wd N p 7) (8 * N) (by omega) (by omega) (fun j hj => chainVF hW x hker j hj) i hi
  case hVt =>
    intro i hi
    rw [poly_blk hW x ⟨bN dsg N p - 1, by omega⟩ 1, poly_blk hW x ⟨bN dsg N p - 1, by omega⟩ 3]
    have h7 := wd7 hW; have h8 := wd8 hW; have h9 := wd9 hW; have h10 := wd10 hW
    have e1 : (⟨4 * (bN dsg N p - 1) + (1 : Fin 4).val, by omega⟩ : Fin 28) = 21 := by
      apply Fin.ext; simp only; omega
    have e3 : (⟨4 * (bN dsg N p - 1) + (3 : Fin 4).val, by omega⟩ : Fin 28) = 23 := by
      apply Fin.ext; simp only; omega
    simp only [e1, e3]
    exact Pilot146O.coeff_of_inf _ (lt_of_le_of_lt (degree_add_le _ _) (max_lt (polx_degree _ _) (polx_degree _ _)))
      (wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10) (56 * N - 1 - 5 * p) (by omega) (by omega)
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

/-- The graph functional `jet_0` (coordinate 26). -/
def low179 (p : ℕ) [Fact p.Prime] : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj (26 : Fin 28)).comp (emb pk p 28)

theorem low179_apply (y : Fin pk.d → Fp) : low179 p y = emb pk p 28 y 26 := rfl

theorem hG_179 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∃ G : Fp[X], G.degree < ((dsg.q N % p : ℕ) : WithBot ℕ) ∧
      ∀ e : Fin p, G.eval ((((dsg.H N : ℤ) - 1 - e : ℤ)) : Fp) = low179 p (x e) := by
  have hq := geom_qmod hW
  have h4 := wd4 hW; have h5 := wd5 hW
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj5 : ∀ k, jetP N p 5 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 4 + k) := by
    intro k; simp [jetP]
  have hv : ∀ g, g < 12 → (hasRow g (unitL 26) = true) → ∀ k, k < wd N p g →
      low179 p (jetP N p g k x) = 0 := by
    intro g hg hr k hk
    have := vanish_hasRow x hker g hg k hk (unitL 26) hr
    have e := sum_unitL (26 : Fin 28) (emb pk p 28 (jetP N p g k x))
    exact e.symm.trans this
  have hchain := Pilot146O.chain2 (Q := fun j => low179 p (Charts3.taylorJet (m := p) (d := pk.d) 1 j x) = 0)
    (a := wd N p 4) (b := wd N p 5)
    (fun k hk => by have := hv 4 (by norm_num) pt1_jet0.1 k hk; rw [hj4 k] at this; simpa using this)
    (fun k hk => by have := hv 5 (by norm_num) pt1_jet0.2 k hk; rw [hj5 k] at this; exact this)
  have := hG_of_taylor (low179 p) (((dsg.H N : ℤ) - 1 : ℤ) : Fp) (dsg.q N % p)
    (by have := hW.2.1; have := hW.1; omega) x (fun k hk => hchain k (by have := hW.2.2.2; omega))
  obtain ⟨G, hGd, hGe⟩ := this
  refine ⟨G, hGd, fun e => ?_⟩
  rw [← hGe e]
  congr 1
  push_cast
  ring

/-! ### Unique graph -/

theorem jet0_eq (m : ℕ) (e : Fin p) (h : m = e.val) :
    (jet0 m : (Fin p → Fin pk.d → Fp) →ₗ[Fp] (Fin pk.d → Fp)) = LinearMap.proj e := by
  subst h; simp [jet0, e.isLt]

theorem jetInf_eq (m : ℕ) (e : Fin p) (h : m = p - 1 - e.val) :
    (jetInf m : (Fin p → Fin pk.d → Fp) →ₗ[Fp] (Fin pk.d → Fp)) = LinearMap.proj e := by
  have hm : m < p := by have := e.isLt; omega
  simp only [jetInf, dif_pos hm]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem jet0_emb (x : Fin p → Fin pk.d → Fp) (k : ℕ) (hk : k < p) (c : Fin 28) :
    emb pk p 28 (jet0 k x) c = emb pk p 28 (x ⟨k, hk⟩) c := by
  rw [emb_jet0, jet0_coord]
  exact polx_coeff (Xr x) c ⟨k, hk⟩

theorem rowsum_aux (r : List ℤ) (y : Fin 28 → Fp) (hy : ∀ c : Fin 28, c.val < 26 → y c = 0) :
    ∑ c : Fin 28, ((r.getD c 0 : ℤ) : Fp) * y c =
      ((r.getD 26 0 : ℤ) : Fp) * y 26 + ((r.getD 27 0 : ℤ) : Fp) * y 27 := by
  refine Finset.sum_eq_add (26 : Fin 28) 27 (by decide) ?_ (fun h => absurd (Finset.mem_univ _) h)
    (fun h => absurd (Finset.mem_univ _) h)
  intro c _ hc
  have : c.val < 26 := by
    have h1 : c ≠ 26 := hc.1
    have h2 : c ≠ 27 := hc.2
    have := c.isLt
    have h1' : c.val ≠ 26 := fun h => h1 (Fin.ext h)
    have h2' : c.val ≠ 27 := fun h => h2 (Fin.ext h)
    omega
  rw [hy c this, mul_zero]

theorem raw_vanish (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 12) (r : List ℤ)
    (hr : hasRow g r = true) (jt k : ℕ) (hk : k < wd N p g) (hjet : jetP N p g k = jet0 jt) (hj : jt < p)
    (hs : ∀ c : Fin 28, c.val < 26 → emb pk p 28 (x ⟨jt, hj⟩) c = 0) :
    ((r.getD 26 0 : ℤ) : Fp) * emb pk p 28 (x ⟨jt, hj⟩) 26 +
      ((r.getD 27 0 : ℤ) : Fp) * emb pk p 28 (x ⟨jt, hj⟩) 27 = 0 := by
  have v := vanish_hasRow x hker g hg k hk r hr
  rw [hjet] at v
  rw [← rowsum_aux r _ hs, ← v]
  exact (Finset.sum_congr rfl fun c _ => by rw [jet0_emb x jt hj c]).symm

theorem jetInf_emb (x : Fin p → Fin pk.d → Fp) (m : ℕ) (hm : m < p) (c : Fin 28) :
    emb pk p 28 (jetInf m x) c = emb pk p 28 (x ⟨p - 1 - m, by omega⟩) c := by
  rw [emb_jetInf, jetInf_coord, if_pos hm]
  exact polx_coeff (Xr x) c ⟨p - 1 - m, by omega⟩

theorem raw_vanish_inf (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 12) (r : List ℤ)
    (hr : hasRow g r = true) (e : Fin p) (k : ℕ) (hk : k < wd N p g)
    (hjet : jetP N p g k = jetInf (p - 1 - e.val))
    (hs : ∀ c : Fin 28, c.val < 26 → emb pk p 28 (x e) c = 0) :
    ((r.getD 26 0 : ℤ) : Fp) * emb pk p 28 (x e) 26 + ((r.getD 27 0 : ℤ) : Fp) * emb pk p 28 (x e) 27 = 0 := by
  have v := vanish_hasRow x hker g hg k hk r hr
  rw [hjet] at v
  rw [← rowsum_aux r _ hs, ← v]
  have hm : p - 1 - e.val < p := by have := e.isLt; omega
  have he : (⟨p - 1 - (p - 1 - e.val), by omega⟩ : Fin p) = e := Fin.ext (by have := e.isLt; simp only; omega)
  refine (Finset.sum_congr rfl fun c _ => ?_).symm
  rw [jetInf_emb x _ hm c, he]

/-- A raw row: contains its row, `ρ_26 | 30030^40`, `ρ_26 ≠ 0` and `ρ_27 = c * ρ_26`. -/
def rawRowOK (g i : ℕ) (c : ℤ) : Bool :=
  hasRow g ((oRows g).getD i []) && decide (((oRows g).getD i []).getD 26 0 ∣ 30030 ^ 40) &&
    decide (((oRows g).getD i []).getD 26 0 ≠ 0) &&
    decide (((oRows g).getD i []).getD 27 0 = c * ((oRows g).getD i []).getD 26 0)

/-- Row index of `raw[1,1].degree` in the `∞` group `g = 7..11`. -/
def ridx1 (g : ℕ) : ℕ := match g with | 7 => 17 | 8 => 15 | 9 => 8 | 10 => 2 | _ => 1

set_option maxRecDepth 100000 in
theorem raw_ok : rawRowOK 1 0 0 = true ∧ rawRowOK 1 6 1 = true ∧ rawRowOK 2 0 1 = true ∧
    (∀ g : Fin 5, rawRowOK (g.val + 7) (ridx1 (g.val + 7)) 0 = true) := by
  decide +kernel

theorem chainJet0 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 4 + wd N p 5, (taylor 1 (polx (Xr x) 26)).coeff j = 0 := by
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj5 : ∀ k, jetP N p 5 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 4 + k) := by
    intro k; simp [jetP]
  exact Pilot146O.chain2 (Q := fun j => (taylor 1 (polx (Xr x) 26)).coeff j = 0)
    (fun k hk => by simpa using vtaylor_unit x hker 4 (by norm_num) 1 0 hj4 26 pt1_jet0.1 k hk)
    (vtaylor_unit x hker 5 (by norm_num) 1 (wd N p 4) hj5 26 pt1_jet0.2)

theorem chainLow (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10 + wd N p 11,
      (polx (Xr x) 27).coeff (p - 1 - j) = 0 := by
  have hj7 : ∀ k, jetP N p 7 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have hj10 : ∀ k, jetP N p 10 k = jetInf (wd N p 7 + wd N p 8 + wd N p 9 + k) := by intro k; simp [jetP]
  have hj11 : ∀ k, jetP N p 11 k = jetInf (wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10 + k) := by
    intro k; simp [jetP]
  have := wd7 hW; have := wd8 hW; have := wd9 hW; have := wd10 hW; have := wd11 hW
  have := hW.2.1; have := hW.2.2.1; have := hW.1; have := hW.2.2.2
  obtain ⟨r7, r8, r9, r10, r11⟩ := inf_low
  exact Pilot146O.chain5 (Q := fun j => (polx (Xr x) 27).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 7 (by norm_num) 0 hj7 (by omega) 27 r7 k hk)
    (vinf_unit x hker 8 (by norm_num) (wd N p 7) hj8 (by omega) 27 r8)
    (vinf_unit x hker 9 (by norm_num) (wd N p 7 + wd N p 8) hj9 (by omega) 27 r9)
    (vinf_unit x hker 10 (by norm_num) (wd N p 7 + wd N p 8 + wd N p 9) hj10 (by omega) 27 r10)
    (vinf_unit x hker 11 (by norm_num) (wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10) hj11 (by omega) 27 r11)

/-- The reversed jet `p - 1 - e` lies in one of the `∞` groups 7..11. -/
theorem inf_group (hW : Win N p) (e : Fin p)
    (hm : p - 1 - e.val < wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10 + wd N p 11) :
    ∃ g k, 7 ≤ g ∧ g ≤ 11 ∧ k < wd N p g ∧ jetP N p g k = jetInf (p - 1 - e.val) ∧
      (p - 1 - e.val < wd N p 7 → g = 7) := by
  have hep := e.isLt
  by_cases h7 : p - 1 - e.val < wd N p 7
  · exact ⟨7, p - 1 - e.val, le_refl _, by norm_num, h7,
      by simp [jetP], fun _ => rfl⟩
  by_cases h8 : p - 1 - e.val < wd N p 7 + wd N p 8
  · refine ⟨8, p - 1 - e.val - wd N p 7, by norm_num, by norm_num, by omega, ?_, fun h => absurd h h7⟩
    simp only [jetP]; congr 1; omega
  by_cases h9 : p - 1 - e.val < wd N p 7 + wd N p 8 + wd N p 9
  · refine ⟨9, p - 1 - e.val - (wd N p 7 + wd N p 8), by norm_num, by norm_num, by omega, ?_,
      fun h => absurd h h7⟩
    simp only [jetP]; congr 1; omega
  by_cases h10 : p - 1 - e.val < wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10
  · refine ⟨10, p - 1 - e.val - (wd N p 7 + wd N p 8 + wd N p 9), by norm_num, by norm_num, by omega, ?_,
      fun h => absurd h h7⟩
    simp only [jetP]; congr 1; omega
  · refine ⟨11, p - 1 - e.val - (wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10), by norm_num, le_refl _,
      by omega, ?_, fun h => absurd h h7⟩
    simp only [jetP]; congr 1; omega

theorem raw_ok_inf (g : ℕ) (h7 : 7 ≤ g) (h11 : g ≤ 11) : rawRowOK g (ridx1 g) 0 = true := by
  have := raw_ok.2.2.2 ⟨g - 7, by omega⟩
  simp only [Fin.val_mk] at this
  rwa [show g - 7 + 7 = g by omega] at this

theorem slot_zero (hW : Win N p) (x : Fin p → Fin pk.d → Fp)
    (hproj : ∀ e, projExtras (hKp hW) (emb pk p 28 (x e)) = 0) (e : Fin p) (c : Fin 28)
    (hc : c.val < 26) : emb pk p 28 (x e) c = 0 := by
  have h0 := congrFun (hproj e) c
  rw [projExtras_apply] at h0
  have hne : ¬ isExtra (hKp hW) c := by
    rintro ⟨j, hj⟩
    have h := Pilot146O.ck_X_val (hKp hW) j
    have hc' : c = (ckEquiv (hKp hW)).symm (Sum.inr (Sum.inr j)) := by rw [← hj]; simp
    have hb : bN dsg N p = 6 := geom_bN hW
    have hv : c.val = bN dsg N p * 4 + 2 + j.val := by rw [hc']; exact h
    omega
  rw [if_neg hne] at h0
  exact h0

set_option maxHeartbeats 4000000 in
theorem hinj_179 (hW : Win N p) (hpD : ¬ (p : ℤ) ∣ pk.D) (x : Fin p → Fin pk.d → Fp)
    (hker : JetKer N p x)
    (hproj : ∀ e, projExtras (hKp hW) (emb pk p 28 (x e)) = 0) : x = 0 := by
  have h13 : 13 < p := by have := hW.2.1; have := hW.1; omega
  have hslot := slot_zero hW x hproj
  have w1 := wd1 hW; have w7 := wd7 hW; have w8 := wd8 hW; have w9 := wd9 hW; have w10 := wd10 hW
  have w11 := wd11 hW
  have hp6 := hW.2.1; have hp78 := hW.2.2.1; have hN := hW.1; have hodd := hW.2.2.2
  obtain ⟨r1a, r1g, r2g, rinf⟩ := raw_ok
  simp only [rawRowOK, Bool.and_eq_true, decide_eq_true_eq] at r1a r1g
  obtain ⟨⟨⟨hr1a, d1a⟩, n1a⟩, e1a⟩ := r1a
  obtain ⟨⟨⟨hr1g, d1g⟩, n1g⟩, e1g⟩ := r1g
  -- low vanishes on e ≥ w1
  have h27 : ∀ e : Fin p, wd N p 1 ≤ e.val → emb pk p 28 (x e) 27 = 0 := by
    intro e he
    have := Pilot146O.coeff_of_inf (polx (Xr x) 27) (polx_degree _ _)
      (wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10 + wd N p 11) (wd N p 1) (by omega) (by omega)
      (fun j hj => chainLow hW x hker j hj) e.val he
    have h2 := polx_coeff (Xr x) 27 e
    rw [this] at h2
    exact h2.symm
  -- jet_0 vanishes everywhere
  have h26 : ∀ e : Fin p, emb pk p 28 (x e) 26 = 0 := by
    intro e
    by_cases h1 : e.val < wd N p 1
    · have v := raw_vanish x hker 1 (by norm_num) _ hr1a e.val e.val h1 (by simp [jetP]) e.isLt
        (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e1a] at v; simp only [zero_mul, Int.cast_zero, add_zero] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ d1a h13
      exact (mul_eq_zero.mp v).resolve_left hu
    · have hm : p - 1 - e.val < wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10 + wd N p 11 := by omega
      obtain ⟨g, k, hg7, hg11, hk, hjet, _⟩ := inf_group hW e hm
      have hr := raw_ok_inf g hg7 hg11
      simp only [rawRowOK, Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨⟨⟨hrow, hd⟩, hn⟩, he0⟩ := hr
      have v := raw_vanish_inf x hker g (by omega) _ hrow e k hk hjet (hslot e)
      rw [he0, h27 e (by omega)] at v
      simp only [zero_mul, Int.cast_zero, add_zero, mul_zero] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ hd h13
      exact (mul_eq_zero.mp v).resolve_left hu
  have h27' : ∀ e : Fin p, emb pk p 28 (x e) 27 = 0 := by
    intro e
    by_cases he : wd N p 1 ≤ e.val
    · exact h27 e he
    · have h1 : e.val < wd N p 1 := by omega
      have v := raw_vanish x hker 1 (by norm_num) _ hr1g e.val e.val h1 (by simp [jetP]) e.isLt
        (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e1g, h26 e] at v
      simp only [mul_zero, zero_add, Int.cast_mul, Int.cast_one, one_mul] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ d1g h13
      have hu' : (((((oRows 1).getD 6 []).getD 27 0 : ℤ)) : Fp) ≠ 0 := by
        rw [e1g]; simpa using hu
      exact (mul_eq_zero.mp v).resolve_left hu'
  have hinjE : Function.Injective (emb pk p 28) :=
    emb_injective CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.pk_sound rfl (not_dvd_delta hpD)
  funext e
  apply hinjE
  funext c
  simp only [Pi.zero_apply, map_zero]
  show emb pk p 28 (x e) c = 0
  have hc := c.isLt
  by_cases h1 : c.val < 26
  · exact hslot e c h1
  · have : c = 26 ∨ c = 27 := by
      rcases (by omega : c.val = 26 ∨ c.val = 27) with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    rcases this with rfl | rfl
    · exact h26 e
    · exact h27' e

end
end Part2

end CatalanMeasure.GenD.Uniform.W.Charts6.L0179
