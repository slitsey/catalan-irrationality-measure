module
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0145.Hdom
public import CatalanMeasure.GenD.Uniform.W.Charts3.GraphJets
public import CatalanMeasure.GenD.Uniform.W.Charts6.Unit13
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# L0145: the graph coordinate polynomial `hG` and the unique-graph lemma `hinj`

`jet_0 = 31`, `@low:raw[1,1] = 32`.  With vanishing slot coordinates, the stored rows leave only the two graph entries.
`low (positions e ≥ w1)` is killed by the slack rows (unit `e_32`, groups 6..10); then the prefix rows (`raw[2,0]`, `e < w1`)
and the graph row (`raw[1,1]`, `w1 ≤ e < w1 + w2`) kill `jet_0`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6.L0145
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric Finset
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap Mx emb_injective not_dvd_delta)
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- The graph functional `jet_0` (coordinate 31). -/
def low145 (p : ℕ) [Fact p.Prime] : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj (31 : Fin 33)).comp (emb pk p 33)

theorem low145_apply (y : Fin pk.d → Fp) : low145 p y = emb pk p 33 y 31 := rfl

theorem hG_145 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∃ G : Fp[X], G.degree < ((dsg.q N % p : ℕ) : WithBot ℕ) ∧
      ∀ e : Fin p, G.eval ((((dsg.H N : ℤ) - 1 - e : ℤ)) : Fp) = low145 p (x e) := by
  have hq := geom_qmod hW
  have h3 := wd3 hW; have h4 := wd4 hW
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 3 + k) := by
    intro k; simp [jetP]
  have hv : ∀ g, g < 11 → (hasRow g (unitL 31) = true) → ∀ k, k < wd N p g →
      low145 p (jetP N p g k x) = 0 := by
    intro g hg hr k hk
    have := vanish_hasRow x hker g hg k hk (unitL 31) hr
    have e := sum_unitL (31 : Fin 33) (emb pk p 33 (jetP N p g k x))
    exact e.symm.trans this
  have hchain := Pilot146O.chain2 (Q := fun j => low145 p (Charts3.taylorJet (m := p) (d := pk.d) 1 j x) = 0)
    (a := wd N p 3) (b := wd N p 4)
    (fun k hk => by have := hv 3 (by norm_num) pt1_jet0.1 k hk; rw [hj3 k] at this; simpa using this)
    (fun k hk => by have := hv 4 (by norm_num) pt1_jet0.2 k hk; rw [hj4 k] at this; exact this)
  have := hG_of_taylor (low145 p) (((dsg.H N : ℤ) - 1 : ℤ) : Fp) (dsg.q N % p)
    (by have := hW.2.1; have := hW.1; omega) x (fun k hk => hchain k (by have := hW.2.2.2; omega))
  obtain ⟨G, hGd, hGe⟩ := this
  refine ⟨G, hGd, fun e => ?_⟩
  rw [← hGe e]
  congr 1
  push_cast
  ring

/-! ### Unique graph -/

theorem jet0_emb (x : Fin p → Fin pk.d → Fp) (k : ℕ) (hk : k < p) (c : Fin 33) :
    emb pk p 33 (jet0 k x) c = emb pk p 33 (x ⟨k, hk⟩) c := by
  rw [emb_jet0, jet0_coord]
  exact polx_coeff (Xr x) c ⟨k, hk⟩

theorem rowsum_aux (r : List ℤ) (y : Fin 33 → Fp) (hy : ∀ c : Fin 33, c.val < 31 → y c = 0) :
    ∑ c : Fin 33, ((r.getD c 0 : ℤ) : Fp) * y c =
      ((r.getD 31 0 : ℤ) : Fp) * y 31 + ((r.getD 32 0 : ℤ) : Fp) * y 32 := by
  refine Finset.sum_eq_add (31 : Fin 33) 32 (by decide) ?_ (fun h => absurd (Finset.mem_univ _) h)
    (fun h => absurd (Finset.mem_univ _) h)
  intro c _ hc
  have : c.val < 31 := by
    have h1 : c ≠ 31 := hc.1
    have h2 : c ≠ 32 := hc.2
    have := c.isLt
    have h1' : c.val ≠ 31 := fun h => h1 (Fin.ext h)
    have h2' : c.val ≠ 32 := fun h => h2 (Fin.ext h)
    omega
  rw [hy c this, mul_zero]

theorem raw_vanish (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (r : List ℤ)
    (hr : hasRow g r = true) (jt k : ℕ) (hk : k < wd N p g) (hjet : jetP N p g k = jet0 jt) (hj : jt < p)
    (hs : ∀ c : Fin 33, c.val < 31 → emb pk p 33 (x ⟨jt, hj⟩) c = 0) :
    ((r.getD 31 0 : ℤ) : Fp) * emb pk p 33 (x ⟨jt, hj⟩) 31 +
      ((r.getD 32 0 : ℤ) : Fp) * emb pk p 33 (x ⟨jt, hj⟩) 32 = 0 := by
  have v := vanish_hasRow x hker g hg k hk r hr
  rw [hjet] at v
  rw [← rowsum_aux r _ hs, ← v]
  exact (Finset.sum_congr rfl fun c _ => by rw [jet0_emb x jt hj c]).symm

/-- A raw row: contains its row, `ρ_31 | 2310^40`, `ρ_31 ≠ 0`, and `ρ_32 = c * ρ_31`. -/
def rawRowOK (g i : ℕ) (c : ℤ) : Bool :=
  hasRow g ((oRows g).getD i []) && decide (((oRows g).getD i []).getD 31 0 ∣ 30030 ^ 40) &&
    decide (((oRows g).getD i []).getD 31 0 ≠ 0) &&
    decide (((oRows g).getD i []).getD 32 0 = c * ((oRows g).getD i []).getD 31 0)

set_option maxRecDepth 100000 in
theorem raw_ok : rawRowOK 1 0 0 = true ∧ rawRowOK 1 10 1 = true ∧ rawRowOK 2 0 1 = true := by
  decide +kernel

theorem chainJet0 (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 3 + wd N p 4, (taylor 1 (polx (Xr x) 31)).coeff j = 0 := by
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := pk.d) 1 (wd N p 3 + k) := by
    intro k; simp [jetP]
  exact Pilot146O.chain2 (Q := fun j => (taylor 1 (polx (Xr x) 31)).coeff j = 0)
    (fun k hk => by simpa using vtaylor_unit x hker 3 (by norm_num) 1 0 hj3 31 pt1_jet0.1 k hk)
    (vtaylor_unit x hker 4 (by norm_num) 1 (wd N p 3) hj4 31 pt1_jet0.2)

theorem chainLow (hW : Win N p) (x : Fin p → Fin pk.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10,
      (polx (Xr x) 32).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 6 + wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have hj10 : ∀ k, jetP N p 10 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + k) := by
    intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := wd8 hW; have := wd9 hW; have := wd10 hW
  have := hW.2.1; have := hW.2.2.1; have := hW.1; have := hW.2.2.2
  obtain ⟨r6, r7, r8, r9, r10⟩ := inf_low
  exact Pilot146O.chain5 (Q := fun j => (polx (Xr x) 32).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 6 (by norm_num) 0 hj6 (by omega) 32 r6 k hk)
    (vinf_unit x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) 32 r7)
    (vinf_unit x hker 8 (by norm_num) (wd N p 6 + wd N p 7) hj8 (by omega) 32 r8)
    (vinf_unit x hker 9 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8) hj9 (by omega) 32 r9)
    (vinf_unit x hker 10 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9) hj10 (by omega) 32 r10)

theorem slot_zero (hW : Win N p) (x : Fin p → Fin pk.d → Fp)
    (hproj : ∀ e, projExtras (hKp hW) (insL p (emb pk p 33 (x e))) = 0) (e : Fin p) (c : Fin 33)
    (hc : c.val < 31) : emb pk p 33 (x e) c = 0 := by
  have h0 := congrFun (hproj e) (iotaF c)
  rw [projExtras_apply] at h0
  have hne : ¬ isExtra (hKp hW) (iotaF c) := by
    rintro ⟨j, hj⟩
    have h := Pilot146O.ck_X_val (hKp hW) j
    have hc' : iotaF c = (ckEquiv (hKp hW)).symm (Sum.inr (Sum.inr j)) := by rw [← hj]; simp
    have hb : bN dsg N p = 10 := geom_b hW
    have hv : (iotaF c).val = bN dsg N p * 4 + 2 + j.val := by rw [hc']; exact h
    rw [iotaF_val] at hv
    unfold iotaN at hv
    have := j.isLt
    split_ifs at hv <;> omega
  rw [if_neg hne, ins_iota] at h0
  exact h0

set_option maxHeartbeats 4000000 in
theorem hinj_145 (hW : Win N p) (hpD : ¬ (p : ℤ) ∣ pk.D) (x : Fin p → Fin pk.d → Fp)
    (hker : JetKer N p x)
    (hproj : ∀ e, projExtras (hKp hW) (insL p (emb pk p 33 (x e))) = 0) : x = 0 := by
  have h11 : 13 < p := by have := hW.2.1; have := hW.1; omega
  have hslot := slot_zero hW x hproj
  have w1 := wd1 hW; have w2 := wd2 hW; have w3 := wd3 hW; have w4 := wd4 hW
  have w6 := wd6 hW; have w7 := wd7 hW; have w8 := wd8 hW; have w9 := wd9 hW; have w10 := wd10 hW
  have hp6 := hW.2.1; have hp6' := hW.2.2.1; have hN := hW.1; have hodd := hW.2.2.2
  obtain ⟨r1a, r1g, r2g⟩ := raw_ok
  simp only [rawRowOK, Bool.and_eq_true, decide_eq_true_eq] at r1a r1g r2g
  obtain ⟨⟨⟨hr1a, d1a⟩, n1a⟩, e1a⟩ := r1a
  obtain ⟨⟨⟨hr1g, d1g⟩, n1g⟩, e1g⟩ := r1g
  obtain ⟨⟨⟨hr2g, d2g⟩, n2g⟩, e2g⟩ := r2g
  -- low vanishes on e ≥ w1
  have h43 : ∀ e : Fin p, wd N p 1 ≤ e.val → emb pk p 33 (x e) 32 = 0 := by
    intro e he
    have := Pilot146O.coeff_of_inf (polx (Xr x) 32) (polx_degree _ _)
      (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10) (wd N p 1) (by omega) (by omega)
      (fun j hj => chainLow hW x hker j hj) e.val he
    have h2 := polx_coeff (Xr x) 32 e
    rw [this] at h2
    exact h2.symm
  -- jet_0 vanishes for e < w1 + w2
  have h42 : ∀ e : Fin p, e.val < wd N p 1 + wd N p 2 → emb pk p 33 (x e) 31 = 0 := by
    intro e he
    by_cases h1 : e.val < wd N p 1
    · have v := raw_vanish x hker 1 (by norm_num) _ hr1a e.val e.val h1 (by simp [jetP]) e.isLt
        (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e1a] at v; simp only [zero_mul, Int.cast_zero, add_zero] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ d1a h11
      exact (mul_eq_zero.mp v).resolve_left hu
    · have v := raw_vanish x hker 2 (by norm_num) _ hr2g (e.val) (e.val - wd N p 1) (by omega)
        (by simp [jetP]; congr 1; omega) e.isLt (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e2g, h43 e (by omega)] at v
      simp only [mul_zero, add_zero] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ d2g h11
      exact (mul_eq_zero.mp v).resolve_left hu
  have hf42 : polx (Xr x) 31 = 0 := by
    refine Pilot146O.poly_zero_of_orders _ (p - 3 * N) (3 * N) (wd N p 1 + wd N p 2) (polx_degree _ _)
      (by omega) (by omega) ?_ ?_
    · have h1 : (X - 1 : Fp[X]) = X - C 1 := by simp
      rw [h1, pow_dvd_iff_taylor]
      intro k hk
      exact chainJet0 hW x hker k (by omega)
    · intro e he
      have hep : e < p := by omega
      have := polx_coeff (Xr x) 31 ⟨e, hep⟩
      simp only at this
      rw [this]
      exact h42 ⟨e, hep⟩ he
  have h42' : ∀ e : Fin p, emb pk p 33 (x e) 31 = 0 := by
    intro e
    have := polx_coeff (Xr x) 31 e
    rw [hf42] at this
    simpa using this.symm
  have h43' : ∀ e : Fin p, emb pk p 33 (x e) 32 = 0 := by
    intro e
    by_cases he : wd N p 1 ≤ e.val
    · exact h43 e he
    · have h1 : e.val < wd N p 1 := by omega
      have v := raw_vanish x hker 1 (by norm_num) _ hr1g e.val e.val h1 (by simp [jetP]) e.isLt
        (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e1g, h42' e] at v
      simp only [mul_zero, zero_add, Int.cast_mul, Int.cast_one, one_mul] at v
      have hu := CatalanMeasure.GenD.Uniform.W.Charts6.unit_of_dvd13 _ d1g h11
      have hu' : (((((oRows 1).getD 10 []).getD 32 0 : ℤ)) : Fp) ≠ 0 := by
        rw [e1g]; simpa using hu
      exact (mul_eq_zero.mp v).resolve_left hu'
  have hinjE : Function.Injective (emb pk p 33) :=
    emb_injective CatalanMeasure.GenD.Uniform.Bank532.Pk.L0145_k280_47.pk_sound rfl (not_dvd_delta hpD)
  funext e
  apply hinjE
  funext c
  simp only [Pi.zero_apply, map_zero]
  show emb pk p 33 (x e) c = 0
  have hc := c.isLt
  by_cases h1 : c.val < 31
  · exact hslot e c h1
  · have : c = 31 ∨ c = 32 := by
      rcases (by omega : c.val = 31 ∨ c.val = 32) with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    rcases this with rfl | rfl
    · exact h42' e
    · exact h43' e

end
end CatalanMeasure.GenD.Uniform.W.Charts6.L0145
