module
public import CatalanMeasure.GenD.Uniform.W.Charts.Rows
public import CatalanMeasure.GenD.Uniform.W.Charts.Seen
public import CatalanMeasure.GenD.Uniform.W.Prof.OfWindow
public import CatalanMeasure.GenD.Uniform.W.Prof.Cover
@[expose] public section
set_option Elab.async false

/-!
# `chartOf`: generated charts, and `PhysWindow` from the slot system alone

* `chartRows pd Z K κ` : the rows of the chart of the group `κ = (S, jlo, cnt)`: the integerised
  seen covectors `ψ(jlo + i, S)`, `i < cnt`, on the `K` profile coordinates (`Rows.rowInt`).
* `chartOf` / `generatePacket` : a stored packet whose chart rows are replaced by the generated
  rows (the rest of a chart, i.e. the rank and kernel certificate, stays stored).
* `CellOK` : what a slot system must satisfy at one point `(N, p)` of a window: profile data,
  `V_p ⊂ dom`, group keys of the cell cover all seen positions, moment bounds, `p ∤ Zmom`.
* `physWindow_of_chartOf` : **`PhysWindow` holds for the window "a slot system with `CellOK`
  exists"**, with weights `wOf` = number of positions of each group.  No chart literal enters.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section

/-- Rows of the chart of group `κ` on `K` profile coordinates. -/
def chartRows (pd : ProfData) (Z K : ℕ) (κ : Key) : List (List ℤ) :=
  (List.range κ.2.2).map fun i => (List.range K).map fun k => rowInt pd Z (κ.2.1 + i) κ.1 k

theorem length_chartRows (pd : ProfData) (Z K : ℕ) (κ : Key) :
    (chartRows pd Z K κ).length = κ.2.2 := by simp [chartRows]

theorem Mx_chartRows (pd : ProfData) (Z K : ℕ) (κ : Key) {r k : ℕ} (hr : r < κ.2.2) (hk : k < K) :
    Mx (chartRows pd Z K κ) r k = rowInt pd Z (κ.2.1 + r) κ.1 k := by
  simp [Mx, chartRows, List.getD_eq_getElem?_getD, hr, hk]

/-- The data of a cell: profile coefficients and the four cell integers
`c = ⌊b/p⌋`, `c' = ⌊L/p⌋`, `Slo ≤ ⌊(H-emax)/p⌋`, `⌊(H-1)/p⌋ ≤ Shi`. -/
structure ChartCell where
  pd : ProfData
  c : ℕ
  c' : ℕ
  Slo : ℤ
  Shi : ℤ

/-- The group keys of the cell (generated). -/
def ChartCell.types (cc : ChartCell) : List Key := typesOf cc.c cc.c' cc.Slo cc.Shi
/-- Moment bounds of the cell. -/
def ChartCell.Ub (cc : ChartCell) : ℕ := cc.Shi.toNat + 3
def ChartCell.Jb (cc : ChartCell) : ℕ := cc.c' + 1

/-- Replace the rows of a stored chart certificate by the generated rows of group `κ`. -/
def chartOf (cc : ChartCell) (K : ℕ) (κ : Key) (cert : Chart) : Chart :=
  { cert with rows := chartRows cc.pd (Zmom cc.Ub cc.Jb) K κ }

/-- A stored packet (certificates only) with all chart rows generated from the cell data. -/
def generatePacket (pk : Packet) (cc : ChartCell) : Packet :=
  { pk with charts := (pk.charts.zip cc.types).map fun ck => chartOf cc pk.n ck.2 ck.1 }

/-- The packet's chart rows are the generated ones. -/
structure ChartsOf (pk : Packet) (cc : ChartCell) : Prop where
  len : cc.types.length = pk.charts.length
  rows : ∀ g : Fin pk.charts.length, (pk.chart g).rows =
    chartRows cc.pd (Zmom cc.Ub cc.Jb) pk.n (cc.types.getD g (0, 0, 0))

theorem generate_chartsOf (pk : Packet) (cc : ChartCell) (h : cc.types.length = pk.charts.length) :
    ChartsOf (generatePacket pk cc) cc := by
  refine ⟨by simp [generatePacket, List.length_zip, h], fun g => ?_⟩
  obtain ⟨i, hi⟩ := g
  have hi' : i < cc.types.length := by simpa [generatePacket, List.length_zip, h] using hi
  have hi'' : i < pk.charts.length := h ▸ hi'
  simp [Packet.chart, generatePacket, chartOf, List.get_eq_getElem, List.getElem_zip,
    List.getD_eq_getElem?_getD, hi']

/-- Number of positions of the group `g` (the weight `w_g(N,p)`). -/
def wOf (P : Parameters) (pk : Packet) (cc : ChartCell) (emax : ℕ → ℕ → ℕ)
    (g : Fin pk.charts.length) (N p : ℕ) : ℕ :=
  (posList (P.H N) (P.b N) (P.L N) p (emax N p) (cc.types.getD g (0, 0, 0))).length

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- What a slot system must satisfy at one window point so that the generated charts identify it. -/
structure CellOK (P : Parameters) (pk : Packet) (cc : ChartCell) (c emax : ℕ → ℕ → ℕ)
    (N p : ℕ) [Fact p.Prime] (S : SlotSystem P N p) : Prop where
  hK : S.K = pk.n
  hD : S.D = c N p
  hE : S.emax = emax N p
  real : cc.pd.Realises S.prof
  dom : ∀ x : Fin S.D → Fin pk.d → ZMod p, (fun d' => emb pk p S.K (x d')) ∈ S.dom
  guard : P.b N / p = cc.c ∧ P.L N / p = cc.c' ∧ cc.Slo ≤ ((P.H N : ℤ) - emax N p) / p ∧
    ((P.H N : ℤ) - 1) / p ≤ cc.Shi
  hH : cc.Ub ≤ P.H N
  unit : ¬ p ∣ Zmom cc.Ub cc.Jb

/-- The window: a slot system with `CellOK` exists. -/
def ChartWin (P : Parameters) (pk : Packet) (cc : ChartCell) (c emax : ℕ → ℕ → ℕ)
    (N p : ℕ) : Prop :=
  ∀ hp : p.Prime, haveI : Fact p.Prime := ⟨hp⟩;
    ∃ S : SlotSystem P N p, CellOK P pk cc c emax N p S

theorem ZMod_Zmom_ne {Ub Jb : ℕ} (h : ¬ p ∣ Zmom Ub Jb) : ((Zmom Ub Jb : ℕ) : ZMod p) ≠ 0 := by
  intro h0
  exact h ((ZMod.natCast_eq_zero_iff _ p).mp h0)

/-- **Chart identification from the generated rows.** -/
def identOfCell (hp0 : 0 < p) {pk : Packet} {cc : ChartCell} (hch : ChartsOf pk cc)
    {c emax : ℕ → ℕ → ℕ} {S : SlotSystem P N p} (hS : CellOK P pk cc c emax N p S) :
    Ident S pk (fun g => wOf P pk cc emax g N p) where
  hK := hS.hK
  pos := fun g k => (posList (P.H N) (P.b N) (P.L N) p (emax N p)
    (cc.types.getD g (0, 0, 0))).getD k 0
  dom := hS.dom
  cover := by
    intro j h1 h2 e a he ha
    obtain ⟨hS1, hlo, hhi⟩ := seenKey_cover hp0 h1 h2 ha
    set κ := seenKey (P.H N) (P.b N) (P.L N) p e with hκ
    have hcnt : 0 < κ.2.2 := by omega
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
    have heE : e < emax N p := hS.hE ▸ he
    have hSlo : cc.Slo ≤ ((P.H N : ℤ) - 1 - e) / p := by
      refine hS.guard.2.2.1.trans (Int.ediv_le_ediv hpz ?_)
      have : (e : ℤ) + 1 ≤ emax N p := by exact_mod_cast heE
      omega
    have hShi : ((P.H N : ℤ) - 1 - e) / p ≤ cc.Shi :=
      (Int.ediv_le_ediv hpz (by omega)).trans hS.guard.2.2.2
    have hmem : seenKey (P.H N) (P.b N) (P.L N) p e ∈ cc.types := by
      have := seenKey_mem_typesOf (H := P.H N) (b := P.b N) (L := P.L N) (e := e) hp0 hSlo hShi
      rw [hS.guard.1, hS.guard.2.1] at this
      exact this
    obtain ⟨i, hi, hiκ⟩ := List.mem_iff_getElem.mp hmem
    have hig : i < pk.charts.length := hch.len ▸ hi
    let g : Fin pk.charts.length := ⟨i, hig⟩
    have hgκ : cc.types.getD g (0, 0, 0) = κ := by
      simp [g, List.getD_eq_getElem?_getD, hi, hiκ]
      rfl
    have hepos : e ∈ posList (P.H N) (P.b N) (P.L N) p (emax N p) (cc.types.getD g (0, 0, 0)) := by
      rw [hgκ, mem_posList]
      exact ⟨hS.hE ▸ he, rfl⟩
    obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hepos
    refine ⟨g, ⟨k, hk⟩, ?_, ?_⟩
    · show (posList (P.H N) (P.b N) (P.L N) p (emax N p) (cc.types.getD g (0, 0, 0))).getD k 0 = e
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact hkv
    · intro y hy
      have hb2 : κ.2.1 + κ.2.2 ≤ cc.c' + 1 := by
        have := seenKey_sum_le (H := P.H N) (b := P.b N) (L := P.L N) (e := e) hp0 hcnt
        rw [hS.guard.2.1] at this
        exact this
      have hJb : j / p < cc.Jb := by unfold ChartCell.Jb; omega
      have hSb : (a.toNat + 3 ≤ cc.Ub) := by
        have hk1 : κ.1 = ((P.H N : ℤ) - 1 - e) / p := rfl
        unfold ChartCell.Ub; rw [← hS1]; omega
      set J := j / p with hJ
      have hrows := hch.rows g
      rw [hgκ] at hrows
      have hlen : (pk.chart g).rows.length = κ.2.2 := by rw [hrows, length_chartRows]
      have hrJ : J - κ.2.1 < (pk.chart g).rows.length := by omega
      let Zinv : ZMod p := ((Zmom cc.Ub cc.Jb : ℕ) : ZMod p)⁻¹
      let μ : Fin (pk.chart g).rows.length → ZMod p := fun r => if (r : ℕ) = J - κ.2.1 then Zinv else 0
      refine vanish_of_comb pk (pk.chart g) S.K (S.prof.psi (P.H N) J a) μ ?_ y hy
      intro kk
      have hsum : ∑ r : Fin (pk.chart g).rows.length, μ r * chartMat (pk.chart g) p S.K r kk =
          μ ⟨J - κ.2.1, hrJ⟩ * chartMat (pk.chart g) p S.K ⟨J - κ.2.1, hrJ⟩ kk := by
        rw [Finset.sum_eq_single ⟨J - κ.2.1, hrJ⟩]
        · intro r _ hr
          have : (r : ℕ) ≠ J - κ.2.1 := fun h => hr (Fin.ext h)
          simp [μ, this]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum]
      have hkk : (kk : ℕ) < pk.n := hS.hK ▸ kk.2
      have hMx : Mx (pk.chart g).rows (J - κ.2.1) kk =
          rowInt cc.pd (Zmom cc.Ub cc.Jb) J a kk := by
        rw [hrows, Mx_chartRows cc.pd _ _ κ (by omega) hkk]
        have : κ.2.1 + (J - κ.2.1) = J := by omega
        rw [this, hS1]
      have hmod := rowInt_mod (p := p) hS.unit cc.pd S.prof hS.real kk (J := J) (S := a)
        (H := P.H N) hJb hSb (by have := hS.hH; omega)
      simp only [μ, chartMat, hMx, if_true]
      rw [hmod]
      have hne := ZMod_Zmom_ne (p := p) hS.unit
      simp only [Zinv]
      field_simp

/-- **`PhysWindow` from the slot system alone.**  If the packet's chart rows are the generated
ones, `PhysWindow` holds for the window "a slot system with `CellOK` exists", with the weights
`wOf` (number of positions of each group) and the central count `c`. -/
theorem physWindow_of_chartOf (P : Parameters) (pk : Packet) (cc : ChartCell)
    (hch : ChartsOf pk cc) (c emax : ℕ → ℕ → ℕ) :
    PhysWindow P pk (ChartWin P pk cc c emax) c (fun g N p => wOf P pk cc emax g N p) := by
  intro N p hN hp hp2 hH hApp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := hApp.1 hp
  exact ⟨S, hS.hD, ⟨identOfCell hp.pos hch hS⟩⟩

end
end CatalanMeasure.GenD.Uniform.W.Charts
