"""Assembly module (Thirds.lean) of the thirds UF layer."""

OPEN = """open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE
  CatalanCore.Uniform.Content.UFFamily2
"""


def thirds_lean(n, mods):
    imp = ''.join("public import CatalanCore.Uniform.Content.UFFamily3.%s\n" % m for m in mods)
    rows = lambda name, dflt: "\n".join("  | %d => F%d.%s" % (i, i, name) for i in range(n)) + "\n  | _ => fun _ _ => " + dflt + "\n"
    t = []
    t.append("module\n\n" + imp + "\n@[expose] public section\n")
    t.append("/-!\n# The thirds UF debit layer (lane H, H12)\n\n`thirdsUFLayer`: the union of the %d window families (first match `idx`),\nwith the explicit price `baseOf (idx r p) r p = base3 m r p t0 tv`.  Valid on the thirds band\n`3 r < 10 p ≤ 39 r`, `p ≥ 60`, `r` even, inside the union of the family regions.\n-/\n" % n)
    t.append(OPEN)
    t.append("namespace CatalanCore.Uniform.Content.UFFamily3\n")
    t.append("def RegOf : ℕ → ℕ → ℕ → Prop\n" + rows("Reg", "False"))
    t.append("def T0Of : ℕ → ℕ → ℕ → ℕ\n" + rows("T0", "0"))
    t.append("def TVOf : ℕ → ℕ → ℕ → ℕ\n" + rows("TV", "0"))
    t.append("def baseOf (i r p : ℕ) : ℕ := base3 ((3 * r + 9) / 20) r p (T0Of i r p) (TVOf i r p)\n")
    t.append("variable {Fr : Frame}\n")
    t.append("""noncomputable def cellOf (T : TwoTermData Fr 3 2) (i : ℕ) {r p : ℕ} [Fact p.Prime] (hn : Fr.norm = 1)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : RegOf i r p → Cell3 cT cT_pos Fr 3 2 T r p :=
  match i with
""" + chr(10).join("  | %d => fun h => F%d.cell T h hn hnorm hnorm0" % (i, i) for i in range(n)) + """
  | n + %d => fun h => False.elim (by simp [RegOf] at h)
""" % n)
    t.append("""theorem cellOf_bound (T : TwoTermData Fr 3 2) (i : ℕ) {r p : ℕ} [Fact p.Prime] (hn : Fr.norm = 1)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ h : RegOf i r p, (cellOf T i hn hnorm hnorm0 h).bound = baseOf i r p := by
  match i with
""" + chr(10).join("  | %d => exact fun h => F%d.cell_bound T h hn hnorm hnorm0" % (i, i) for i in range(n)) + """
  | n + %d => exact fun h => False.elim (by simp [RegOf] at h)
""" % n)
    t.append("""open Classical in
/-- First family whose region contains `(r, p)`. -/
noncomputable def idx (r p : ℕ) : ℕ := if h : ∃ i, RegOf i r p then Nat.find h else 0

theorem idx_spec {r p : ℕ} (h : ∃ i, RegOf i r p) : RegOf (idx r p) r p := by
  classical
  unfold idx
  rw [dif_pos h]
  exact Nat.find_spec h

/-- Validity of the thirds UF layer. -/
def ValidT (Fr : Frame) (r p : ℕ) : Prop :=
  (∃ i, RegOf i r p) ∧ Fr.norm = 1 ∧ ∀ [Fact p.Prime], Fr.norm ∈ S p ∧ red p Fr.norm ≠ 0

/-- **The thirds UF debit layer.** -/
noncomputable def thirdsUFLayer (T : TwoTermData Fr 3 2) {depth : ℕ} :
    DebitLayer (altGeom cT cT_pos) Fr depth :=
  layer3 (T := T) (ValidT Fr) (fun r p => baseOf (idx r p) r p)
    (fun r p _ h => cellOf T (idx r p) h.2.1 h.2.2.1 h.2.2.2 (idx_spec h.1))
    (fun r p _ h => (cellOf_bound T (idx r p) h.2.1 h.2.2.1 h.2.2.2 (idx_spec h.1)).le)

theorem thirdsUFLayer_valid (T : TwoTermData Fr 3 2) {depth : ℕ} :
    (thirdsUFLayer (depth := depth) T).valid = ValidT Fr := rfl

theorem thirdsUFLayer_debit (T : TwoTermData Fr 3 2) {depth : ℕ} :
    (thirdsUFLayer (depth := depth) T).debit = 1 := rfl

theorem thirdsUFLayer_eff (T : TwoTermData Fr 3 2) {depth : ℕ} (r p : ℕ) :
    (thirdsUFLayer (depth := depth) T).eff r p = baseOf (idx r p) r p + depth := by
  have hb : (thirdsUFLayer (depth := depth) T).base = fun r p => baseOf (idx r p) r p := rfl
  have hd : (thirdsUFLayer (depth := depth) T).debit = 1 := rfl
  simp [DebitLayer.eff, hb, hd]

end CatalanCore.Uniform.Content.UFFamily3
""")
    return "\n".join(t)
