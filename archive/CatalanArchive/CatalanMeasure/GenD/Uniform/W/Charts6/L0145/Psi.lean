module
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0145.Jets
public import CatalanMeasure.GenD.Uniform.W.Charts5.Prof146
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# L0145: the psi-row identity for the stored raw rows

For `J = 1..11`, `S ∈ {13, 12}` the stored rows satisfy, on the 31 slot coordinates,
`r_c · Zmom = -r_31 · rowInt pd146 Zmom J S (ι c)`, with `r_32 = ε r_31` and `rowInt = 0` on the graph coordinates; hence for `p ∤ Zmom`
and a vector in the kernel of the row, `ψ(J,S)(ι y) = y_31 + ε y_32`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6.L0145
open Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts5
open CatalanMeasure.GenD.Uniform.W.Prof (emb chartMap)
noncomputable section

/-- The moment denominator used for the rows. -/
abbrev ZM : ℕ := Zmom 16 12

def rowOK (g i J : ℕ) (S : ℤ) (ε : ℤ) : Bool :=
  let r := (oRows g).getD i []
  decide (i < (oRows g).length) && decide (r.getD 31 0 < 0) &&
    decide ((30030 ^ 40 : ℤ) % (r.getD 31 0) = 0) &&
    decide (r.getD 32 0 = ε * r.getD 31 0) &&
    (List.range 31).all (fun c => decide (r.getD c 0 * (ZM : ℤ) = -(r.getD 31 0) * rowInt pd146 ZM J S (iotaN c))) &&
    decide (rowInt pd146 ZM J S 42 = 0) && decide (rowInt pd146 ZM J S 43 = 0)

/-- Row index of the `raw[J,1].degree` row in the `∞` group `g` (`g = 6..10`). -/
def ridx (g J : ℕ) : ℕ :=
  if J = 11 then (match g with | 6 => 23 | 7 => 12 | 8 => 2 | _ => 1)
  else (match g with | 6 => J + 23 | 7 => J + 12 | 8 => J + 2 | 9 => J + 1 | _ => J - 1)

theorem ZM_dvd : ZM ∣ 30030 ^ 40 := by decide +kernel

theorem not_dvd_ZM {p : ℕ} [Fact p.Prime] (hp : 13 < p) : ¬ p ∣ ZM := by
  intro h
  have h1 : p ∣ 30030 ^ 40 := h.trans ZM_dvd
  have hpn := (Fact.out : p.Prime)
  have h2 : p ∣ 30030 := hpn.dvd_of_dvd_pow h1
  have e : (30030 : ℕ) = 2 * 3 * 5 * 7 * 11 * 13 := by norm_num
  rw [e] at h2
  rcases (Nat.Prime.dvd_mul hpn).mp h2 with h | h
  · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
          · have := Nat.le_of_dvd (by norm_num) h; omega
          · have := Nat.le_of_dvd (by norm_num) h; omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

set_option maxRecDepth 100000 in
theorem rows_zero : ∀ J : Fin 10, rowOK 1 J.val (J.val + 2) 13 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rows_graph : rowOK 1 10 1 12 1 = true ∧ rowOK 2 0 1 12 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem rows_inf : ∀ g : Fin 5, ∀ J : Fin 10,
    (J.val = 9 → g.val ≤ 3) → rowOK (g.val + 6) (ridx (g.val + 6) (J.val + 2)) (J.val + 2) 12 0 = true := by
  decide +kernel

end
end CatalanMeasure.GenD.Uniform.W.Charts6.L0145
