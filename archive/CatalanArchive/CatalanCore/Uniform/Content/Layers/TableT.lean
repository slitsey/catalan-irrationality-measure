module
public import CatalanCore.Uniform.Content.Layers.SawCount
@[expose] public section

/-!
# Table T for the thirds frames, every `2m ≤ r`

For a modulus `q` with first singular index `k` (`lev q c = 0 ↔ c < k`, `k ≤ q`) the
assignment value of the one-level weight is bounded by the integer closed form `tableT q r m k`:

* `q < 2m` (sawtooth, odd `q`):          `2(r+m) - q‖m/q‖`;
* `2m < q ≤ r` (D2, D3):                 `min (2(r-U)+2m+min(U,2m)) (2r+m)`, `U = (k+q-r)_+`;
* `r < q` (D4/D5, and D6 when `q ≥ N`, `k ≥ r`): `2(r-k)+2m+(2m-(q-r))`, resp. `2m-(k-r)`.

No relation between `m` and `r` beyond `2m ≤ r` is used (in particular no `8m ≤ r`).  The cases are
the existing certificates D2/D3/D45/D6 (`Arith/Hybrid/Values`) and the new sawtooth certificate.
-/

namespace CatalanCore.Uniform.Content.Layers
open CatalanCore.Arith.Hybrid

/-- The closed form of table T (integer form `δ_A + E`). -/
def tableT (q r m k : ℕ) : ℕ :=
  if q < 2 * m then 2 * (r + m) - sawM q m
  else if q ≤ r then
    min (2 * (r - (k + q - r)) + 2 * m + min (k + q - r) (2 * m)) (2 * r + m)
  else if r + 2 * m ≤ q ∧ r ≤ k then 2 * m - (k - r)
  else 2 * (r - k) + 2 * m + (2 * m - (q - r))

/-- **Table T for every `2m ≤ r`.**  For odd `q`, `k ≤ q` and a level function whose zero set is
`{c < k}`, `tropVal (HW lev q r m) ≤ tableT q r m k`. -/
theorem tableT_bound (lev : ℕ → ℕ → ℕ) {q r m k : ℕ} (hq : q % 2 = 1) (hmr : 2 * m ≤ r)
    (hk : k ≤ q) (hlow : ∀ c, lev q c = 0 ↔ c < k) :
    tropVal (HW lev q r m) ≤ tableT q r m k := by
  have hq1 : 1 ≤ q := by omega
  unfold tableT
  by_cases h1 : q < 2 * m
  · rw [if_pos h1]
    have := trop_saw_closed (r := r) (m := m) lev hq
    omega
  rw [if_neg h1]
  by_cases h2 : q ≤ r
  · rw [if_pos h2]
    have hm : 2 * m < q := by omega
    have hh : ∀ c, q ≤ c → 0 < lev q c := by
      intro c hc
      by_contra hn
      have := (hlow c).mp (by omega)
      omega
    have h3 := val_D3 (lev := lev) q r m hq1 hh hm h2
    obtain ⟨u, L, hu1, hu2, hL1, hL2, hv⟩ :=
      val_D2 (lev := lev) q r m k hq1 hh hm h2 (by omega) hlow
    apply le_min
    · omega
    · exact h3
  · rw [if_neg h2]
    have hrq : r < q := by omega
    by_cases h4 : r + 2 * m ≤ q ∧ r ≤ k
    · rw [if_pos h4]
      exact val_D6 (lev := lev) q r m k h4.1 h4.2 hlow
    · rw [if_neg h4]
      exact val_D45 (lev := lev) q r m k hrq hmr hlow

/-- The same at `α = 3/20`: `20 m ≤ 3 r` implies `2 m ≤ r`. -/
theorem tableT_bound_alpha (lev : ℕ → ℕ → ℕ) {q r m k : ℕ} (hq : q % 2 = 1)
    (hα : 20 * m ≤ 3 * r) (hk : k ≤ q) (hlow : ∀ c, lev q c = 0 ↔ c < k) :
    tropVal (HW lev q r m) ≤ tableT q r m k :=
  tableT_bound lev hq (by omega) hk hlow

end CatalanCore.Uniform.Content.Layers
