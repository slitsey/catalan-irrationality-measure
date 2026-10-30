import CatalanCore.Uniform.Content.Smith.TwoTerm
import CatalanCore.Uniform.Content.Wire.M3D
set_option Elab.async false
namespace CatalanCore.Uniform.Content.Wire
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.ChainClasses
open CatalanCore.Uniform.Content.Smith

/-- Three residue gaps give a cut-free window; integer indices include the gap before k. -/
theorem nocut_twoTerm_window (p q o r a b k : ℕ) (hp : 0 < p)
    (hk : (p : ℤ) ∣ (q : ℤ) * k - o) (hcop : IsCoprime (p : ℤ) (q : ℤ))
    (n0 n1 n3 : ℤ)
    (h0 : n0 * p ≤ (a : ℤ) ∧ (b : ℤ) ≤ (n0 + 1) * p)
    (h1 : n1 * p + k ≤ (a : ℤ) ∧ (b : ℤ) ≤ (n1 + 1) * p + k)
    (h3 : (r : ℤ) + n3 * p ≤ (a : ℤ) ∧ (b : ℤ) ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r (ttSing p q o)) (min (x : ℤ) y) (max (x : ℤ) y) := by
  intro x y hax hxb hay hyb t hat htb hcut
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have ha : (a : ℤ) < t := by
    have : (a : ℤ) ≤ min (x : ℤ) y := le_min (by exact_mod_cast hax) (by exact_mod_cast hay)
    omega
  have hb : t < b := by
    have hx : (x : ℤ) < b := by exact_mod_cast hxb
    have hy : (y : ℤ) < b := by exact_mod_cast hyb
    have : max (x : ℤ) y ≤ (b : ℤ) - 1 := max_le (by omega) (by omega)
    omega
  have bet : ∀ (n j : ℤ), n * p < j * p → j * p < (n + 1) * p → False := by
    intro n j h1 h2
    have u : n < j := lt_of_mul_lt_mul_right h1 hpz.le
    have v : j < n + 1 := lt_of_mul_lt_mul_right h2 hpz.le
    omega
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h3a, h3b⟩ := h3
  have cls : (p : ℤ) ∣ (q : ℤ) * t - o → ∃ j : ℤ, t = k + j * p := by
    intro hd
    have hq : (p : ℤ) ∣ (q : ℤ) * (t - k) := by
      have h := dvd_sub hd hk
      have e : (q : ℤ) * t - o - ((q : ℤ) * k - o) = (q : ℤ) * (t - k) := by ring
      rwa [e] at h
    obtain ⟨j, hj⟩ := hcop.dvd_of_dvd_mul_left hq
    exact ⟨j, by linarith⟩
  rcases hcut with (hj | hj) | ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨j, hj⟩ := hj
    exact bet n0 j (by linarith) (by linarith)
  · obtain ⟨j, hj⟩ := cls hj
    exact bet n1 j (by linarith) (by linarith)
  · exact bet n0 j (by linarith) (by linarith)
  · exact bet n3 j (by linarith) (by linarith)

#print axioms nocut_twoTerm_window
end CatalanCore.Uniform.Content.Wire
