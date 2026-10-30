import CatalanCore.Uniform.Bank.ThirdsContent.TwoTerm
import CatalanCore.Uniform.Bank.ThirdsContent.CovDefs
import CatalanCore.Uniform.Content.Wire.M3D
import CatalanCore.Uniform.Content.Wire.LP
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # M3D windows for the thirds pipeline frames (lane B, B4b)

`nocut_window3`: a segment `[a, b)` is cut-free for the singular classes `p ∣ t`, `p ∣ 3t - o` and
the border shift `t ≡ r (mod p)` as soon as it lies strictly between two consecutive multiples in
each class (the `3t - o` class may skip multiples of `p` that give no integer `t`).
`m3dValid_of_window` packages this with the pole data of a two-term frame (`twoTermPoleData`) into
the validity window of `m3dLayer`. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Uniform CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Thirds

theorem nocut_window3 (p r a b o : ℕ) (hp : 0 < p) (n0 n1 K1 n3 : ℕ)
    (h0 : n0 * p ≤ a ∧ b ≤ (n0 + 1) * p)
    (h1 : n1 * p + o ≤ 3 * a ∧ 3 * b ≤ (n1 + K1 + 1) * p + o)
    (m1 : ∀ i : ℕ, 1 ≤ i → i ≤ K1 → ((n1 + i) * p + o) % 3 ≠ 0)
    (h3 : r + n3 * p ≤ a ∧ b ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r (ttSing p 3 o)) (min (x : ℤ) y) (max (x : ℤ) y) := by
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
  have c0a : ((n0 : ℤ)) * p ≤ a := by exact_mod_cast h0a
  have c0b : (b : ℤ) ≤ ((n0 : ℤ) + 1) * p := by exact_mod_cast h0b
  have c1a : ((n1 : ℤ)) * p + o ≤ 3 * a := by exact_mod_cast h1a
  have c1b : 3 * (b : ℤ) ≤ ((n1 : ℤ) + K1 + 1) * p + o := by exact_mod_cast h1b
  have c3a : (r : ℤ) + ((n3 : ℤ)) * p ≤ a := by exact_mod_cast h3a
  have c3b : (b : ℤ) ≤ r + ((n3 : ℤ) + 1) * p := by exact_mod_cast h3b
  rcases hcut with (⟨j, hj⟩ | ⟨j, hj⟩) | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact bet n0 j (by linarith) (by linarith)
  · -- 3t - o = p j
    push_cast at hj
    have l1 : (n1 : ℤ) * p < j * p := by linarith
    have l2 : j * p < ((n1 : ℤ) + K1 + 1) * p := by linarith
    have u : (n1 : ℤ) < j := lt_of_mul_lt_mul_right l1 hpz.le
    have v : j < (n1 : ℤ) + K1 + 1 := lt_of_mul_lt_mul_right l2 hpz.le
    obtain ⟨i, hi⟩ : ∃ i : ℕ, j = (n1 : ℤ) + i := ⟨(j - n1).toNat, by omega⟩
    have hz := m1 i (by omega) (by omega)
    have hz2 : (((n1 + i) * p + o : ℕ) : ℤ) = 3 * t := by
      push_cast; rw [← hi]; linarith
    generalize (n1 + i) * p = X at hz hz2
    omega
  · exact bet n0 j (by linarith) (by linarith)
  · exact bet n3 j (by linarith) (by linarith)


open CatalanFrames.Thirds in
/-- The pole data of a thirds frame (norm 9) at a prime `p ≥ 5` with `3 N < p²`. -/
noncomputable def thirdsPoleData {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (p N : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hN : 3 * N < p * p) : Periodic.PoleData Fr p N :=
  twoTermPoleData (ThirdsData.twoTerm T) (N := N) (by nlinarith)
    (fun t ht htN => by
      intro hd
      have h1 := Nat.le_of_dvd (by have := (ThirdsData.twoTerm T).pos ht; omega) hd
      have h2 : 3 * t - e ≤ 3 * t := Nat.sub_le _ _
      nlinarith [pow_two p])
    (by rw [T.norm_eq]; simpa using (Good.ofNat (ℓ := p) 9).mem)
    (by
      rw [T.norm_eq]
      have h9 : (9 : ZMod p) ≠ 0 := by
        have : ((9 : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
          have h33 : p ∣ 3 * 3 := by simpa using hd
          rcases (Fact.out : p.Prime).dvd_mul.mp h33 with h | h <;>
            exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        simpa using this
      simpa [red] using h9)

open CatalanFrames.Thirds in
theorem m3dValid_thirds {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (a b : ℕ → ℕ → ℕ) (r p : ℕ)
    (hr : r % 2 = 0) (hp5 : 5 ≤ p) (hN : 3 * (r + 2 * G310.borderSize r) < p * p)
    (hra : r ≤ a r p) (hab : a r p ≤ b r p) (hb1 : b r p ≤ r + 2 * G310.borderSize r)
    (hb2 : b r p ≤ r + p)
    (hj : max (a r p) (r + 2 * G310.borderSize r - p) ≤ b r p)
    (hcut : ∀ x y : ℕ, a r p ≤ x → x < b r p → a r p ≤ y → y < b r p →
      NoCut (Cut p r (ttSing p 3 e)) (min (x : ℤ) y) (max (x : ℤ) y)) :
    m3dValid G310 Fr a b r p := by
  have hk : (G310.geometry r).k = G310.borderSize r :=
    CatalanCore.Uniform.Content.BankShared.geometry_k_eq_borderSize G310 r
  refine ⟨altGeom_hybShape (3 / 10) c310_pos hr, fun [hpf : Fact p.Prime] => ?_⟩
  rw [hk]
  exact ⟨thirdsPoleData T p _ hp5 hN, by nlinarith, hra, hab, hb1, hb2, hj, hcut⟩

theorem m3_gle {Fr : Frame} {depth : ℕ} (a b : ℕ → ℕ → ℕ) (i : (FamE Fr depth).ι)
    (hi : (FamE Fr depth).Adm i) (p : ℕ) [Fact p.Prime] (hv : m3dValid G310 Fr a b i.1 p) :
    GLE p (2 * i.1 + (2 * G310.borderSize i.1 -
      (b i.1 p - max (a i.1 p) (i.1 + 2 * G310.borderSize i.1 - p)))) ((FamE Fr depth).Q i) := by
  have h := (m3dLayer G310 Fr depth a b).gle i hi.1 p hv
  have hk : (G310.geometry i.1).k = G310.borderSize i.1 :=
    CatalanCore.Uniform.Content.BankShared.geometry_k_eq_borderSize G310 i.1
  simp only [m3dLayer, zero_mul, add_zero, m3dBase, hk] at h
  exact h

end CatalanCore.Uniform.Bank.ThirdsContent
