import CatalanCore.Uniform.Bank.FifthsContent.M3
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The general M3D bound for the fifths family (lane B, B5c)

`nocut_window5k`: a segment `[a, b)` is cut-free for the three residue families `t ≡ 0`, `t ≡ k`
(the pole class `5 t ≡ o`) and `t ≡ r (mod p)` when it lies inside a gap of each.

`m3_general`: for every choice of gap indices `n0, n1, n3`, a member at a prime `p ≥ 7` with
`5 N < p²` is cleared by `2r + 2m - (Bu - a)` (`0` truncated), where `[a, Bu)` is the intersection of
the three gaps with the window `[max(r, N - p), min(N, r + p))`.  Every M3D piece of the profile is
an instance (the indices are numerals), so each piece cover is linear arithmetic. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Uniform CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Fifths

theorem nocut_window5k (p r a b o k : ℕ) (hp : 0 < p) (hk : (p : ℤ) ∣ 5 * (k : ℤ) - o)
    (hcop : IsCoprime (p : ℤ) 5) (n0 n1 n3 : ℕ)
    (h0 : n0 * p ≤ a ∧ b ≤ (n0 + 1) * p)
    (h1 : n1 * p + k ≤ a ∧ b ≤ (n1 + 1) * p + k)
    (h3 : r + n3 * p ≤ a ∧ b ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r (ttSing p 5 o)) (min (x : ℤ) y) (max (x : ℤ) y) := by
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
  have c1a : ((n1 : ℤ)) * p + k ≤ a := by exact_mod_cast h1a
  have c1b : (b : ℤ) ≤ ((n1 : ℤ) + 1) * p + k := by exact_mod_cast h1b
  have c3a : (r : ℤ) + ((n3 : ℤ)) * p ≤ a := by exact_mod_cast h3a
  have c3b : (b : ℤ) ≤ r + ((n3 : ℤ) + 1) * p := by exact_mod_cast h3b
  -- the class `p ∣ 5 t - o` is the class `t ≡ k (mod p)`
  have cls : (p : ℤ) ∣ 5 * t - o → ∃ j : ℤ, t = k + j * p := by
    intro hd
    have h5 : (p : ℤ) ∣ 5 * (t - k) := by
      have := dvd_sub hd hk
      have e : 5 * t - (o : ℤ) - (5 * (k : ℤ) - o) = 5 * (t - k) := by ring
      rwa [e] at this
    obtain ⟨j, hj⟩ := hcop.dvd_of_dvd_mul_left h5
    exact ⟨j, by linarith⟩
  rcases hcut with (hj | hj) | ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨j, hj⟩ := hj
    exact bet n0 j (by linarith) (by linarith)
  · obtain ⟨j, hj⟩ := cls hj
    have l1 : (n1 : ℤ) * p < j * p := by linarith
    have l2 : j * p < ((n1 : ℤ) + 1) * p := by linarith
    exact bet n1 j l1 l2
  · exact bet n0 j (by linarith) (by linarith)
  · exact bet n3 j (by linarith) (by linarith)

theorem m3_general {Fr : Frame} {o : ℕ} (T : TwoTermData Fr 5 o) (hnorm : Fr.norm = 25)
    (depth : ℕ) (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι)
    (hi : (AltE (2 / 9) two_ninths_pos Fr depth).Adm i) (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hsq : 5 * (i.1 + 2 * F5.borderSize i.1) < p * p) (hmp : F5.borderSize i.1 ≤ p)
    (k j : ℕ) (hk : 5 * k = o + j * p) (n0 n1 n3 : ℕ) :
    ∃ n : ℕ, GLE p n ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) ∧
      (n : ℤ) ≤ ((2 * i.1 + 2 * F5.borderSize i.1 : ℕ) : ℤ) -
        ((min (min ((n0 + 1) * p) ((n1 + 1) * p + k))
              (min (i.1 + (n3 + 1) * p) (min (i.1 + 2 * F5.borderSize i.1) (i.1 + p))) -
          max (max (n0 * p) (n1 * p + k))
            (max (i.1 + n3 * p) (max i.1 (i.1 + 2 * F5.borderSize i.1 - p))) : ℕ) : ℤ) := by
  have hr : i.1 % 2 = 0 := hi.2
  have hcop : IsCoprime (p : ℤ) 5 := by
    have hpp : p.Prime := Fact.out
    have : Nat.Coprime p 5 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hpp).1 hd
      omega
    exact Nat.isCoprime_iff_coprime.2 this
  have hkd : (p : ℤ) ∣ 5 * (k : ℤ) - o := ⟨j, by
    have : (5 * k : ℤ) = o + j * p := by exact_mod_cast hk
    linarith⟩
  set r := i.1 with hr_def
  set m := F5.borderSize i.1 with hm_def
  set a : ℕ := max (max (n0 * p) (n1 * p + k)) (max (r + n3 * p) (max r (r + 2 * m - p))) with ha
  set Bu : ℕ := min (min ((n0 + 1) * p) ((n1 + 1) * p + k))
    (min (r + (n3 + 1) * p) (min (r + 2 * m) (r + p))) with hBu
  have F1 : r ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have F2 : r + 2 * m - p ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have F3 : n0 * p ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have F4 : n1 * p + k ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have F5' : r + n3 * p ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have G1 : Bu ≤ (n0 + 1) * p := by rw [hBu]; simp only [min_le_iff]; omega
  have G2 : Bu ≤ (n1 + 1) * p + k := by rw [hBu]; simp only [min_le_iff]; omega
  have G3 : Bu ≤ r + (n3 + 1) * p := by rw [hBu]; simp only [min_le_iff]; omega
  have G4 : Bu ≤ r + 2 * m := by rw [hBu]; simp only [min_le_iff]; omega
  have G5 : Bu ≤ r + p := by rw [hBu]; simp only [min_le_iff]; omega
  clear_value a Bu
  clear ha hBu
  have hp0 : 0 < p := by omega
  by_cases hne : a ≤ Bu
  · have hv : m3dValid F5 Fr (fun _ _ => a) (fun _ _ => Bu) r p := by
      refine m3dValid_fifths T hnorm _ _ r p hr hp7 hsq ?_ ?_ ?_ ?_ ?_ ?_
      · exact F1
      · exact hne
      · exact G4
      · exact G5
      · show max a (r + 2 * m - p) ≤ Bu
        exact max_le hne (by omega)
      · exact nocut_window5k p r a Bu o k hp0 hkd hcop n0 n1 n3 ⟨F3, G1⟩ ⟨F4, G2⟩ ⟨F5', G3⟩
    have hg := m3_gle5 (Fr := Fr) (depth := depth) (fun _ _ => a) (fun _ _ => Bu) i hi p hv
    rw [← hm_def, ← hr_def] at hg
    refine ⟨_, hg, ?_⟩
    have hmx : max a (r + 2 * m - p) = a := max_eq_left F2
    show _ ≤ _
    simp only [hmx]
    omega
  · have hv : m3dValid F5 Fr (fun _ _ => max r (r + 2 * m - p)) (fun _ _ => max r (r + 2 * m - p))
        r p := by
      refine m3dValid_fifths T hnorm _ _ r p hr hp7 hsq ?_ ?_ ?_ ?_ ?_ ?_
      · show r ≤ max r (r + 2 * m - p)
        exact le_max_left _ _
      · exact le_rfl
      · show max r (r + 2 * m - p) ≤ r + 2 * m
        exact max_le (by omega) (by omega)
      · show max r (r + 2 * m - p) ≤ r + p
        exact max_le (by omega) (by omega)
      · show max (max r (r + 2 * m - p)) (r + 2 * m - p) ≤ max r (r + 2 * m - p)
        exact max_le le_rfl (le_max_right _ _)
      · intro x y hax hxb hay hyb
        exfalso
        omega
    have hg := m3_gle5 (Fr := Fr) (depth := depth) (fun _ _ => max r (r + 2 * m - p))
      (fun _ _ => max r (r + 2 * m - p)) i hi p hv
    rw [← hm_def, ← hr_def] at hg
    refine ⟨_, hg, ?_⟩
    have hmx : max (max r (r + 2 * m - p)) (r + 2 * m - p) = max r (r + 2 * m - p) :=
      max_eq_left (le_max_right _ _)
    show _ ≤ _
    simp only [hmx]
    omega

#print axioms m3_general
end CatalanCore.Uniform.Bank.FifthsContent
