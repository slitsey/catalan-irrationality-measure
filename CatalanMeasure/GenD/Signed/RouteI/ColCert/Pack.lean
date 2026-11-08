module

public import Mathlib.Tactic

@[expose] public section

/-!
# Kronecker pack/unpack uniqueness (G31)

kcost: no computation here.  `pack_inj`: balanced base-2^W digits are unique; `unpack_spec`: the digits of `unpack` repack to the number.
-/

namespace PackKr
def pack (W : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: t => a + 2 ^ W * pack W t

def unpack (W : ℕ) : ℕ → ℤ → List ℤ × ℤ
  | 0, x => ([], x)
  | n + 1, x =>
    let d := (x + 2 ^ (W - 1)) % 2 ^ W - 2 ^ (W - 1)
    let r := unpack W n ((x - d) / 2 ^ W)
    (d :: r.1, r.2)

/-- digits are in `[-2^(W-1), 2^(W-1))` -/
def InRange (W : ℕ) (a : ℤ) : Prop := -(2 ^ (W - 1) : ℤ) ≤ a ∧ a < 2 ^ (W - 1)

theorem unpack_spec (W : ℕ) (hW : 1 ≤ W) : ∀ (n : ℕ) (x : ℤ),
    x = pack W (unpack W n x).1 + 2 ^ (W * n) * (unpack W n x).2 ∧
    ∀ a ∈ (unpack W n x).1, InRange W a
  | 0, x => by simp [unpack, pack]
  | n + 1, x => by
    obtain ⟨h1, h2⟩ := unpack_spec W hW n ((x - ((x + 2 ^ (W - 1)) % 2 ^ W - 2 ^ (W - 1))) / 2 ^ W)
    have hp : (0 : ℤ) < 2 ^ W := by positivity
    have h2W : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      rw [← pow_succ']; congr 1; omega
    set d := (x + 2 ^ (W - 1)) % 2 ^ W - 2 ^ (W - 1) with hd
    have hdiv : (2 : ℤ) ^ W ∣ x - d := by
      rw [hd]
      have := Int.emod_emod_of_dvd (x + 2 ^ (W - 1)) (dvd_refl ((2:ℤ) ^ W))
      have h3 : (2:ℤ) ^ W ∣ (x + 2 ^ (W - 1)) - (x + 2 ^ (W - 1)) % 2 ^ W :=
        ⟨(x + 2 ^ (W - 1)) / 2 ^ W, by rw [Int.emod_def]; ring⟩
      have : x - ((x + 2 ^ (W - 1)) % 2 ^ W - 2 ^ (W - 1)) = (x + 2 ^ (W - 1)) - (x + 2 ^ (W - 1)) % 2 ^ W := by ring
      rw [this]; exact h3
    refine ⟨?_, ?_⟩
    · simp only [unpack, pack]
      have e : x - d = 2 ^ W * ((x - d) / 2 ^ W) := (Int.mul_ediv_cancel' hdiv).symm
      have : (2 : ℤ) ^ (W * (n + 1)) = 2 ^ W * 2 ^ (W * n) := by rw [mul_add, mul_one, pow_add]; ring
      rw [this]
      calc x = d + (x - d) := by ring
        _ = d + 2 ^ W * ((x - d) / 2 ^ W) := by rw [← e]
        _ = _ := by
          conv_lhs => rw [h1]
          ring
    · intro a ha
      simp only [unpack, List.mem_cons] at ha
      rcases ha with rfl | ha
      · have := Int.emod_nonneg (x + 2 ^ (W - 1)) hp.ne'
        have := Int.emod_lt_of_pos (x + 2 ^ (W - 1)) hp
        constructor <;> omega
      · exact h2 a ha

theorem pack_inj (W : ℕ) (hW1 : 1 ≤ W) : ∀ (l m : List ℤ), (∀ a ∈ l, InRange W a) → (∀ a ∈ m, InRange W a) →
    l.length = m.length → pack W l = pack W m → l = m
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | a :: t, b :: r, hl, hm, hlen, hp => by
    have ha := hl a (by simp)
    have hb := hm b (by simp)
    simp only [pack] at hp
    have hW : (2 : ℤ) ^ W ∣ a - b := ⟨pack W r - pack W t, by linarith⟩
    have h2W : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hab : a = b := by
      have : |a - b| < 2 ^ W := by
        rw [abs_lt]; unfold InRange at ha hb; constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hW this
      omega
    subst hab
    have : pack W t = pack W r := by
      have hp' : (2 : ℤ) ^ W * pack W t = 2 ^ W * pack W r := by linarith
      exact mul_left_cancel₀ (by positivity) hp'
    have := pack_inj W hW1 t r (fun x hx => hl x (by simp [hx])) (fun x hx => hm x (by simp [hx]))
      (by simpa using hlen) this
    rw [this]
end PackKr
