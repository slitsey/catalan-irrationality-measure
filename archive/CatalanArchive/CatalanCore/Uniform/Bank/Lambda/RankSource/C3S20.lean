import CatalanCore.Uniform.Bank.Lambda.DigitShape
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankSource

def C3S20_run0_Rset : Finset ℕ := {0}

theorem C3S20_run0_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C3S20_run0_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C3S20_run0_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C3S20_run0_Rset] at h <;> omega
    interval_cases d <;> norm_num [rowDigit, C3S20_run0_Rset] at * <;> omega

def C3S20_run0_Cset : Finset ℕ := {0}

theorem C3S20_run0_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C3S20_run0_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C3S20_run0_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C3S20_run0_Cset] at h <;> omega
    interval_cases d <;> norm_num [colDigit, C3S20_run0_Cset] at * <;> omega

theorem C3S20_run0_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 3 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C3S20_run1_Rset : Finset ℕ := {0}

theorem C3S20_run1_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C3S20_run1_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C3S20_run1_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C3S20_run1_Rset] at h <;> omega
    interval_cases d <;> norm_num [rowDigit, C3S20_run1_Rset] at * <;> omega

def C3S20_run1_Cset : Finset ℕ := {0}

theorem C3S20_run1_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C3S20_run1_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C3S20_run1_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C3S20_run1_Cset] at h <;> omega
    interval_cases d <;> norm_num [colDigit, C3S20_run1_Cset] at * <;> omega

theorem C3S20_run1_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 3 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C3S20_run2_Rset : Finset ℕ := {0}

theorem C3S20_run2_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C3S20_run2_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C3S20_run2_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C3S20_run2_Rset] at h <;> omega
    interval_cases d <;> norm_num [rowDigit, C3S20_run2_Rset] at * <;> omega

def C3S20_run2_Cset : Finset ℕ := ∅

theorem C3S20_run2_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C3S20_run2_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C3S20_run2_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C3S20_run2_Cset] at h <;> omega
    interval_cases d <;> norm_num [colDigit, C3S20_run2_Cset] at * <;> omega

theorem C3S20_run2_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 3 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C3S20_run3_Rset : Finset ℕ := ∅

theorem C3S20_run3_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C3S20_run3_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C3S20_run3_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C3S20_run3_Rset] at h <;> omega
    interval_cases d <;> norm_num [rowDigit, C3S20_run3_Rset] at * <;> omega

def C3S20_run3_Cset : Finset ℕ := {0}

theorem C3S20_run3_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C3S20_run3_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C3S20_run3_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C3S20_run3_Cset] at h <;> omega
    interval_cases d <;> norm_num [colDigit, C3S20_run3_Cset] at * <;> omega

theorem C3S20_run3_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 3 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega
end CatalanCore.Uniform.Bank.Lambda.RankSource
