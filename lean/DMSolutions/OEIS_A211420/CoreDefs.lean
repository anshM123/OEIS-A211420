import Mathlib

/-!
# OEIS A211420: definitions and the valuation framework

This file contains verbatim copies of `OeisA211420.a` and `OeisA211420.oddDescendingProduct` from
`FormalConjectures/OEIS/211420.lean` (formal-conjectures pull request 6426), and the valuation
framework used for all four conjectures.

For a prime power `q` put `T = ⌊24 n / q⌋`. Since `c ∣ 24` for `c ∈ {8, 4, 3, 2, 1}`,
`⌊c n / q⌋ = ⌊T / (24 / c)⌋`. Hence the `q`-term of Legendre's formula for `a n` is
`phi T = hi T - lo T`, where `hi T = ⌊T/3⌋ + ⌊T/24⌋` and `lo T = ⌊T/6⌋ + ⌊T/8⌋ + ⌊T/12⌋`.
The function `phi` is `24`-periodic, takes the values `0` and `1`, and `lo T ≤ hi T` (Landau).

* `den_dvd_num`: `(4n)! (3n)! (2n)! ∣ (8n)! n!`, so `a n` is an exact quotient.
* `dvd_mul_a`: a prime-by-prime criterion for `t ∣ c * a n`.
* `termwise`: the criterion holds at `p` if every `p ^ i ∣ t` has `p ^ i ∣ c` or `phi = 1`.
* `escape3`, `escape2`: if `⌊24 n / p ^ i⌋ mod 24` is at least `9` (for `p = 3`) or `6`
  (for `p = 2`), then some `j > i` has `phi ⌊24 n / p ^ j⌋ = 1`.
-/

open Finset Nat

namespace A211420Core

/-- $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$. -/
def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

/-- The product $\prod_{i=0}^r (8n - (2i + 1))$ in $\mathbb{Z}$. -/
def oddDescendingProduct (n r : ℕ) : ℤ :=
  ∏ i ∈ Finset.range (r + 1), ((8 * n : ℤ) - (2 * i + 1 : ℤ))

/-- `lo T = ⌊T/6⌋ + ⌊T/8⌋ + ⌊T/12⌋`; with `T = ⌊24 n / q⌋` this is `⌊4n/q⌋ + ⌊3n/q⌋ + ⌊2n/q⌋`. -/
def lo (T : ℕ) : ℕ := T / 6 + T / 8 + T / 12

/-- `hi T = ⌊T/3⌋ + ⌊T/24⌋`; with `T = ⌊24 n / q⌋` this is `⌊8n/q⌋ + ⌊n/q⌋`. -/
def hi (T : ℕ) : ℕ := T / 3 + T / 24

/-- `phi T = hi T - lo T`, the `q`-term of Legendre's formula for `a n`. -/
def phi (T : ℕ) : ℕ := hi T - lo T

theorem lo_le_hi (T : ℕ) : lo T ≤ hi T := by unfold lo hi; omega

theorem hi_eq (T : ℕ) : hi T = lo T + phi T := by unfold phi lo hi; omega

theorem phi_le_one (T : ℕ) : phi T ≤ 1 := by unfold phi lo hi; omega

theorem phi_zero : phi 0 = 0 := by unfold phi lo hi; omega

/-! ### Rescaling the Legendre terms -/

theorem div_scale (d c n q : ℕ) (hd : 0 < d) : d * c * n / q / d = c * n / q := by
  rw [Nat.div_div_eq_div_mul, mul_comm q d, mul_assoc, Nat.mul_div_mul_left (c * n) q hd]

theorem eight_mul_div (n q : ℕ) : 8 * n / q = 24 * n / q / 3 := by
  rw [show 24 * n = 3 * 8 * n by ring, div_scale 3 8 n q (by norm_num)]

theorem one_mul_div' (n q : ℕ) : n / q = 24 * n / q / 24 := by
  rw [show 24 * n = 24 * 1 * n by ring, div_scale 24 1 n q (by norm_num), one_mul]

theorem four_mul_div (n q : ℕ) : 4 * n / q = 24 * n / q / 6 := by
  rw [show 24 * n = 6 * 4 * n by ring, div_scale 6 4 n q (by norm_num)]

theorem three_mul_div (n q : ℕ) : 3 * n / q = 24 * n / q / 8 := by
  rw [show 24 * n = 8 * 3 * n by ring, div_scale 8 3 n q (by norm_num)]

theorem two_mul_div (n q : ℕ) : 2 * n / q = 24 * n / q / 12 := by
  rw [show 24 * n = 12 * 2 * n by ring, div_scale 12 2 n q (by norm_num)]

/-! ### Legendre's formula in terms of `lo` and `hi` -/

theorem fact_eq {p m b : ℕ} (hp : p.Prime) (hb0 : b ≠ 0) (hm : m < p ^ b) :
    (m)!.factorization p = ∑ i ∈ Ico 1 b, m / p ^ i :=
  Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow' hb0 hm)

theorem legendre_hi {n p b : ℕ} (hp : p.Prime) (hb0 : b ≠ 0) (hb : 24 * n < p ^ b) :
    (8 * n)!.factorization p + (n)!.factorization p = ∑ i ∈ Ico 1 b, hi (24 * n / p ^ i) := by
  rw [fact_eq hp hb0 (show 8 * n < p ^ b by omega), fact_eq hp hb0 (show n < p ^ b by omega),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eight_mul_div, one_mul_div' n]
  rfl

theorem legendre_lo {n p b : ℕ} (hp : p.Prime) (hb0 : b ≠ 0) (hb : 24 * n < p ^ b) :
    (4 * n)!.factorization p + (3 * n)!.factorization p + (2 * n)!.factorization p =
      ∑ i ∈ Ico 1 b, lo (24 * n / p ^ i) := by
  rw [fact_eq hp hb0 (show 4 * n < p ^ b by omega), fact_eq hp hb0 (show 3 * n < p ^ b by omega),
    fact_eq hp hb0 (show 2 * n < p ^ b by omega), ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [four_mul_div, three_mul_div, two_mul_div]
  rfl

theorem fact_den_eq {n p : ℕ} :
    ((4 * n)! * (3 * n)! * (2 * n)!).factorization p =
      (4 * n)!.factorization p + (3 * n)!.factorization p + (2 * n)!.factorization p := by
  rw [Nat.factorization_mul (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _))
      (factorial_ne_zero _), Nat.factorization_mul (factorial_ne_zero _) (factorial_ne_zero _)]
  rfl

theorem fact_num_eq {n p : ℕ} :
    ((8 * n)! * (n)!).factorization p = (8 * n)!.factorization p + (n)!.factorization p := by
  rw [Nat.factorization_mul (factorial_ne_zero _) (factorial_ne_zero _)]
  rfl

/-- Landau: `(4n)! (3n)! (2n)! ∣ (8n)! n!`. -/
theorem den_dvd_num (n : ℕ) : (4 * n)! * (3 * n)! * (2 * n)! ∣ (8 * n)! * (n)! := by
  rw [← Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)]
  intro p hp
  have hb : 24 * n < p ^ (24 * n + 1) :=
    lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self hp.one_lt)
  rw [fact_den_eq, fact_num_eq, legendre_lo hp (by omega) hb, legendre_hi hp (by omega) hb]
  exact Finset.sum_le_sum fun i _ => lo_le_hi _

theorem a_mul_den (n : ℕ) : a n * ((4 * n)! * (3 * n)! * (2 * n)!) = (8 * n)! * (n)! :=
  Nat.div_mul_cancel (den_dvd_num n)

/-- The divisibility criterion. `B` is any extra bound the caller wants below `p ^ b`. -/
theorem dvd_mul_a {t c n : ℕ} (B : ℕ) (ht : t ≠ 0) (hc : c ≠ 0)
    (h : ∀ p b : ℕ, p.Prime → 24 * n + t + c + B < p ^ b →
      t.factorization p ≤ c.factorization p + ∑ i ∈ Ico 1 b, phi (24 * n / p ^ i)) :
    t ∣ c * a n := by
  have hD : 0 < (4 * n)! * (3 * n)! * (2 * n)! := by positivity
  apply Nat.dvd_of_mul_dvd_mul_right hD
  rw [mul_assoc c, a_mul_den]
  rw [← Nat.factorization_prime_le_iff_dvd (mul_ne_zero ht hD.ne')
    (mul_ne_zero hc (by positivity))]
  intro p hp
  have hb : 24 * n + t + c + B < p ^ (24 * n + t + c + B + 1) :=
    lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self hp.one_lt)
  have key := h p _ hp hb
  have hb' : 24 * n < p ^ (24 * n + t + c + B + 1) := by omega
  rw [Nat.factorization_mul ht hD.ne', Nat.factorization_mul hc (by positivity)]
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [fact_den_eq, fact_num_eq, legendre_lo hp (by omega) hb', legendre_hi hp (by omega) hb']
  have hsum : ∑ i ∈ Ico 1 (24 * n + t + c + B + 1), hi (24 * n / p ^ i) =
      ∑ i ∈ Ico 1 (24 * n + t + c + B + 1), lo (24 * n / p ^ i) +
        ∑ i ∈ Ico 1 (24 * n + t + c + B + 1), phi (24 * n / p ^ i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hi_eq _
  omega

/-- Termwise form of the criterion at one prime. -/
theorem termwise {t c n p b : ℕ} (hp : p.Prime) (ht : t ≠ 0) (hc : c ≠ 0) (htb : t < p ^ b)
    (hcb : c < p ^ b) (h : ∀ i, 1 ≤ i → p ^ i ∣ t → p ^ i ∣ c ∨ 1 ≤ phi (24 * n / p ^ i)) :
    t.factorization p ≤ c.factorization p + ∑ i ∈ Ico 1 b, phi (24 * n / p ^ i) := by
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (Nat.pos_of_ne_zero ht) htb,
    Nat.factorization_eq_card_pow_dvd_of_lt hp (Nat.pos_of_ne_zero hc) hcb,
    Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  by_cases h1 : p ^ i ∣ t
  · rcases h i hi1 h1 with h2 | h2
    · simp [h1, h2]
    · simp only [h1, if_true]
      split_ifs <;> omega
  · simp only [h1, if_false]
    exact Nat.zero_le _

/-! ### Counting helpers -/

theorem card_le_sum {f : ℕ → ℕ} {l' l u b : ℕ} (hl : l' ≤ l) (hub : u ≤ b)
    (h : ∀ i, l ≤ i → i < u → 1 ≤ f i) : u - l ≤ ∑ i ∈ Ico l' b, f i := by
  calc u - l = ∑ i ∈ Ico l u, 1 := by simp
    _ ≤ ∑ i ∈ Ico l u, f i :=
      Finset.sum_le_sum fun i hi => h i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
    _ ≤ ∑ i ∈ Ico l' b, f i := Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico hl hub)

theorem T_succ (n p j : ℕ) : 24 * n / p ^ (j + 1) = 24 * n / p ^ j / p := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

theorem T_eq_zero {n p b i : ℕ} (hp : 0 < p) (hb : 24 * n < p ^ b) (hi : b ≤ i) :
    24 * n / p ^ i = 0 :=
  Nat.div_eq_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right hp hi))

/-! ### Escape lemmas -/

theorem step3 (T : ℕ) (h0 : phi (T / 3) = 0) (h9 : T / 3 % 24 < 9) : T % 24 < 9 := by
  unfold phi hi lo at h0; omega

theorem step2 (T : ℕ) (h0 : phi (T / 2) = 0) (h6 : T / 2 % 24 < 6) : T % 24 < 6 := by
  unfold phi hi lo at h0; omega

theorem escape_gen (n p b θ : ℕ) (hp : 0 < p) (hb : 24 * n < p ^ b) (hθ : 0 < θ)
    (step : ∀ T : ℕ, phi (T / p) = 0 → T / p % 24 < θ → T % 24 < θ) :
    ∀ k i, i + k = b → θ ≤ 24 * n / p ^ i % 24 →
      1 ≤ ∑ j ∈ Ico (i + 1) b, phi (24 * n / p ^ j) := by
  intro k
  induction k with
  | zero =>
    intro i hik hθi
    rw [T_eq_zero hp hb (by omega)] at hθi
    simp at hθi
    omega
  | succ k ih =>
    intro i hik hθi
    by_cases hφ : phi (24 * n / p ^ (i + 1)) = 0
    · have hθ' : θ ≤ 24 * n / p ^ (i + 1) % 24 := by
        by_contra hcon
        rw [not_le] at hcon
        rw [T_succ] at hφ hcon
        have := step _ hφ hcon
        omega
      have := ih (i + 1) (by omega) hθ'
      calc 1 ≤ ∑ j ∈ Ico (i + 1 + 1) b, phi (24 * n / p ^ j) := this
        _ ≤ ∑ j ∈ Ico (i + 1) b, phi (24 * n / p ^ j) :=
          Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (by omega) le_rfl)
    · have hlt : i + 1 < b := by
        by_contra hcon
        rw [T_eq_zero hp hb (by omega), phi_zero] at hφ
        exact hφ rfl
      calc 1 ≤ phi (24 * n / p ^ (i + 1)) := by omega
        _ ≤ ∑ j ∈ Ico (i + 1) b, phi (24 * n / p ^ j) :=
          Finset.single_le_sum (f := fun j => phi (24 * n / p ^ j)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩)

/-- Escape for `p = 3`: if `phi T_i = 1` or `T_i mod 24 ≥ 9`, then some `j ≥ i` has `phi T_j = 1`. -/
theorem escape3 {n b : ℕ} (hb : 24 * n < 3 ^ b) (i : ℕ)
    (h : 1 ≤ phi (24 * n / 3 ^ i) ∨ 9 ≤ 24 * n / 3 ^ i % 24) :
    1 ≤ ∑ j ∈ Ico i b, phi (24 * n / 3 ^ j) := by
  have hib : i < b := by
    by_contra hcon
    rw [T_eq_zero (by norm_num) hb (by omega), phi_zero] at h
    omega
  rcases h with h | h
  · calc 1 ≤ phi (24 * n / 3 ^ i) := h
      _ ≤ ∑ j ∈ Ico i b, phi (24 * n / 3 ^ j) :=
        Finset.single_le_sum (f := fun j => phi (24 * n / 3 ^ j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_Ico.mpr ⟨le_rfl, hib⟩)
  · have := escape_gen n 3 b 9 (by norm_num) hb (by norm_num) step3 (b - i) i (by omega) h
    calc 1 ≤ ∑ j ∈ Ico (i + 1) b, phi (24 * n / 3 ^ j) := this
      _ ≤ ∑ j ∈ Ico i b, phi (24 * n / 3 ^ j) :=
        Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (by omega) le_rfl)

/-- Escape for `p = 2`: if `phi T_i = 1` or `T_i mod 24 ≥ 6`, then some `j ≥ i` has `phi T_j = 1`. -/
theorem escape2 {n b : ℕ} (hb : 24 * n < 2 ^ b) (i : ℕ)
    (h : 1 ≤ phi (24 * n / 2 ^ i) ∨ 6 ≤ 24 * n / 2 ^ i % 24) :
    1 ≤ ∑ j ∈ Ico i b, phi (24 * n / 2 ^ j) := by
  have hib : i < b := by
    by_contra hcon
    rw [T_eq_zero (by norm_num) hb (by omega), phi_zero] at h
    omega
  rcases h with h | h
  · calc 1 ≤ phi (24 * n / 2 ^ i) := h
      _ ≤ ∑ j ∈ Ico i b, phi (24 * n / 2 ^ j) :=
        Finset.single_le_sum (f := fun j => phi (24 * n / 2 ^ j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_Ico.mpr ⟨le_rfl, hib⟩)
  · have := escape_gen n 2 b 6 (by norm_num) hb (by norm_num) step2 (b - i) i (by omega) h
    calc 1 ≤ ∑ j ∈ Ico (i + 1) b, phi (24 * n / 2 ^ j) := this
      _ ≤ ∑ j ∈ Ico i b, phi (24 * n / 2 ^ j) :=
        Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (by omega) le_rfl)

/-- Double escape for `p = 2`: if `phi T_i = 1` and `T_i mod 24 ≥ 6`, the sum from `i` is `≥ 2`. -/
theorem escape2_two {n b : ℕ} (hb : 24 * n < 2 ^ b) (i : ℕ) (h1 : 1 ≤ phi (24 * n / 2 ^ i))
    (h6 : 6 ≤ 24 * n / 2 ^ i % 24) : 2 ≤ ∑ j ∈ Ico i b, phi (24 * n / 2 ^ j) := by
  have hib : i < b := by
    by_contra hcon
    rw [T_eq_zero (by norm_num) hb (by omega), phi_zero] at h1
    omega
  have := escape_gen n 2 b 6 (by norm_num) hb (by norm_num) step2 (b - i) i (by omega) h6
  rw [Finset.sum_eq_sum_Ico_succ_bot hib]
  omega

/-! ### Locating `⌊x / q⌋` -/

theorem div_bracket {x s q y c : ℕ} (hq : 0 < q) (hx : x + s = q * y) (hs : 0 < s)
    (hsc : s ≤ c * q) : y - c ≤ x / q ∧ x / q < y := by
  have hyq : y * q = q * y := mul_comm _ _
  constructor
  · rw [Nat.le_div_iff_mul_le hq, Nat.sub_mul]
    omega
  · rw [Nat.div_lt_iff_lt_mul hq]
    omega

theorem div_exact {x s q y : ℕ} (hx : x = q * y + s) (hsq : s < q) : x / q = y := by
  subst hx
  rw [Nat.mul_add_div (by omega : 0 < q), Nat.div_eq_of_lt hsq, add_zero]

theorem odd_of_mul {q m x : ℕ} (hx : x % 2 = 1) (h : x = q * m) : m % 2 = 1 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have : q * (k + k) = 2 * (q * k) := by ring
    omega
  · omega

end A211420Core
