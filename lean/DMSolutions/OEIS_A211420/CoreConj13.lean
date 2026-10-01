import DMSolutions.OEIS_A211420.CoreLemmas

/-!
# OEIS A211420: conjectures 1 and 3

* `succ_dvd`: `(n + 1) ∣ 35 a(n)`. Prime powers `q ≥ 8` dividing `n + 1` carry `phi = 1`;
  `q = 5, 7` divide `35`; at `p = 2, 3` the deficit is repaid (`succ_val2_aux`, `succ_val3_aux`).
* `two_succ_dvd`: `(2n + 1) ∣ 3 a(n)`. Every `q ≥ 4` carries `phi = 1`, and `q = 3` divides `3`.
* `three_succ_dvd`: `(3n + 1) ∣ 5 a(n)`. Every `q ≥ 4`, `q ≠ 5` carries `phi = 1`, `q = 5`
  divides `5`, and `p = 2` is repaid (`three_succ_val2_aux`).
* `eight_pred_dvd`: `(8n - 1) ∣ a(n)` for `n ≥ 1`. Every `q ≥ 4` carries `phi = 1`, and `p = 3`
  is repaid (`eight_pred_val3_aux`).
-/

open Finset Nat

namespace A211420Core

theorem pow_eq_one_of_lt_sq {p i : ℕ} (hp : 2 ≤ p) (hi : 1 ≤ i) (h : p ^ i < p * p) : i = 1 := by
  by_contra hne
  have : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right (by omega) (by omega)
  rw [sq] at this
  omega

/-- Conjecture 1, first part: `(n + 1) ∣ 35 a(n)`. -/
theorem succ_dvd (n : ℕ) : n + 1 ∣ 35 * a n := by
  apply dvd_mul_a 0 (by omega) (by norm_num)
  intro p b hp hb
  by_cases h2 : p = 2
  · subst h2
    have hw := val_wrap Nat.prime_two (show n + 1 ≠ 0 by omega) (show n + 1 < 2 ^ b by omega)
    rcases Nat.eq_zero_or_pos ((n + 1).factorization 2) with h0 | h0
    · rw [h0]
      exact Nat.zero_le _
    have := succ_val2_aux (show 24 * n < 2 ^ b by omega) hw.1 h0 hw.2.1
      (by have := hw.2.2; omega)
    omega
  by_cases h3 : p = 3
  · subst h3
    have hw := val_wrap Nat.prime_three (show n + 1 ≠ 0 by omega) (show n + 1 < 3 ^ b by omega)
    rcases Nat.eq_zero_or_pos ((n + 1).factorization 3) with h0 | h0
    · rw [h0]
      exact Nat.zero_le _
    have := succ_val3_aux (show 24 * n < 3 ^ b by omega) hw.1 h0 hw.2.1
    omega
  apply termwise hp (by omega) (by norm_num) (by omega) (by omega)
  intro i hi1 hdvd
  by_cases hq : 8 ≤ p ^ i
  · exact Or.inr (phi_succ hq hdvd)
  · left
    have hpi : p ≤ p ^ i := Nat.le_self_pow (by omega) p
    have hp2 := hp.two_le
    have hp8 : p < 8 := by omega
    interval_cases p
    · exact absurd rfl h2
    · exact absurd rfl h3
    · norm_num at hp
    · rw [pow_eq_one_of_lt_sq (p := 5) (by norm_num) hi1 (by omega)]
      norm_num
    · norm_num at hp
    · rw [pow_eq_one_of_lt_sq (p := 7) (by norm_num) hi1 (by omega)]
      norm_num

/-- Conjecture 1, second part: `(2n + 1) ∣ 3 a(n)`. -/
theorem two_succ_dvd (n : ℕ) : 2 * n + 1 ∣ 3 * a n := by
  apply dvd_mul_a 0 (by omega) (by norm_num)
  intro p b hp hb
  apply termwise hp (by omega) (by norm_num) (by omega) (by omega)
  intro i hi1 hdvd
  have hq2 : 2 ≤ p ^ i := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  generalize p ^ i = q at hq2 hdvd ⊢
  by_cases hq : 4 ≤ q
  · exact Or.inr (phi_two_succ hq hdvd)
  · left
    interval_cases q
    · omega
    · norm_num

/-- Conjecture 1, third part: `(3n + 1) ∣ 5 a(n)`. -/
theorem three_succ_dvd (n : ℕ) : 3 * n + 1 ∣ 5 * a n := by
  apply dvd_mul_a 0 (by omega) (by norm_num)
  intro p b hp hb
  by_cases h2 : p = 2
  · subst h2
    have hw := val_wrap Nat.prime_two (show 3 * n + 1 ≠ 0 by omega)
      (show 3 * n + 1 < 2 ^ b by omega)
    rcases Nat.eq_zero_or_pos ((3 * n + 1).factorization 2) with h0 | h0
    · rw [h0]
      exact Nat.zero_le _
    have := three_succ_val2_aux (show 24 * n < 2 ^ b by omega) hw.1 h0 hw.2.1
      (by have := hw.2.2; omega)
    omega
  apply termwise hp (by omega) (by norm_num) (by omega) (by omega)
  intro i hi1 hdvd
  have hpi : p ≤ p ^ i := Nat.le_self_pow (by omega) p
  have hp2 := hp.two_le
  have hq2 : 2 ≤ p ^ i := le_trans hp2 hpi
  generalize p ^ i = q at hpi hq2 hdvd ⊢
  by_cases hq5 : q = 5
  · subst hq5
    left
    norm_num
  by_cases hq : 4 ≤ q
  · exact Or.inr (phi_three_succ hq hq5 hdvd)
  · exfalso
    interval_cases q <;> omega

/-- Conjecture 3 for `n ≥ 1`: `(8n - 1) ∣ a(n)` in `ℕ`. -/
theorem eight_pred_dvd (n : ℕ) (hn : 1 ≤ n) : 8 * n - 1 ∣ a n := by
  have h := dvd_mul_a (t := 8 * n - 1) (c := 1) (n := n) 0 (by omega) one_ne_zero ?_
  · simpa using h
  intro p b hp hb
  by_cases h3 : p = 3
  · subst h3
    have hw := val_wrap Nat.prime_three (show 8 * n - 1 ≠ 0 by omega)
      (show 8 * n - 1 < 3 ^ b by omega)
    rcases Nat.eq_zero_or_pos ((8 * n - 1).factorization 3) with h0 | h0
    · rw [h0]
      exact Nat.zero_le _
    have := eight_pred_val3_aux hn (show 24 * n < 3 ^ b by omega) hw.1 h0 hw.2.1
    omega
  apply termwise hp (by omega) one_ne_zero (by omega) (by omega)
  intro i hi1 hdvd
  right
  apply phi_eight_pred hn _ hdvd
  have hpi : p ≤ p ^ i := Nat.le_self_pow (by omega) p
  have hpd : p ∣ 8 * n - 1 := (dvd_pow_self p (by omega)).trans hdvd
  have hp2 := hp.two_le
  by_contra hlt
  have hp4 : p < 4 := by omega
  interval_cases p
  · omega
  · exact absurd rfl h3

end A211420Core
