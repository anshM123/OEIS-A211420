import DMSolutions.OEIS_A211420.CoreLemmas

/-!
# OEIS A211420: conjectures 2 and 4

* `asc_dvd`: for `k ∈ {1, 2, 3}` and `r ≥ 1`, `(kn+1)(kn+2)⋯(kn+r) ∣ ((24r)!)^r a(n)`.
  Since `(kn)! · (kn+1)^(r) = (kn+r)!`, the `q`-term of the left side is
  `⌊(kn+r)/q⌋ - ⌊kn/q⌋`, the number of multiples of `q` in `(kn, kn+r]`. For `q ≤ 24r` it is at
  most `r ≤ r ⌊24r/q⌋`; for `q > 24r` it is at most `1`, and when it is `1` the multiple
  `kn + i` has `24 i < q`, so `phi = 1` (`phi_conj2`).
* `ell_prod_dvd`: `∏_{i=0}^{r} |8n - (2i+1)| ∣ ((6r+3)!)^(r+1) a(n)`. For `q ≤ 6r+3` at most
  `r + 1` factors are divisible by `q`; for `q > 6r+3` at most one is, it equals `8n - s` with
  `3 s < q`, and `phi = 1` (`phi_conj4`).
-/

open Finset Nat

namespace A211420Core

theorem add_div_le_add {x r q : ℕ} (hq : 0 < q) : (x + r) / q ≤ x / q + r := by
  calc (x + r) / q ≤ (x + r * q) / q :=
        Nat.div_le_div_right (Nat.add_le_add_left (Nat.le_mul_of_pos_right r hq) x)
    _ = x / q + r := Nat.add_mul_div_right x r hq

theorem add_div_le_succ {x r q : ℕ} (hrq : r ≤ q) (hq : 0 < q) : (x + r) / q ≤ x / q + 1 := by
  calc (x + r) / q ≤ (x + 1 * q) / q := Nat.div_le_div_right (by omega)
    _ = x / q + 1 := Nat.add_mul_div_right x 1 hq

theorem conj2_term {k r n q : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) (hq : 2 ≤ q) :
    (k * n + r) / q ≤ k * n / q + r * (24 * r / q) + phi (24 * n / q) := by
  by_cases hsmall : q ≤ 24 * r
  · have h1 : 1 ≤ 24 * r / q := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have h2 : (k * n + r) / q ≤ k * n / q + r := add_div_le_add (by omega)
    have h3 : r ≤ r * (24 * r / q) := Nat.le_mul_of_pos_right r h1
    omega
  · have h0 : 24 * r / q = 0 := Nat.div_eq_of_lt (by omega)
    rw [h0, mul_zero, add_zero]
    have h1 : (k * n + r) / q ≤ k * n / q + 1 := add_div_le_succ (by omega) (by omega)
    rcases Nat.lt_or_ge ((k * n + r) / q) (k * n / q + 1) with h | h
    · omega
    · have hMeq : (k * n + r) / q = k * n / q + 1 := by omega
      have hM1 : q * (k * n / q + 1) ≤ k * n + r := by
        have := Nat.div_mul_le_self (k * n + r) q
        rw [hMeq, mul_comm] at this
        exact this
      have hM2 : k * n < q * (k * n / q + 1) := Nat.lt_mul_div_succ (k * n) (by omega)
      have hphi := phi_conj2 (n := n) (q := q) (i := q * (k * n / q + 1) - k * n)
        (m := k * n / q + 1) hk
        (by omega) (by omega) (by omega)
      omega

/-- Conjecture 2 with `C = ((24 r)!)^r`. -/
theorem asc_dvd (k r : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) (n : ℕ) :
    (k * n + 1).ascFactorial r ∣ (24 * r)! ^ r * a n := by
  have hP : (k * n)! * (k * n + 1).ascFactorial r = (k * n + r)! :=
    Nat.factorial_mul_ascFactorial _ _
  have hPne : (k * n + 1).ascFactorial r ≠ 0 := (Nat.ascFactorial_pos _ _).ne'
  apply dvd_mul_a (k * n + r + 24 * r) hPne (by positivity)
  intro p b hp hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hb
    omega
  have hPf : (k * n)!.factorization p + ((k * n + 1).ascFactorial r).factorization p =
      (k * n + r)!.factorization p := by
    rw [← hP, Nat.factorization_mul (factorial_ne_zero _) hPne]
    rfl
  rw [fact_eq hp hb0 (show k * n < p ^ b by omega),
    fact_eq hp hb0 (show k * n + r < p ^ b by omega)] at hPf
  have hc : ((24 * r)! ^ r).factorization p = r * ∑ i ∈ Ico 1 b, 24 * r / p ^ i := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      fact_eq hp hb0 (show 24 * r < p ^ b by omega)]
  have key : ∑ i ∈ Ico 1 b, (k * n + r) / p ^ i ≤
      ∑ i ∈ Ico 1 b, (k * n / p ^ i + r * (24 * r / p ^ i) + phi (24 * n / p ^ i)) := by
    refine Finset.sum_le_sum fun i hi => conj2_term hk hr ?_
    exact le_trans hp.two_le (Nat.le_self_pow (by have := (Finset.mem_Ico.mp hi).1; omega) p)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at key
  rw [hc]
  omega

/-- `ell n i = |8n - (2i+1)|`, the absolute value of the `i`-th factor of
`oddDescendingProduct n r`. -/
def ell (n i : ℕ) : ℕ := ((8 * n : ℤ) - (2 * i + 1 : ℤ)).natAbs

theorem ell_spec (n i : ℕ) :
    (2 * i + 1 < 8 * n ∧ ell n i = 8 * n - (2 * i + 1)) ∨
      (8 * n < 2 * i + 1 ∧ ell n i = 2 * i + 1 - 8 * n) := by
  unfold ell
  omega

theorem conj4_term {r n q : ℕ} (hq : 2 ≤ q) :
    ∑ i ∈ range (r + 1), (if q ∣ ell n i then 1 else 0) ≤
      (r + 1) * ((6 * r + 3) / q) + phi (24 * n / q) := by
  by_cases hsmall : q ≤ 6 * r + 3
  · have h1 : 1 ≤ (6 * r + 3) / q := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hs : ∑ i ∈ range (r + 1), (if q ∣ ell n i then 1 else 0) ≤ ∑ i ∈ range (r + 1), 1 :=
      Finset.sum_le_sum fun i _ => by split_ifs <;> omega
    have hr : ∑ i ∈ range (r + 1), (1 : ℕ) = r + 1 := by simp
    have hm : r + 1 ≤ (r + 1) * ((6 * r + 3) / q) := Nat.le_mul_of_pos_right _ h1
    omega
  · have h0 : (6 * r + 3) / q = 0 := Nat.div_eq_of_lt (by omega)
    rw [h0, mul_zero, zero_add, ← Finset.card_filter]
    have hmem : ∀ i ∈ (range (r + 1)).filter (fun i => q ∣ ell n i),
        ∃ m, 8 * n = q * m + (2 * i + 1) ∧ i ≤ r := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hir, hdvd⟩ := hi
      rcases ell_spec n i with ⟨hlt, heq⟩ | ⟨hlt, heq⟩
      · rw [heq] at hdvd
        obtain ⟨m, hm⟩ := hdvd
        exact ⟨m, by omega, by omega⟩
      · exfalso
        rw [heq] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
    rcases Finset.eq_empty_or_nonempty ((range (r + 1)).filter (fun i => q ∣ ell n i))
      with he | hne
    · rw [he]
      simp
    · obtain ⟨i0, hi0⟩ := hne
      obtain ⟨m0, hm0, hi0r⟩ := hmem i0 hi0
      have hphi : 1 ≤ phi (24 * n / q) := phi_conj4 (s := 2 * i0 + 1) (by omega) (by omega) hm0
      have hcard : ((range (r + 1)).filter (fun i => q ∣ ell n i)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro x hx y hy
        obtain ⟨mx, hmx, hxr⟩ := hmem x hx
        obtain ⟨my, hmy, hyr⟩ := hmem y hy
        have hTx : 24 * n / q = 3 * mx :=
          div_exact (s := 3 * (2 * x + 1))
            (by rw [show q * (3 * mx) = 3 * (q * mx) by ring]; omega) (by omega)
        have hTy : 24 * n / q = 3 * my :=
          div_exact (s := 3 * (2 * y + 1))
            (by rw [show q * (3 * my) = 3 * (q * my) by ring]; omega) (by omega)
        have hmxy : mx = my := by omega
        subst hmxy
        omega
      omega

/-- Conjecture 4 in `ℕ`, with `K = ((6r+3)!)^(r+1)`. -/
theorem ell_prod_dvd (r n : ℕ) :
    ∏ i ∈ range (r + 1), ell n i ∣ (6 * r + 3)! ^ (r + 1) * a n := by
  have hℓne : ∀ i, ell n i ≠ 0 := fun i => by
    unfold ell
    omega
  have hℓle : ∀ i, i ≤ r → ell n i ≤ 8 * n + 2 * r + 1 := fun i hi => by
    unfold ell
    omega
  apply dvd_mul_a (8 * n + 2 * r + 1 + (6 * r + 3))
    (Finset.prod_ne_zero_iff.mpr fun i _ => hℓne i) (by positivity)
  intro p b hp hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hb
    omega
  have hprod : (∏ i ∈ range (r + 1), ell n i).factorization p =
      ∑ j ∈ Ico 1 b, ∑ i ∈ range (r + 1), (if p ^ j ∣ ell n i then 1 else 0) := by
    rw [Nat.factorization_prod fun i _ => hℓne i, Finsupp.finsetSum_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hil := hℓle i (by rw [Finset.mem_range] at hi; omega)
    rw [Nat.factorization_eq_card_pow_dvd_of_lt (b := b) hp (Nat.pos_of_ne_zero (hℓne i))
      (by omega),
      Finset.card_filter]
  have hc : ((6 * r + 3)! ^ (r + 1)).factorization p =
      (r + 1) * ∑ j ∈ Ico 1 b, (6 * r + 3) / p ^ j := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      fact_eq hp hb0 (show 6 * r + 3 < p ^ b by omega)]
  rw [hprod, hc, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => conj4_term ?_
  exact le_trans hp.two_le (Nat.le_self_pow (by have := (Finset.mem_Ico.mp hj).1; omega) p)

end A211420Core
