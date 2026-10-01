import DMSolutions.OEIS_A211420.CoreDefs

/-!
# OEIS A211420: the Legendre term at prime powers dividing the linear forms

With `T = ⌊24 n / q⌋`:

* `phi_succ`: `q ∣ n + 1`, `q ≥ 8` gives `T ≡ 21, 22, 23 (mod 24)`, so `phi T = 1`.
* `phi_two_succ`: `q ∣ 2n + 1`, `q ≥ 4` gives `T ≡ 9, 10, 11`.
* `phi_three_succ`: `q ∣ 3n + 1`, `q ≥ 4`, `q ≠ 5` gives `phi T = 1`.
* `phi_eight_pred`: `q ∣ 8n - 1`, `q ≥ 4` gives `T = 3m` with `m` odd.
* `phi_conj2`, `phi_conj4`: the same for `q ∣ kn + i` (`24 i ≤ q`) and `q ∣ 8n - s` (`3 s < q`).

The exceptional prime powers are `2, 3, 4, 5, 7` for `n + 1`, `3` for `2n + 1`, `2, 5` for
`3n + 1` and `3` for `8n - 1`. At `p = 2, 3` the deficit is repaid by a later index
(`succ_val2_aux`, `succ_val3_aux`, `three_succ_val2_aux`, `eight_pred_val3_aux`).
-/

open Finset Nat

namespace A211420Core

/-- `phi` is `24`-periodic. -/
theorem phi_mod (T : ℕ) : phi T = phi (T % 24) := by
  obtain ⟨r, k, hr, rfl⟩ : ∃ r k, r < 24 ∧ T = r + 24 * k :=
    ⟨T % 24, T / 24, Nat.mod_lt _ (by norm_num), (Nat.mod_add_div T 24).symm⟩
  have e3 : (r + 24 * k) / 3 = r / 3 + 8 * k := by
    rw [show r + 24 * k = r + 3 * (8 * k) by ring, Nat.add_mul_div_left _ _ (by norm_num)]
  have e24 : (r + 24 * k) / 24 = r / 24 + k := Nat.add_mul_div_left _ _ (by norm_num)
  have e6 : (r + 24 * k) / 6 = r / 6 + 4 * k := by
    rw [show r + 24 * k = r + 6 * (4 * k) by ring, Nat.add_mul_div_left _ _ (by norm_num)]
  have e8 : (r + 24 * k) / 8 = r / 8 + 3 * k := by
    rw [show r + 24 * k = r + 8 * (3 * k) by ring, Nat.add_mul_div_left _ _ (by norm_num)]
  have e12 : (r + 24 * k) / 12 = r / 12 + 2 * k := by
    rw [show r + 24 * k = r + 12 * (2 * k) by ring, Nat.add_mul_div_left _ _ (by norm_num)]
  have hmod : (r + 24 * k) % 24 = r := by omega
  rw [hmod]
  unfold phi hi lo
  rw [e3, e24, e6, e8, e12]
  omega

/-- The table of `phi` on residues mod `24`: `phi T = 1` iff
`T mod 24 ∈ {3, 4, 5, 6, 7, 9, 10, 11, 15, 21, 22, 23}`. -/
theorem one_le_phi_iff (T : ℕ) : 1 ≤ phi T ↔
    (T % 24 = 3 ∨ T % 24 = 4 ∨ T % 24 = 5 ∨ T % 24 = 6 ∨ T % 24 = 7 ∨ T % 24 = 9 ∨
      T % 24 = 10 ∨ T % 24 = 11 ∨ T % 24 = 15 ∨ T % 24 = 21 ∨ T % 24 = 22 ∨ T % 24 = 23) := by
  rw [phi_mod]
  have hr : T % 24 < 24 := Nat.mod_lt _ (by norm_num)
  generalize T % 24 = r at hr ⊢
  interval_cases r <;> decide

theorem phi_succ {n q : ℕ} (hq : 8 ≤ q) (hd : q ∣ n + 1) : 1 ≤ phi (24 * n / q) := by
  obtain ⟨m, hm⟩ := hd
  obtain ⟨h1, h2⟩ := div_bracket (x := 24 * n) (s := 24) (q := q) (y := 24 * m) (c := 3)
    (by omega) (by rw [show q * (24 * m) = 24 * (q * m) by ring]; omega) (by norm_num) (by omega)
  generalize 24 * n / q = T at h1 h2 ⊢
  rw [one_le_phi_iff]
  omega

theorem phi_two_succ {n q : ℕ} (hq : 4 ≤ q) (hd : q ∣ 2 * n + 1) : 1 ≤ phi (24 * n / q) := by
  obtain ⟨m, hm⟩ := hd
  have hodd : m % 2 = 1 := odd_of_mul (x := 2 * n + 1) (by omega) hm
  obtain ⟨h1, h2⟩ := div_bracket (x := 24 * n) (s := 12) (q := q) (y := 12 * m) (c := 3)
    (by omega) (by rw [show q * (12 * m) = 12 * (q * m) by ring]; omega) (by norm_num) (by omega)
  generalize 24 * n / q = T at h1 h2 ⊢
  rw [one_le_phi_iff]
  omega

theorem phi_three_succ {n q : ℕ} (hq : 4 ≤ q) (hq5 : q ≠ 5) (hd : q ∣ 3 * n + 1) :
    1 ≤ phi (24 * n / q) := by
  obtain ⟨m, hm⟩ := hd
  by_cases h8 : 8 ≤ q
  · obtain ⟨h1, h2⟩ := div_bracket (x := 24 * n) (s := 8) (q := q) (y := 8 * m) (c := 1)
      (by omega) (by rw [show q * (8 * m) = 8 * (q * m) by ring]; omega) (by norm_num) (by omega)
    generalize 24 * n / q = T at h1 h2 ⊢
    rw [one_le_phi_iff]
    omega
  · interval_cases q <;> rw [one_le_phi_iff] <;> omega

theorem phi_eight_pred {n q : ℕ} (hn : 1 ≤ n) (hq : 4 ≤ q) (hd : q ∣ 8 * n - 1) :
    1 ≤ phi (24 * n / q) := by
  obtain ⟨m, hm⟩ := hd
  have hodd : m % 2 = 1 := odd_of_mul (x := 8 * n - 1) (by omega) hm
  have hT : 24 * n / q = 3 * m :=
    div_exact (s := 3) (by rw [show q * (3 * m) = 3 * (q * m) by ring]; omega) (by omega)
  rw [hT]
  rw [one_le_phi_iff]
  omega

theorem phi_conj2 {k n q i m : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3) (hi1 : 1 ≤ i) (hq : 24 * i ≤ q)
    (hm : k * n + i = q * m) : 1 ≤ phi (24 * n / q) := by
  rcases hk with rfl | rfl | rfl
  · obtain ⟨h1, h2⟩ := div_bracket (x := 24 * n) (s := 24 * i) (q := q) (y := 24 * m) (c := 1)
      (by omega) (by rw [show q * (24 * m) = 24 * (q * m) by ring]; omega) (by omega) (by omega)
    generalize 24 * n / q = T at h1 h2 ⊢
    rw [one_le_phi_iff]
    omega
  · obtain ⟨h1, h2⟩ := div_bracket (x := 24 * n) (s := 12 * i) (q := q) (y := 12 * m) (c := 1)
      (by omega) (by rw [show q * (12 * m) = 12 * (q * m) by ring]; omega) (by omega) (by omega)
    generalize 24 * n / q = T at h1 h2 ⊢
    rw [one_le_phi_iff]
    omega
  · obtain ⟨h1, h2⟩ := div_bracket (x := 24 * n) (s := 8 * i) (q := q) (y := 8 * m) (c := 1)
      (by omega) (by rw [show q * (8 * m) = 8 * (q * m) by ring]; omega) (by omega) (by omega)
    generalize 24 * n / q = T at h1 h2 ⊢
    rw [one_le_phi_iff]
    omega

theorem phi_conj4 {n q s m : ℕ} (hs : s % 2 = 1) (hq : 3 * s < q) (hm : 8 * n = q * m + s) :
    1 ≤ phi (24 * n / q) := by
  have hodd : m % 2 = 1 := odd_of_mul (q := q) (x := 8 * n - s) (by omega) (by omega)
  have hT : 24 * n / q = 3 * m :=
    div_exact (s := 3 * s) (by rw [show q * (3 * m) = 3 * (q * m) by ring]; omega) hq
  rw [hT]
  rw [one_le_phi_iff]
  omega

/-! ### The primes `2` and `3` -/

theorem pow3_mod8 (e : ℕ) : 3 ^ e % 8 = 1 ∨ 3 ^ e % 8 = 3 := by
  induction e with
  | zero => left; rfl
  | succ e ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> omega

theorem pow_ge {p i j : ℕ} (hp : 0 < p) (hij : j ≤ i) : p ^ j ≤ p ^ i :=
  Nat.pow_le_pow_right hp hij

/-- `v_2(n + 1) ≤ v_2(a n)`: the indices `1, 2` are repaid by `e + 1` and a later index. -/
theorem succ_val2_aux {n b e u : ℕ} (hb : 24 * n < 2 ^ b) (heb : e < b) (he0 : 1 ≤ e)
    (htm : 2 ^ e * u = n + 1) (hu : u % 2 = 1) :
    e ≤ ∑ i ∈ Ico 1 b, phi (24 * n / 2 ^ i) := by
  have h1 : (e + 1) - 3 ≤ ∑ i ∈ Ico 1 (e + 1), phi (24 * n / 2 ^ i) := by
    refine card_le_sum (f := fun i => phi (24 * n / 2 ^ i)) (l := 3) (by norm_num) le_rfl ?_
    intro i hi3 hie
    apply phi_succ
    · calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ i := pow_ge (by norm_num) hi3
    · exact (pow_dvd_pow 2 (by omega : i ≤ e)).trans (Dvd.intro u htm)
  have h2 : 2 ≤ ∑ i ∈ Ico (e + 1) b, phi (24 * n / 2 ^ i) := by
    have hpow : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    have key : 1 ≤ phi (24 * n / 2 ^ (e + 1)) ∧ 6 ≤ 24 * n / 2 ^ (e + 1) % 24 := by
      rcases (show e = 1 ∨ e = 2 ∨ 3 ≤ e by omega) with h | h | h
      · subst h
        norm_num at htm ⊢
        rw [one_le_phi_iff]
        omega
      · subst h
        norm_num at htm ⊢
        rw [one_le_phi_iff]
        omega
      · have h8 : 8 ≤ 2 ^ e := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ e := pow_ge (by norm_num) h
        obtain ⟨hT1, hT2⟩ := div_bracket (x := 24 * n) (s := 24) (q := 2 ^ (e + 1)) (y := 12 * u)
          (c := 2) (by positivity)
          (by rw [hpow, show 2 * 2 ^ e * (12 * u) = 24 * (2 ^ e * u) by ring]; omega)
          (by norm_num) (by rw [hpow]; omega)
        generalize 24 * n / 2 ^ (e + 1) = T at hT1 hT2 ⊢
        rw [one_le_phi_iff]
        omega
    exact escape2_two hb (e + 1) key.1 key.2
  rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ e + 1) (by omega : e + 1 ≤ b)]
  omega

/-- `v_3(n + 1) ≤ v_3(a n)`: the index `1` is repaid by an index `≥ e + 1`. -/
theorem succ_val3_aux {n b e m : ℕ} (hb : 24 * n < 3 ^ b) (heb : e < b) (he0 : 1 ≤ e)
    (htm : 3 ^ e * m = n + 1) : e ≤ ∑ i ∈ Ico 1 b, phi (24 * n / 3 ^ i) := by
  have h1 : (e + 1) - 2 ≤ ∑ i ∈ Ico 1 (e + 1), phi (24 * n / 3 ^ i) := by
    refine card_le_sum (f := fun i => phi (24 * n / 3 ^ i)) (l := 2) (by norm_num) le_rfl ?_
    intro i hi2 hie
    apply phi_succ
    · calc 8 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ i := pow_ge (by norm_num) hi2
    · exact (pow_dvd_pow 3 (by omega : i ≤ e)).trans (Dvd.intro m htm)
  have h2 : 1 ≤ ∑ i ∈ Ico (e + 1) b, phi (24 * n / 3 ^ i) := by
    have hpow : 3 ^ (e + 1) = 3 * 3 ^ e := by rw [pow_succ]; ring
    have h3e : 3 ≤ 3 ^ e := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ e := pow_ge (by norm_num) he0
    obtain ⟨hT1, hT2⟩ := div_bracket (x := 24 * n) (s := 24) (q := 3 ^ (e + 1)) (y := 8 * m)
      (c := 3) (by positivity)
      (by rw [hpow, show 3 * 3 ^ e * (8 * m) = 24 * (3 ^ e * m) by ring]; omega)
      (by norm_num) (by rw [hpow]; omega)
    apply escape3 hb (e + 1)
    generalize 24 * n / 3 ^ (e + 1) = T at hT1 hT2 ⊢
    rw [one_le_phi_iff]
    omega
  rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ e + 1) (by omega : e + 1 ≤ b)]
  omega

/-- `v_2(3n + 1) ≤ v_2(a n)`: the index `1` is repaid by an index `≥ e + 1`. -/
theorem three_succ_val2_aux {n b e u : ℕ} (hb : 24 * n < 2 ^ b) (heb : e < b) (he0 : 1 ≤ e)
    (htm : 2 ^ e * u = 3 * n + 1) (hu : u % 2 = 1) :
    e ≤ ∑ i ∈ Ico 1 b, phi (24 * n / 2 ^ i) := by
  have h1 : (e + 1) - 2 ≤ ∑ i ∈ Ico 1 (e + 1), phi (24 * n / 2 ^ i) := by
    refine card_le_sum (f := fun i => phi (24 * n / 2 ^ i)) (l := 2) (by norm_num) le_rfl ?_
    intro i hi2 hie
    apply phi_three_succ
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ i := pow_ge (by norm_num) hi2
    · intro h5
      have h2i : 2 ∣ 2 ^ i := dvd_pow_self 2 (by omega)
      rw [h5] at h2i
      omega
    · exact (pow_dvd_pow 2 (by omega : i ≤ e)).trans (Dvd.intro u htm)
  have h2 : 1 ≤ ∑ i ∈ Ico (e + 1) b, phi (24 * n / 2 ^ i) := by
    apply escape2 hb (e + 1)
    have hpow : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    rcases (show e = 1 ∨ 2 ≤ e by omega) with h | h
    · subst h
      norm_num at htm ⊢
      rw [one_le_phi_iff]
      omega
    · have h4 : 4 ≤ 2 ^ e := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ e := pow_ge (by norm_num) h
      obtain ⟨hT1, hT2⟩ := div_bracket (x := 24 * n) (s := 8) (q := 2 ^ (e + 1)) (y := 4 * u)
        (c := 1) (by positivity)
        (by rw [hpow, show 2 * 2 ^ e * (4 * u) = 8 * (2 ^ e * u) by ring]; omega)
        (by norm_num) (by rw [hpow]; omega)
      generalize 24 * n / 2 ^ (e + 1) = T at hT1 hT2 ⊢
      rw [one_le_phi_iff]
      omega
  rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ e + 1) (by omega : e + 1 ≤ b)]
  omega

/-- `v_3(8n - 1) ≤ v_3(a n)`: the index `1` is repaid by an index `≥ e + 1`. -/
theorem eight_pred_val3_aux {n b e m : ℕ} (hn : 1 ≤ n) (hb : 24 * n < 3 ^ b) (heb : e < b)
    (he0 : 1 ≤ e) (htm : 3 ^ e * m = 8 * n - 1) : e ≤ ∑ i ∈ Ico 1 b, phi (24 * n / 3 ^ i) := by
  have h1 : (e + 1) - 2 ≤ ∑ i ∈ Ico 1 (e + 1), phi (24 * n / 3 ^ i) := by
    refine card_le_sum (f := fun i => phi (24 * n / 3 ^ i)) (l := 2) (by norm_num) le_rfl ?_
    intro i hi2 hie
    apply phi_eight_pred hn
    · calc 4 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ i := pow_ge (by norm_num) hi2
    · exact (pow_dvd_pow 3 (by omega : i ≤ e)).trans (Dvd.intro m htm)
  have h2 : 1 ≤ ∑ i ∈ Ico (e + 1) b, phi (24 * n / 3 ^ i) := by
    have hpow : 3 ^ (e + 1) = 3 * 3 ^ e := by rw [pow_succ]; ring
    have h3e : 3 ≤ 3 ^ e := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ e := pow_ge (by norm_num) he0
    have hT : 24 * n / 3 ^ (e + 1) = m := by
      apply div_exact (s := 3)
      · rw [hpow, show 3 * 3 ^ e * m = 3 * (3 ^ e * m) by ring]
        omega
      · rw [hpow]
        omega
    have hm8 : m % 8 = 5 ∨ m % 8 = 7 := by
      have hmod : 3 ^ e * m % 8 = 7 := by omega
      rw [Nat.mul_mod] at hmod
      rcases pow3_mod8 e with h | h <;> rw [h] at hmod <;> omega
    apply escape3 hb (e + 1)
    rw [hT]
    rw [one_le_phi_iff]
    omega
  rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ e + 1) (by omega : e + 1 ≤ b)]
  omega

/-- The `p`-part of `t`: `e = v_p(t) < b`, `t = p ^ e * m` and `p ∤ m`. -/
theorem val_wrap {t p b : ℕ} (hp : p.Prime) (ht : t ≠ 0) (htb : t < p ^ b) :
    t.factorization p < b ∧ p ^ t.factorization p * (t / p ^ t.factorization p) = t ∧
      ¬ p ∣ t / p ^ t.factorization p := by
  refine ⟨?_, Nat.ordProj_mul_ordCompl_eq_self t p, Nat.not_dvd_ordCompl hp ht⟩
  have h1 : p ^ t.factorization p ≤ t := Nat.le_of_dvd (Nat.pos_of_ne_zero ht) (Nat.ordProj_dvd t p)
  exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt h1 htb)

end A211420Core
