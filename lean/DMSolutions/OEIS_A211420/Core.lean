import DMSolutions.OEIS_A211420.CoreConj13
import DMSolutions.OEIS_A211420.CoreConj24

/-!
# OEIS A211420: the four conjectures, in the form of the repository statements

The statements below are those of `conjecture1` to `conjecture4` in
`FormalConjectures/OEIS/211420.lean` (formal-conjectures pull request 6426), stated for the copies
`A211420Core.a` and `A211420Core.oddDescendingProduct` of the repository definitions.

* `conjecture1_core`: `(n + 1) ∣ 35 a(n)`, `(2n + 1) ∣ 3 a(n)`, `(3n + 1) ∣ 5 a(n)`.
* `conjecture2_core`: `C = ((24 r)!)^r` works for `k ∈ {1, 2, 3}`.
* `conjecture3_core`: `(8n - 1) ∣ a(n)` in `ℤ` (at `n = 0` the divisor is `-1`).
* `conjecture4_core`: `K = ((6 r + 3)!)^(r + 1)` works.
-/

open Finset Nat

namespace A211420Core

theorem conjecture1_core (n : ℕ) :
    (n + 1) ∣ 35 * a n ∧ (2 * n + 1) ∣ 3 * a n ∧ (3 * n + 1) ∣ 5 * a n :=
  ⟨succ_dvd n, two_succ_dvd n, three_succ_dvd n⟩

theorem conjecture2_core (k r : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, (k * n + 1).ascFactorial r ∣ C * a n :=
  ⟨(24 * r)! ^ r, by positivity, asc_dvd k r hk hr⟩

theorem conjecture3_core (n : ℕ) :
    ((8 * n : ℤ) - 1) ∣ (a n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hcast : ((8 * n : ℤ) - 1) = ((8 * n - 1 : ℕ) : ℤ) := by omega
    rw [hcast]
    exact Int.natCast_dvd_natCast.mpr (eight_pred_dvd n hn)

theorem natAbs_prod_range (f : ℕ → ℤ) (m : ℕ) :
    (∏ i ∈ range m, f i).natAbs = ∏ i ∈ range m, (f i).natAbs := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, Finset.prod_range_succ, Int.natAbs_mul, ih]

theorem conjecture4_core (r : ℕ) :
    ∃ K : ℤ, 0 < K ∧ ∀ n : ℕ, oddDescendingProduct n r ∣ (a n : ℤ) * K := by
  refine ⟨((6 * r + 3)! ^ (r + 1) : ℕ), by positivity, fun n => ?_⟩
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast,
    oddDescendingProduct, natAbs_prod_range, mul_comm (a n)]
  exact ell_prod_dvd r n

end A211420Core
