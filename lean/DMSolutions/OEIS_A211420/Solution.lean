import DMSolutions.OEIS_A211420.Statement
import DMSolutions.OEIS_A211420.Core

/-!
# Solution of `OeisA211420.conjecture1` to `OeisA211420.conjecture4`

The statements are those of `FormalConjectures/OEIS/211420.lean` (formal-conjectures pull request
6426), included unmodified as `Statement.lean`. They are stated here with the repository's own
definitions `OeisA211420.a` and `OeisA211420.oddDescendingProduct`, which agree with the copies in
`A211420Core` by `rfl`.

* `conjecture1_solved`: `(n + 1) ∣ 35 a(n)`, `(2n + 1) ∣ 3 a(n)` and `(3n + 1) ∣ 5 a(n)`.
* `conjecture2_solved`: one can take `C(k, r) = ((24 r)!)^r`.
* `conjecture3_solved`: `(8n - 1) ∣ a(n)`.
* `conjecture4_solved`: one can take `K(r) = ((6 r + 3)!)^(r + 1)`.
-/

namespace OeisA211420

theorem a_eq_core : a = A211420Core.a := rfl

theorem oddDescendingProduct_eq_core :
    oddDescendingProduct = A211420Core.oddDescendingProduct := rfl

theorem conjecture1_solved (n : ℕ) :
    (n + 1) ∣ 35 * a n ∧ (2 * n + 1) ∣ 3 * a n ∧ (3 * n + 1) ∣ 5 * a n := by
  rw [a_eq_core]
  exact A211420Core.conjecture1_core n

theorem conjecture2_solved (k r : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, (k * n + 1).ascFactorial r ∣ C * a n := by
  rw [a_eq_core]
  exact A211420Core.conjecture2_core k r hk hr

theorem conjecture3_solved (n : ℕ) :
    ((8 * n : ℤ) - 1) ∣ (a n : ℤ) := by
  rw [a_eq_core]
  exact A211420Core.conjecture3_core n

theorem conjecture4_solved (r : ℕ) :
    ∃ K : ℤ, 0 < K ∧ ∀ n : ℕ, oddDescendingProduct n r ∣ (a n : ℤ) * K := by
  rw [a_eq_core, oddDescendingProduct_eq_core]
  exact A211420Core.conjecture4_core r

end OeisA211420
