# Divisibility of (8n)! n! / ((4n)! (3n)! (2n)!): proofs of Bala's conjectures on OEIS A211420

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT. **Paper:** [`paper/main.pdf`](paper/main.pdf)

`a(n) = (8n)! n! / ((4n)! (3n)! (2n)!)` = 1, 140, 60060, 29745716, … is [OEIS A211420](https://oeis.org/A211420).

In 2025 Peter Bala recorded four conjectures in the OEIS entry. Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) states them as
`OeisA211420.conjecture1` … `conjecture4` (`research open`) in pull request
[#6426](https://github.com/google-deepmind/formal-conjectures/pull/6426), file `FormalConjectures/OEIS/211420.lean`.

**This repository proves all four, with Lean 4 proofs of the exact statements.**

| Statement | Claim | Our constant | Status of the mathematics |
|---|---|---|---|
| `conjecture1` | `(n+1) ∣ 35 a(n)`, `(2n+1) ∣ 3 a(n)`, `(3n+1) ∣ 5 a(n)` | as stated; all three are optimal | `(3n+1) ∣ 5a(n)` follows from Z.-W. Sun (2012). The other two parts are new, as far as we found. |
| `conjecture2` | `(kn+1)⋯(kn+r) ∣ C(k,r) a(n)` for `k ∈ {1,2,3}` | `C = ((24r)!)^r` | Known. [DannyExperiments/a211420-fixed-divisor](https://github.com/DannyExperiments/a211420-fixed-divisor) proved it in Lean, with `lcm(1..8r−1)^r`. |
| `conjecture3` | `(8n − 1) ∣ a(n)` | none | New, as far as we found. Adamczewski's `K(r)` theorem gives only `(8n−1) ∣ 8! a(n)`. |
| `conjecture4` | `(8n−1)(8n−3)⋯(8n−2r−1) ∣ K(r) a(n)` | `K = ((6r+3)!)^(r+1)` | Known. T. Adamczewski, arXiv:2608.11941, Appendix A, proved it with `K = (8r)!`. |

## The proof in one paragraph

Put `T = ⌊24n/p^j⌋`. Legendre's formula gives `v_p(a(n)) = Σ_j φ(⌊24n/p^j⌋)`, with

```
φ(T) = ⌊T/3⌋ + ⌊T/24⌋ − ⌊T/6⌋ − ⌊T/8⌋ − ⌊T/12⌋,
```

which has period 24 and equals 1 exactly when `T mod 24 ∈ {3,4,5,6,7,9,10,11,15,21,22,23}`. If `p^j` divides `n+1`, `2n+1`,
`3n+1` or `8n−1` and is not too small, `T` lands in that set, so `φ = 1`. The constants 35, 3, 5 absorb the small prime
powers 5, 7, 3. The remaining deficits at `p = 2, 3` are paid by an "escape" lemma: if the residue of `T_i` is large,
some later `T_j` has `φ = 1`.

## Lean 4 verification (`lean/`)

- `Statement.lean` is the pull-request file, byte-identical (git blob `25daf953`), compiled with the repository's
  `leanOptions`.
- The Core files import Mathlib only:
  - `CoreDefs`: verbatim definitions;
  - `CoreLemmas`: the residue function and the location and escape lemmas;
  - `CoreConj13`, `CoreConj24`: the four conjectures;
  - `Core`: assembly.
- `Solution.lean` proves `OeisA211420.conjecture1_solved` … `conjecture4_solved`.
- `CheckAnswer.lean` checks by `rfl` that each has exactly the type of the repository statement, and that the copied
  definitions agree. It also prints the axioms: only `propext`, `Classical.choice` and `Quot.sound`. There is no
  `sorry`, `admit` or `native_decide` in our files.

To reproduce, you need:
- Lean v4.33.1;
- a formal-conjectures checkout, tested at `ab0addc45f699bdd0b7cc58efa5140a72f101a9e`;
- `lake exe cache get`, run in that checkout.

Then run:

```bash
bash lean/check.sh /path/to/formal-conjectures
```

Log: `logs/lean_check.log` (exit 0, 237 s).

## Numerical checks (`scripts/`, `logs/`)

- `verify.py` checks every lemma, and conjectures 1 and 3, via valuations for `n ≤ 200 000`, and with exact integers
  for `n < 400`.
- `verify2.py` checks conjectures 2 and 4 for `r ≤ 6` and `n ≤ 3000`. It also computes the minimal constants, e.g.
  `K(1) = 3`, `K(2) = 105`, `C(2, 2) = 210`.

## Prior work

- Integrality: Landau's criterion; Bober, J. London Math. Soc. 79 (2009).
- `(3n+1) ∣ 5a(n)`: the case `k = 4` of Z.-W. Sun, J. Aust. Math. Soc. 93 (2012),
  `C(2n,n) ∣ (k+1)′ C_n^(k−1) C(2kn,kn)`, since `a(n) = C(8n,4n) C(4n,n) / C(2n,n)`.
- `(2n+1)(2n+3) ∣ 99 a(n)`: Yang, EJC 22 (2015), as cited by DannyExperiments.
- Conjecture 2: DannyExperiments (2026), Zenodo doi:10.5281/zenodo.21762443.
- Conjecture 4: Adamczewski, arXiv:2608.11941 (2026). The OEIS entry cites it.
- Search date 2026-10-01. We found no earlier proof of `(n+1) ∣ 35 a(n)`, `(2n+1) ∣ 3 a(n)` or `(8n−1) ∣ a(n)` in:
  - Formal Conjectures issues and pull requests;
  - the-omega-institute/trureturing;
  - the fc-review-results audits;
  - the OEIS entry;
  - web search.
