"""A211420 verification of every lemma used in the paper (paper/main.pdf), with exact integers.

a(n) = (8n)! n! / ((4n)! (3n)! (2n)!).
phi(T) = T/3 + T/24 - T/6 - T/8 - T/12 (integer division), T_j = 24n // p^j.
v_p(a(n)) = sum_{j>=1} phi(24n // p^j).

Usage: python verify.py [N]   (default N = 200000)
"""
import sys
from math import factorial

N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000


def phi(T):
    return T // 3 + T // 24 - T // 6 - T // 8 - T // 12


PHI = [phi(t) for t in range(24)]
assert PHI == [0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1], PHI
for T in range(0, 24 * 50):
    assert phi(T) == PHI[T % 24]
print("L0 phi is 24-periodic with the stated table: OK")

# L1: c*n // q == (24 n // q) // (24 // c) for c in {8,4,3,2,1}
for n in range(0, 400):
    for q in range(1, 400):
        T = 24 * n // q
        for c in (8, 4, 3, 2, 1):
            assert (c * n) // q == T // (24 // c)
print("L1 c*n/q = (24n/q)/(24/c): OK (n<400, q<400)")

# smallest-prime-factor sieve
M = 8 * N + 64
import numpy as np
spf = np.zeros(M + 1, dtype=np.int32)
for i in range(2, M + 1):
    if spf[i] == 0:
        spf[i] = i
        if i * i <= M:
            s = spf[i * i::i]
            s[s == 0] = i
spf = spf.tolist()


def factor(m):
    out = {}
    while m > 1:
        p = spf[m]
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        out[p] = e
    return out


def vpa(n, p):
    s, q = 0, p
    while q <= 24 * n:
        s += phi(24 * n // q)
        q *= p
    return s


def vp(m, p):
    e = 0
    while m % p == 0:
        m //= p
        e += 1
    return e


# exact cross-check of the Legendre/phi formula
for n in range(0, 120):
    A = factorial(8 * n) * factorial(n) // (factorial(4 * n) * factorial(3 * n) * factorial(2 * n))
    assert A * factorial(4 * n) * factorial(3 * n) * factorial(2 * n) == factorial(8 * n) * factorial(n)
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23):
        assert vp(A, p) == vpa(n, p) if A > 0 else True
print("phi-sum = v_p(a(n)) exactly for n<120: OK")

# ---------- termwise lemmas (all q >= 2, all n in range) ----------
cnt = 0
for q in range(2, 3000):
    for n in range(0, 3000):
        T = 24 * n // q
        if (8 * n - 1) % q == 0 and n >= 1 and q > 3:
            assert phi(T) == 1, ("8n-1", n, q)
        if (n + 1) % q == 0 and q >= 8:
            assert phi(T) == 1, ("n+1", n, q)
        if (2 * n + 1) % q == 0 and q >= 4:
            assert phi(T) == 1, ("2n+1", n, q)
        if (3 * n + 1) % q == 0 and q >= 4 and q != 5:
            assert phi(T) == 1, ("3n+1", n, q)
        cnt += 1
print("termwise lemmas (8n-1,q>3), (n+1,q>=8), (2n+1,q>=4), (3n+1,q>=4,q!=5): OK", cnt)

# generic lemma for conj2: q | k n + i, i>=1, (24/k) i <= q  ==> phi = 1
for k in (1, 2, 3):
    D = 24 // k
    for q in range(2, 600):
        for n in range(0, 600):
            for i in range(1, 30):
                if (k * n + i) % q == 0 and D * i <= q:
                    assert phi(24 * n // q) == 1, (k, n, q, i)
print("conj2 lemma: OK")
# generic lemma for conj4: q odd | 8n - s (s odd, 0<s<8n), 3 s < q ==> phi = 1
for q in range(3, 800, 2):
    for n in range(1, 800):
        for s in range(1, 60, 2):
            if s < 8 * n and (8 * n - s) % q == 0 and 3 * s < q:
                assert phi(24 * n // q) == 1, (n, q, s)
print("conj4 lemma: OK")

# ---------- escape lemmas ----------
def escape_ok(n, p, thr):
    # for every i with T_i % 24 >= thr: some j > i has phi(T_j) = 1
    Ts = []
    q = 1
    j = 0
    while True:
        T = 24 * n // q
        Ts.append(T)
        if T == 0:
            break
        q *= p
        j += 1
    for i in range(len(Ts)):
        if Ts[i] % 24 >= thr:
            if not any(phi(Ts[j]) == 1 for j in range(i + 1, len(Ts))):
                return False
    return True


for n in range(0, 200000):
    assert escape_ok(n, 3, 9), n
    assert escape_ok(n, 2, 6), n
print("escape lemmas p=3 (thr 9) and p=2 (thr 6): OK for n<200000")
# step lemmas (finite check on residues)
for S in range(0, 24 * 3):
    for d in range(3):
        if phi(S) == 0 and S % 24 < 9:
            assert (3 * S + d) % 24 < 9
    for d in range(2):
        if phi(S) == 0 and S % 24 < 6:
            assert (2 * S + d) % 24 < 6
print("step lemmas: OK")

# ---------- T_{e+1} claims ----------
for n in range(1, N + 1):
    # (8n-1), p=3
    t = 8 * n - 1
    e = vp(t, 3)
    if e >= 1:
        m = t // 3 ** e
        T = 24 * n // 3 ** (e + 1)
        assert T == m and m % 8 in (5, 7), n
        assert phi(T) == 1 or T % 24 >= 9
    # (n+1), p=3
    e = vp(n + 1, 3)
    if e >= 1:
        m = (n + 1) // 3 ** e
        T = 24 * n // 3 ** (e + 1)
        assert 8 * m - 3 <= T <= 8 * m - 1, n
        assert phi(T) == 1 or T % 24 >= 9, n
    # (n+1), p=2
    e = vp(n + 1, 2)
    if e >= 1:
        u = (n + 1) // 2 ** e
        T = 24 * n // 2 ** (e + 1)
        if e == 1:
            assert T == 12 * u - 6
        elif e == 2:
            assert T == 12 * u - 3
        else:
            assert 12 * u - 2 <= T <= 12 * u - 1
        assert phi(T) == 1 and T % 24 >= 6, n
    # (3n+1), p=2
    e = vp(3 * n + 1, 2)
    if e >= 1:
        u = (3 * n + 1) // 2 ** e
        T = 24 * n // 2 ** (e + 1)
        if e == 1:
            assert T == 6 * n and T % 24 == 18
        else:
            assert T == 4 * u - 1
        assert phi(T) == 1 or T % 24 >= 6, n
print("T_{e+1} claims: OK for n <=", N)

# ---------- conjecture 1 and 3 directly (valuations) up to N ----------
bad = []
for n in range(0, N + 1):
    for (t, c) in ((n + 1, 35), (2 * n + 1, 3), (3 * n + 1, 5), (8 * n - 1, 1)):
        if t <= 1:
            continue
        for p, e in factor(t).items():
            if e > vpa(n, p) + vp(c, p):
                bad.append((n, t, c, p))
print("conj1 & conj3 valuation check n <= %d: failures = %d" % (N, len(bad)))

# ---------- exact integer check for small n ----------
def a_exact(n):
    return factorial(8 * n) * factorial(n) // (factorial(4 * n) * factorial(3 * n) * factorial(2 * n))


for n in range(0, 400):
    A = a_exact(n)
    assert (35 * A) % (n + 1) == 0 and (3 * A) % (2 * n + 1) == 0 and (5 * A) % (3 * n + 1) == 0
    assert A % (8 * n - 1) == 0  # Python % with negative modulus: 8n-1 = -1 at n = 0
print("conj1 & conj3 exact integers n < 400: OK")
