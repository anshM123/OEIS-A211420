"""A211420, conjectures 2 and 4: p-adic deficits and the constants used in the paper (paper/main.pdf).

conj2: P_{k,r}(n) = (kn+1)(kn+2)...(kn+r), k in {1,2,3}; constant C = ((24r)!)^r.
conj4: Q_r(n) = prod_{i=0}^{r} (8n-(2i+1)) (integers, may be negative); constant K = ((6r+3)!)^(r+1).
Reports, for each (k,r) / r, the empirical minimal constant prod_p p^(max_n deficit_p),
checks every deficit is <= v_p(constant), and checks exact divisibility for small n.
Usage: python verify2.py [N] [RMAX]
"""
import sys
from math import factorial

N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
RMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6


def phi(T):
    return T // 3 + T // 24 - T // 6 - T // 8 - T // 12


def vpa(n, p):
    s, q = 0, p
    while q <= 24 * n:
        s += phi(24 * n // q)
        q *= p
    return s


def vp(m, p):
    m = abs(m)
    e = 0
    while m % p == 0:
        m //= p
        e += 1
    return e


def primes_upto(x):
    s = bytearray([1]) * (x + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(x ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(x + 1) if s[i]]


def factor(m):
    m = abs(m)
    out = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            out[d] = out.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        out[m] = out.get(m, 0) + 1
    return out


def vp_fact(m, p):
    s, q = 0, p
    while q <= m:
        s += m // q
        q *= p
    return s


def a_exact(n):
    return factorial(8 * n) * factorial(n) // (factorial(4 * n) * factorial(3 * n) * factorial(2 * n))


A = [a_exact(n) for n in range(0, 121)]

print("== conjecture 2")
for k in (1, 2, 3):
    for r in range(1, RMAX + 1):
        maxdef = {}
        for n in range(0, N + 1):
            vals = {}
            for i in range(1, r + 1):
                for p, e in factor(k * n + i).items():
                    vals[p] = vals.get(p, 0) + e
            for p, e in vals.items():
                d = e - vpa(n, p)
                if d > maxdef.get(p, 0):
                    maxdef[p] = d
        Cmin = 1
        for p, d in maxdef.items():
            Cmin *= p ** d
            assert d <= r * vp_fact(24 * r, p), (k, r, p, d)
            assert p <= 24 * r, (k, r, p)
        # exact check with the empirical minimal constant and with ((24r)!)^r for n <= 120
        C = factorial(24 * r) ** r
        for n in range(0, 121):
            P = 1
            for i in range(1, r + 1):
                P *= k * n + i
            assert (Cmin * A[n]) % P == 0, (k, r, n)
            assert (C * A[n]) % P == 0
        print("k=%d r=%d  empirical C_min=%d  deficits=%s" % (k, r, Cmin, dict(sorted(maxdef.items()))))

print("== conjecture 4")
for r in range(0, RMAX + 1):
    maxdef = {}
    for n in range(0, N + 1):
        vals = {}
        for i in range(0, r + 1):
            for p, e in factor(8 * n - (2 * i + 1)).items():
                vals[p] = vals.get(p, 0) + e
        for p, e in vals.items():
            d = e - vpa(n, p)
            if d > maxdef.get(p, 0):
                maxdef[p] = d
    Kmin = 1
    for p, d in maxdef.items():
        Kmin *= p ** d
        assert d <= (r + 1) * vp_fact(6 * r + 3, p), (r, p, d)
        assert p <= 6 * r + 3 and p % 2 == 1, (r, p)
    K = factorial(6 * r + 3) ** (r + 1)
    for n in range(0, 121):
        Q = 1
        for i in range(0, r + 1):
            Q *= 8 * n - (2 * i + 1)
        assert (Kmin * A[n]) % Q == 0, (r, n)
        assert (K * A[n]) % Q == 0
    print("r=%d  empirical K_min=%d  deficits=%s" % (r, Kmin, dict(sorted(maxdef.items()))))
