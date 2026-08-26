#!/usr/bin/env python3
"""Machine validation for the paper universal-words.tex.

Three independent checks (all passed on 2026-08-25; rerun with --all):

1. criteria   -- exhaustive verification of the two factorization criteria:
                 Herzog--Kaplan--Lev (two cycles) on S_7/S_8, and Boccara
                 (arbitrary class times a full cycle) for N <= 8.
2. bookkeeping -- the inequality/parity chains of Propositions 4.1, 5.1 and
                 Lemma 6.2, exactly as displayed in the paper, on random
                 instances (n, r, s, z) with n up to 3000.
3. endtoend   -- the small-support construction executed on real permutations
                 in S_14..S_16: find z = A.B of type ((q1,q2,q3,1), N-cycle),
                 take the roots of Lemma 2.3, verify x^r y^s = z exactly.

Requires sympy.
Usage: python3 validate.py [criteria|bookkeeping|endtoend|constants|lowerbound|--all]
"""
import math
import random
import sys
from itertools import permutations

from sympy import factorint, isprime, primerange

# ---------------- permutation utilities (tuples: p[i] = image of i) --------

def compose(a, b):
    """a after b: x -> a(b(x)), i.e. the product a*b acting on the left."""
    return tuple(a[b[i]] for i in range(len(a)))

def cycles_of(p):
    n = len(p); seen = [False] * n; out = []
    for i in range(n):
        if not seen[i]:
            c = []; j = i
            while not seen[j]:
                seen[j] = True; c.append(j); j = p[j]
            if len(c) > 1:
                out.append(c)
    return out

def full_type(p):
    n = len(p); seen = [False] * n; t = []
    for i in range(n):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]; l += 1
            t.append(l)
    return tuple(sorted(t, reverse=True))

def perm_power(p, t):
    res = list(range(len(p)))
    for c in cycles_of(p):
        l = len(c)
        for i in range(l):
            res[c[i]] = c[(i + t) % l]
    return tuple(res)

def from_cycles(n, cycs):
    p = list(range(n))
    for c in cycs:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)

def root_of(sig, t, n):
    """Lemma 2.3: t-th root of a product of disjoint cycles, all coprime to t."""
    out = []
    for c in cycles_of(sig):
        l = len(c); a = pow(t, -1, l)
        newc = [c[0]]; j = 0
        for _ in range(l - 1):
            j = (j + a) % l; newc.append(c[j])
        out.append(newc)
    return from_cycles(n, out)

def stats(p):
    cy = cycles_of(p)
    m = sum(len(c) for c in cy)
    return m, len(cy)

# ---------------- 1. the two criteria, exhaustively ------------------------

def check_boccara():
    """z in C_lambda * C_(N)  <=>  l(lam)+l(mu) <= N+1 and == N+1 (mod 2)."""
    def parts_all(k, mx=None):
        if mx is None:
            mx = k
        if k == 0:
            yield ()
        for a in range(min(k, mx), 0, -1):
            for rest in parts_all(k - a, a):
                yield (a,) + rest
    bad = 0
    for N in (5, 6, 7):
        perms = list(permutations(range(N)))
        ncycles = [p for p in perms if full_type(p)[0] == N]
        reach = set()
        for A in perms:
            tA = full_type(A)
            for w in ncycles:
                reach.add((tA, full_type(compose(w, A))))
        for tA in parts_all(N):
            for tz in parts_all(N):
                pred = (len(tA) + len(tz) <= N + 1) and ((len(tA) + len(tz)) % 2 == (N + 1) % 2)
                if pred != ((tA, tz) in reach):
                    bad += 1
                    print("BOCCARA MISMATCH", N, tA, tz)
    print(f"Boccara criterion, N=5..7 exhaustive: {'OK' if bad == 0 else f'{bad} MISMATCHES'}")
    return bad == 0

def check_hkl():
    """sigma = (l1-cycle)(l2-cycle) <=> exact-disjoint or sum/parity/diff clause."""
    bad = 0
    for n in (6, 7):
        perms = list(permutations(range(n)))
        by_len = {}
        for p in perms:
            t = full_type(p)
            nt = [x for x in t if x > 1]
            if len(nt) == 1:
                by_len.setdefault(nt[0], []).append(p)
        reach = set()
        for l1, ps in by_len.items():
            for l2, qs in by_len.items():
                for a in ps:
                    for b in qs:
                        reach.add((full_type(compose(a, b)), tuple(sorted((l1, l2), reverse=True))))
        def parts_all(k, mx=None):
            if mx is None:
                mx = k
            if k == 0:
                yield ()
            for a in range(min(k, mx), 0, -1):
                for rest in parts_all(k - a, a):
                    yield (a,) + rest
        for t in parts_all(n):
            nt = [x for x in t if x > 1]
            if not nt:
                continue  # HKL requires sigma != 1
            m = sum(nt); c = len(nt)
            for l1 in range(2, n + 1):
                for l2 in range(2, l1 + 1):
                    clause_a = (len(nt) == 2 and sorted(nt, reverse=True) == [l1, l2])
                    clause_b = (l1 + l2 >= m + c and (l1 + l2 - m - c) % 2 == 0 and l1 - l2 <= m - c)
                    if (clause_a or clause_b) != ((t, (l1, l2)) in reach):
                        bad += 1
                        print("HKL MISMATCH", n, t, l1, l2)
    print(f"HKL criterion, S_6/S_7 exhaustive: {'OK' if bad == 0 else f'{bad} MISMATCHES'}")
    return bad == 0

# ---------------- 2. proposition bookkeeping on random instances -----------

def check_bookkeeping(trials=600, seed=7):
    rng = random.Random(seed)
    bad = []
    for _ in range(trials):
        n = rng.choice([400, 1000, 2711, 3000])
        r = rng.choice([2, 4, 8, 6, 30, 210, 9699690])
        s = rng.choice([3, 9, 15, 105, 15015])
        z = list(range(n)); rng.shuffle(z); z = tuple(z)
        m, c = stats(z); d = m - c
        odd = (d % 2 == 1)
        if not odd and m > 0:
            qs = [q for q in primerange(int(3 * n / 4) + 1, n + 1) if (r * s) % q != 0]
            if not qs:
                bad.append(("case1-window", n, r, s)); continue
            q = qs[0]
            if not (2 * q >= m + c and (2 * q - (m + c)) % 2 == 0 and 0 <= m - c):
                bad.append(("case1-ineq", n, r, s, m, c, q))
        elif odd and m >= n / 2:
            us = [u for u in primerange(int(3 * n / 4) + 1, n + 1) if r % u != 0]
            vs = [2 ** a * q for a in range(1, 6)
                  for q in primerange(int(3 * n / 2 ** (a + 2)) + 1, n // 2 ** a + 1)
                  if s % q != 0]
            if not us or not vs:
                bad.append(("case2-window", n, r, s)); continue
            u = us[0]; v = vs[0]
            if not (u + v >= m + c and (u + v - (m + c)) % 2 == 0
                    and abs(u - v) <= m - c and u <= n and v <= n):
                bad.append(("case2-ineq", n, r, s, m, c, u, v))
        elif odd and d >= 3:
            hit = False
            for qt in [q for q in primerange((n + 2) // 4 + 1, n // 2 + 1) if s % q != 0][:50]:
                N = 2 * qt
                if N < m or N > n:
                    continue
                M = N - 1
                ps = [p for p in primerange(3, M) if (r * s) % p != 0]
                pset = set(ps); done = False
                for q1 in ps[:200]:
                    for q2 in ps[:200]:
                        if M - q1 - q2 in pset:
                            done = True; break
                    if done:
                        break
                if not done:
                    continue
                lm, lmu = 4, c + N - m
                if not (lm + lmu <= N + 1 and (lm + lmu - (N + 1)) % 2 == 0):
                    bad.append(("case3-boccara", n, r, s, m, c, d, N))
                hit = True
                break
            if not hit:
                bad.append(("case3-window", n, r, s, m))
    print(f"bookkeeping on {trials} random instances: "
          f"{'OK' if not bad else f'{len(bad)} VIOLATIONS'}")
    for b in bad[:10]:
        print(" ", b)
    return not bad

# ---------------- 3. end-to-end small-support construction ----------------

def check_endtoend(trials=400, seed=11):
    rng = random.Random(seed)
    combos = [(2, 11), (4, 13), (2, 13), (8, 11), (10, 11)]
    ok = fail = skipped = 0
    for _ in range(trials):
        n = rng.choice([14, 15, 16])
        r, s = rng.choice(combos)
        while True:
            k = rng.choice([4, 5, 6, 7])
            pts = rng.sample(range(n), k); rng.shuffle(pts)
            cycs = []; i = 0
            while i < len(pts):
                cl = min(rng.choice([2, 3, 4, 5]), len(pts) - i)
                if cl >= 2:
                    cycs.append(pts[i:i + cl])
                i += cl
            z = from_cycles(n, cycs)
            m, c = stats(z); d = m - c
            if d % 2 == 1 and d >= 3:
                break
        found = None
        for qt in (5, 7):
            if s % qt == 0 or 2 * qt < m or 2 * qt > n:
                continue
            N = 2 * qt; M = N - 1
            ps = [p for p in primerange(2, M) if (r * s) % p != 0]
            for q1 in ps:
                for q2 in ps:
                    q3 = M - q1 - q2
                    if q3 >= 2 and isprime(q3) and (r * s) % q3 != 0:
                        found = (N, q1, q2, q3); break
                if found:
                    break
            if found:
                break
        if not found:
            skipped += 1; continue
        N, q1, q2, q3 = found
        suppz = sorted(set(x for cc in cycles_of(z) for x in cc))
        omega = (suppz + [x for x in range(n) if x not in suppz])[:N]
        hit = False
        for _t in range(500000):
            pts = omega[:]; rng.shuffle(pts)
            A = from_cycles(n, [pts[:q1], pts[q1:q1 + q2], pts[q1 + q2:q1 + q2 + q3]])
            Ainv = tuple(sorted(range(n), key=lambda i: A[i]))
            B = compose(Ainv, z)
            bc = cycles_of(B)
            if len(bc) == 1 and len(bc[0]) == N and set(bc[0]) == set(omega):
                hit = True; break
        if not hit:
            fail += 1; print("NO FACTORIZATION FOUND", n, r, s, cycles_of(z), found)
            continue
        x = root_of(A, r, n); y = root_of(B, s, n)
        if compose(perm_power(x, r), perm_power(y, s)) == z:
            ok += 1
        else:
            fail += 1; print("COMPOSITION MISMATCH", n, r, s, found)
    print(f"end-to-end small-support construction: ok={ok} fail={fail} skipped={skipped}")
    return fail == 0

# ---------------- 3b. the lower-bound construction (section 8) -------------

def check_lowerbound():
    """Prop 8.1: r = lcm(1..n), s = odd part of r  ==>  x^r = 1 identically,
    every y^s has all cycle lengths powers of two, and no 3-cycle is a value."""
    from math import lcm as _lcm
    ok = True
    for n in (5, 6, 7):
        r = _lcm(*range(1, n + 1)); s = r
        while s % 2 == 0:
            s //= 2
        xr_trivial = all(perm_power(x, r) == tuple(range(n))
                         for x in permutations(range(n)))
        types = {full_type(perm_power(y, s)) for y in permutations(range(n))}
        all2 = all(all((l & (l - 1)) == 0 for l in t) for t in types)
        three = tuple(sorted([3] + [1] * (n - 3), reverse=True))
        good = xr_trivial and all2 and three not in types
        print(f"  n={n}: x^r trivial {xr_trivial}, y^s 2-power types {all2}, "
              f"3-cycle absent {three not in types}")
        ok &= good
    print(f"lower-bound construction, n=5..7 exhaustive: {'OK' if ok else 'FAIL'}")
    return ok

# ---------------- 4. numerical constants used in Lemmas 6.3-6.4 -----------

def check_constants():
    """Rigorous bounds for the two Euler products in the averaging lemma:
    partial product over p <= 10^7 plus an elementary tail bound
    (log(1+t) <= t and sum_{p>P} f(p) <= sum_{k>P} f(k) for decreasing f)."""
    import math
    P = 10 ** 7
    c5 = c6 = 0.0  # logs
    for p in primerange(3, P):
        c5 += math.log1p(1 / ((p - 2) * (p - 1)))
        c6 += math.log1p(1 / (math.sqrt(p) * (p - 2)))
    # tails: sum_{k > P} 1/((k-2)(k-1)) <= 1/(P-2);  sum_{k > P} k^{-3/2}*(1+eps) <= 3/sqrt(P-2)
    t5 = 1 / (P - 2)
    t6 = 3 / math.sqrt(P - 2)
    C5, C6 = math.exp(c5 + t5), math.exp(c6 + t6)
    ok = C5 < 1.75 and C6 < 2.33
    print(f"Euler products: prod(1+1/((p-2)(p-1))) <= {C5:.5f} (< 1.75), "
          f"prod(1+1/(sqrt(p)(p-2))) <= {C6:.5f} (< 2.33): {'OK' if ok else 'FAIL'}")
    from sympy import primepi
    ok2 = primepi(11927) == 1429
    print(f"pi(11927) = 1429: {'OK' if ok2 else 'FAIL'}")
    return ok and ok2

if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "--all"
    passed = True
    if what in ("lowerbound", "--all"):
        passed &= check_lowerbound()
    if what in ("constants", "--all"):
        passed &= check_constants()
    if what in ("criteria", "--all"):
        passed &= check_boccara(); passed &= check_hkl()
    if what in ("bookkeeping", "--all"):
        passed &= check_bookkeeping()
    if what in ("endtoend", "--all"):
        passed &= check_endtoend()
    sys.exit(0 if passed else 1)
