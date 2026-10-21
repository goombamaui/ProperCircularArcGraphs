"""Exact prototype of the symbolic model formalized in Lean.

Colour vectors at level k are polynomials G(y_1..y_k) over Q[E_1^{+-1}, E_2^{+-1}, ...],
standing for  sum_i x_{i_1}...x_{i_k} G(x_{i_1},..,x_{i_k}) bhat_i.
Checks the intertwining identities (M), (R), (S), (D) of the paper on small indices.
"""
import itertools
import sympy as sp
from functools import lru_cache

MAXE = 12
E = [sp.Integer(1)] + [sp.Symbol(f"E{j}") for j in range(1, MAXE + 1)]
Y = [sp.Symbol(f"y{r}") for r in range(1, 8)]


@lru_cache(None)
def P(m):
    """Power sum p_m in terms of E (Newton)."""
    assert m >= 1
    s = (-1) ** (m + 1) * m * E[m]
    for i in range(1, m):
        s -= (-1) ** i * E[i] * P(m - i)
    return sp.expand(s)


def T(s):
    s = set(s)
    return sorted({y for y in [1] + [t + 1 for t in s] if y not in s and (y == 1 or y - 1 in s)})


def Z(w):
    w = set(w)
    return sorted(z for z in w if z >= 2 and z - 1 not in w)


def A(y, s):
    s = set(s)
    if y not in T(s):
        return sp.Integer(0)
    c = sp.Integer(1) if y == 1 else sp.Rational(y, y - 1)
    for t in s:
        if t != y - 1:
            c *= sp.Rational(y - t, y - 1 - t)
    return c


# ---- colour operators (symbolic) ----
def Mhat(G, k):  # level k -> k+1
    return G


def Dhat(G, k):  # level k -> k-1
    poly = sp.Poly(sp.expand(G), Y[0])
    out = 0
    for (m,), c in poly.terms():
        out += c * (P(m + 1) - sum(Y[r] ** (m + 1) for r in range(1, k)))
    out = sp.expand(out)
    return sp.expand(out.subs({Y[r]: Y[r - 1] for r in range(1, k)}, simultaneous=True))


def Rhat(G, k):
    sub = {Y[0]: Y[k - 1]}
    sub.update({Y[r]: Y[r - 1] for r in range(1, k)})
    return sp.expand(Y[k - 1] * G.subs(sub, simultaneous=True))


def Shat(G, s):  # swap positions s, s+1 (1-based)
    return sp.expand(G.subs({Y[s - 1]: Y[s], Y[s]: Y[s - 1]}, simultaneous=True))


# ---- U ----
@lru_cache(None)
def U(sig):
    k = len(sig)
    if k == 0:
        return sp.Integer(1)
    if k == 1:
        a = sig[0]
        return sp.expand(sum((-Y[0]) ** j * E[a - 1 - j] for j in range(a)) / (a * E[a - 1]))
    w, y = sig[:-1], sig[-1]
    if y in T(w):
        return block(w)[y]
    # free equation
    rhs = sum(A(z, w) / (y - z) * U(w + (z,)) for z in T(w)) - E[y - 2] / E[y - 1] * Rhat(U((y - 1,) + w), k)
    return sp.expand(rhs / A(y, (y - 1,) + w))


@lru_cache(None)
def block(w):
    k = len(w) + 1
    Ts, Zs = T(w), Z(w)
    assert len(Ts) == len(Zs) + 1
    us = sp.symbols(f"u0:{len(Ts)}")
    eqs = [sum(A(y, w) * u for y, u in zip(Ts, us)) - Mhat(U(w), k - 1)]
    for z in Zs:
        eqs.append(sum(A(y, w) / (z - y) * u for y, u in zip(Ts, us)) - E[z - 2] / E[z - 1] * Rhat(U((z - 1,) + w), k))
    sol = sp.solve(eqs, us, dict=True)[0]
    return {y: sp.expand(sol[u]) for y, u in zip(Ts, us)}


# ---- tableau operators on basis vectors (dicts index -> coeff) ----
def Mk(sig):
    return {sig + (y,): A(y, sig) for y in T(sig)}


def Dk(sig):
    return {sig[1:]: E[sig[0]] / E[sig[0] - 1]}


def Ulin(vec):
    return sp.expand(sum(c * U(s) for s, c in vec.items()))


def apply(op, vec):
    out = {}
    for s, c in vec.items():
        for t, d in op(s).items():
            out[t] = out.get(t, 0) + c * d
    return out


def Rk(sig):
    a = apply(Dk, Mk(sig))
    b = apply(Mk, Dk(sig))
    out = dict(b)
    for t, c in a.items():
        out[t] = out.get(t, 0) - c
    return out


def Sk(s):
    def op(sig):
        d = sig[s] - sig[s - 1]
        t = list(sig)
        t[s - 1], t[s] = t[s], t[s - 1]
        return {sig: sp.Rational(1, d), tuple(t): 1 - sp.Rational(1, d)}
    return op


def indices(k, maxv):
    return [p for p in itertools.permutations(range(1, maxv + 1), k)]


def check(k, maxv):
    bad = 0
    for sig in indices(k, maxv):
        # (D)
        lhs = Dhat(U(sig), k)
        rhs = sp.expand(E[sig[0]] / E[sig[0] - 1] * U(sig[1:]))
        if sp.simplify(lhs - rhs) != 0:
            bad += 1
            print("D fails", sig)
        # (R)
        if sp.simplify(Ulin(Rk(sig)) - Rhat(U(sig), k)) != 0:
            bad += 1
            print("R fails", sig)
        # (S)
        for s in range(1, k):
            if sp.simplify(Ulin(Sk(s)(sig)) - Shat(U(sig), s)) != 0:
                bad += 1
                print("S fails", sig, s)
    for w in indices(k - 1, maxv):
        if sp.simplify(Ulin(Mk(w)) - Mhat(U(w), k - 1)) != 0:
            bad += 1
            print("M fails", w)
    print(f"k={k} maxv={maxv}: {'OK' if bad == 0 else bad}")


if __name__ == "__main__":
    check(1, 5)
    check(2, 4)
    check(3, 4)
