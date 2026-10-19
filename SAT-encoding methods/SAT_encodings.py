from itertools import combinations, product
from math import ceil, sqrt


def alo(lits):
    return [list(lits)]


def pairwise_amo(lits):
    return [[-a, -b] for a, b in combinations(lits, 2)]


def pairwise_exactly_one(lits):
    return alo(lits) + pairwise_amo(lits)


def _start_var(lits, next_var):
    return next_var if next_var is not None else max(abs(l) for l in lits) + 1


def sequential_amo(lits, next_var=None):
    n = len(lits)
    if n <= 1:
        return [], next_var
    next_var = _start_var(lits, next_var)

    s = list(range(next_var, next_var + n - 1))
    clauses = [[-lits[0], s[0]]]
    for i in range(1, n - 1):
        clauses.append([-lits[i], s[i]])
        clauses.append([-s[i - 1], s[i]])
        clauses.append([-lits[i], -s[i - 1]])
    clauses.append([-lits[n - 1], -s[n - 2]])
    return clauses, next_var + n - 1


def commander_amo(lits, next_var=None, group_size=3):
    """
    Commander Encoding for AMO (Klieber & Kwon).

    Split literals into groups of `group_size`. Inside a group use pairwise AMO.
    Each group gets a commander variable c with (l -> c) for every l in the group.
    Then recursively enforce AMO over the commanders.
    """
    assert group_size >= 2, "group_size must be >= 2 for the recursion to terminate"
    n = len(lits)
    if n <= 1:
        return [], next_var
    next_var = _start_var(lits, next_var)

    if n <= group_size:
        return pairwise_amo(lits), next_var

    clauses, commanders = [], []
    for i in range(0, n, group_size):
        group = lits[i:i + group_size]
        if len(group) == 1:
            commanders.append(group[0])      # singleton group: literal is its own commander
            continue
        clauses += pairwise_amo(group)
        c = next_var
        next_var += 1
        clauses += [[-l, c] for l in group]  # l -> c (enough for AMO)
        commanders.append(c)

    sub, next_var = commander_amo(commanders, next_var, group_size)
    return clauses + sub, next_var


def product_amo(lits, next_var=None, base=6):
    """
    Product Encoding for AMO (Chen, 2010).

    Place literals in a p x q grid (p = ceil(sqrt(n)), q = ceil(n/p)).
    Row variables u_i and column variables v_j; literal at (i, j) implies u_i and v_j.
    Two distinct literals differ in a row or a column, so AMO over u and over v
    (applied recursively) forbids them being true together.
    """
    n = len(lits)
    if n <= 1:
        return [], next_var
    next_var = _start_var(lits, next_var)

    if n <= base:
        return pairwise_amo(lits), next_var

    p = ceil(sqrt(n))
    q = ceil(n / p)

    u = list(range(next_var, next_var + p))
    next_var += p
    v = list(range(next_var, next_var + q))
    next_var += q

    clauses = []
    for idx, x in enumerate(lits):
        i, j = divmod(idx, q)
        clauses.append([-x, u[i]])
        clauses.append([-x, v[j]])

    sub_u, next_var = product_amo(u, next_var, base)
    sub_v, next_var = product_amo(v, next_var, base)
    return clauses + sub_u + sub_v, next_var

from math import ceil, log2

def binary_amo(lits, next_var=None):
    """
    Binary (bitwise) Encoding for AMO (Frisch & Giannaros).

    Give literal i the index i in binary. Introduce m = ceil(log2 n) auxiliary
    bit variables b_0..b_{m-1}. If x_i is true, the b's must spell out i:
        x_i -> b_k      if bit k of i is 1
        x_i -> not b_k  if bit k of i is 0
    Two different literals have different indices, so some bit conflicts
    and they can't both be true.
    """
    n = len(lits)
    if n <= 1:
        return [], next_var
    next_var = _start_var(lits, next_var)

    m = ceil(log2(n))
    bits = list(range(next_var, next_var + m))

    clauses = []
    for i, x in enumerate(lits):
        for k in range(m):
            clauses.append([-x, bits[k] if (i >> k) & 1 else -bits[k]])

    return clauses, next_var + m


def exactly_one(lits, amo_fn=pairwise_amo, next_var=None, **kw):
    """ALO + any AMO encoding. Returns (clauses, next_var)."""
    if amo_fn is pairwise_amo:
        return alo(lits) + pairwise_amo(lits), next_var
    amo, next_var = amo_fn(lits, next_var, **kw)
    return alo(lits) + amo, next_var


# ---------- brute-force correctness check ----------
def check_amo(amo_fn, n, **kw):
    lits = list(range(1, n + 1))
    clauses, nv = amo_fn(lits, n + 1, **kw)
    aux = list(range(n + 1, nv)) if nv else []

    def sat(assign):
        return all(any(assign[abs(l)] == (l > 0) for l in c) for c in clauses)

    for bits in product([False, True], repeat=n):
        base = {i + 1: b for i, b in enumerate(bits)}
        ok = any(sat({**base, **dict(zip(aux, ab))})
                 for ab in product([False, True], repeat=len(aux)))
        assert ok == (sum(bits) <= 1), (amo_fn.__name__, n, bits)


if __name__ == "__main__":
    for n in range(2, 10):
        check_amo(sequential_amo, n)
        check_amo(commander_amo, n, group_size=3)
        check_amo(product_amo, n, base=3)
    print("all AMO encodings OK")