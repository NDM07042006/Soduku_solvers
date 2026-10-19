from math import ceil, log2, sqrt, isqrt


# ---------- helpers ----------
def var_id(r, c, v, n):
    """Variable for 'cell (r,c) has value v' (r, c, v are 0-based). IDs start at 1."""
    return r * n * n + c * n + v + 1


def alo(lits):
    return [list(lits)]


# ---------- AMO encodings: all share the signature (lits, next_var) -> (clauses, next_var) ----------
def pairwise_amo(lits, next_var=None):
    clauses = []
    for i in range(len(lits)):
        for j in range(i + 1, len(lits)):
            clauses.append([-lits[i], -lits[j]])
    return clauses, next_var


def sequential_amo(lits, next_var):
    n = len(lits)
    if n <= 1:
        return [], next_var

    s = list(range(next_var, next_var + n - 1))
    clauses = [[-lits[0], s[0]]]
    for i in range(1, n - 1):
        clauses.append([-lits[i], s[i]])
        clauses.append([-s[i - 1], s[i]])
        clauses.append([-lits[i], -s[i - 1]])
    clauses.append([-lits[n - 1], -s[n - 2]])

    return clauses, next_var + n - 1


def commander_amo(lits, next_var, group_size=3):
    n = len(lits)
    if n <= 1:
        return [], next_var
    if n <= group_size:
        return pairwise_amo(lits)[0], next_var

    clauses, commanders = [], []
    for i in range(0, n, group_size):
        group = lits[i:i + group_size]
        if len(group) == 1:
            commanders.append(group[0])
            continue
        clauses += pairwise_amo(group)[0]
        c = next_var
        next_var += 1
        clauses += [[-l, c] for l in group]
        commanders.append(c)

    sub, next_var = commander_amo(commanders, next_var, group_size)
    return clauses + sub, next_var


def product_amo(lits, next_var, base=6):
    n = len(lits)
    if n <= 1:
        return [], next_var
    if n <= base:
        return pairwise_amo(lits)[0], next_var

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


def binary_amo(lits, next_var):
    n = len(lits)
    if n <= 1:
        return [], next_var

    m = ceil(log2(n))
    bits = list(range(next_var, next_var + m))

    clauses = []
    for i, x in enumerate(lits):
        for k in range(m):
            clauses.append([-x, bits[k] if (i >> k) & 1 else -bits[k]])

    return clauses, next_var + m


# ---------- dispatch ----------
AMO_ENCODINGS = {
    "pairwise": pairwise_amo,
    "sequential": sequential_amo,
    "commander": commander_amo,
    "product": product_amo,
    "binary": binary_amo,
}


def exactly_one(lits, encoding, next_var):
    """ALO + selected AMO encoding."""
    key = encoding.lower()
    if key not in AMO_ENCODINGS:
        raise ValueError(f"encoding must be one of {list(AMO_ENCODINGS)}")

    amo_clauses, next_var = AMO_ENCODINGS[key](lits, next_var)
    return alo(lits) + amo_clauses, next_var


# ---------- Sudoku ----------
def sudoku_clauses(grid, encoding="pairwise"):
    """
    Convert a Sudoku grid into CNF clauses (0 = empty cell).
    encoding: "pairwise", "sequential", "commander", "product", or "binary".

    Returns:
        clauses: CNF clauses
        max_var: largest variable ID used
    """
    n = len(grid)
    box_size = isqrt(n)

    if box_size * box_size != n:
        raise ValueError("Sudoku size must be a perfect square")
    if any(len(row) != n for row in grid):
        raise ValueError("grid must be an n x n matrix")
    if any(value < 0 or value > n for row in grid for value in row):
        raise ValueError(f"Cell values must be between 0 and {n}")
    if encoding.lower() not in AMO_ENCODINGS:
        raise ValueError(f"encoding must be one of {list(AMO_ENCODINGS)}")

    clauses = []
    next_var = n ** 3 + 1  # primary variables occupy 1..n^3

    def add_exactly_one(lits):
        nonlocal next_var
        new_clauses, next_var = exactly_one(lits, encoding, next_var)
        clauses.extend(new_clauses)

    # 1. Cell: exactly one value
    for r in range(n):
        for c in range(n):
            add_exactly_one([var_id(r, c, v, n) for v in range(n)])

    # 2. Row/value: exactly once
    for r in range(n):
        for v in range(n):
            add_exactly_one([var_id(r, c, v, n) for c in range(n)])

    # 3. Column/value: exactly once
    for c in range(n):
        for v in range(n):
            add_exactly_one([var_id(r, c, v, n) for r in range(n)])

    # 4. Box/value: exactly once
    for box_r in range(0, n, box_size):
        for box_c in range(0, n, box_size):
            for v in range(n):
                add_exactly_one([
                    var_id(r, c, v, n)
                    for r in range(box_r, box_r + box_size)
                    for c in range(box_c, box_c + box_size)
                ])

    # 5. Givens
    for r in range(n):
        for c in range(n):
            if grid[r][c] != 0:
                clauses.append([var_id(r, c, grid[r][c] - 1, n)])

    return clauses, next_var - 1


def decode(model, n):
    """Turn a SAT model (list of signed ints) into an n x n grid."""
    true_vars = {l for l in model if l > 0}
    grid = [[0] * n for _ in range(n)]
    for r in range(n):
        for c in range(n):
            for v in range(n):
                if var_id(r, c, v, n) in true_vars:
                    grid[r][c] = v + 1
    return grid