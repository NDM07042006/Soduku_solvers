
import argparse
import json
import os
import random
import time

BOX = 6
N = BOX * BOX  # 36
CELLS = N * N


def base_grid():
    return [[(BOX * (r % BOX) + r // BOX + c) % N + 1 for c in range(N)] for r in range(N)]


def _axis_order(rng):
    bands = list(range(BOX))
    rng.shuffle(bands)
    order = []
    for b in bands:
        idx = [b * BOX + k for k in range(BOX)]
        rng.shuffle(idx)
        order += idx
    return order


def random_solution(rng):
    g = base_grid()
    perm = list(range(1, N + 1))
    rng.shuffle(perm)
    rord, cord = _axis_order(rng), _axis_order(rng)
    g = [[perm[g[rord[r]][cord[c]] - 1] for c in range(N)] for r in range(N)]
    if rng.random() < 0.5:
        g = [list(row) for row in zip(*g)]
    return g


def is_valid_solution(g):
    full = set(range(1, N + 1))
    if any(set(row) != full for row in g):
        return False
    if any({g[r][c] for r in range(N)} != full for c in range(N)):
        return False
    for br in range(BOX):
        for bc in range(BOX):
            s = {g[br * BOX + i][bc * BOX + j] for i in range(BOX) for j in range(BOX)}
            if s != full:
                return False
    return True


def var(r, c, v):
    return r * N * N + c * N + v + 1


def build_sat_solver(name="g4"):
    from pysat.solvers import Solver

    s = Solver(name=name)
    for r in range(N):
        for c in range(N):
            s.add_clause([var(r, c, v) for v in range(N)])  # every cell has a value
    units = []
    for r in range(N):
        units.append([(r, c) for c in range(N)])
    for c in range(N):
        units.append([(r, c) for r in range(N)])
    for br in range(BOX):
        for bc in range(BOX):
            units.append([(br * BOX + i, bc * BOX + j) for i in range(BOX) for j in range(BOX)])
    for unit in units:
        for v in range(N):
            lits = [var(r, c, v) for r, c in unit]
            s.add_clause(lits)  # value appears in unit
            for i in range(N):  # at most once (pairwise)
                for j in range(i + 1, N):
                    s.add_clause([-lits[i], -lits[j]])
    return s


# ------------------------------------------------------------------ puzzle
def make_puzzle(sol, rng, target, unique=False, solver=None, budget=20000, time_limit=None):
    cells = [(r, c) for r in range(N) for c in range(N)]
    rng.shuffle(cells)
    stats = dict(unique_guaranteed=unique, proven_removals=0, kept_unknown=0, kept_not_unique=0,
                 timed_out=False)

    if not unique:
        keep = set(cells[:target])
        puzzle = [[sol[r][c] if (r, c) in keep else 0 for c in range(N)] for r in range(N)]
        return puzzle, stats

    givens = set(cells)
    t0 = time.time()
    for (r, c) in cells:
        if len(givens) <= target:
            break
        if time_limit and time.time() - t0 > time_limit:
            stats["timed_out"] = True
            break
        d = sol[r][c] - 1
        assumptions = [var(rr, cc, sol[rr][cc] - 1) for (rr, cc) in givens if (rr, cc) != (r, c)]
        assumptions.append(-var(r, c, d))  # force a DIFFERENT value in the cleared cell
        solver.conf_budget(budget)
        res = solver.solve_limited(assumptions=assumptions)
        if res is False:
            givens.discard((r, c))
            stats["proven_removals"] += 1
        elif res is None:
            stats["kept_unknown"] += 1
        else:
            stats["kept_not_unique"] += 1
    puzzle = [[sol[r][c] if (r, c) in givens else 0 for c in range(N)] for r in range(N)]
    return puzzle, stats


_SOLVER_CACHE = {}


def generate_puzzle36x36(givens=450, seed=None, unique=False, with_solution=False, flat=False,
                    budget=20000, time_limit=None, sat_solver="g4"):

    rng = random.Random(seed)
    sol = random_solution(rng)
    solver = None
    if unique:
        if sat_solver not in _SOLVER_CACHE:  # build the SAT model once, reuse across calls
            _SOLVER_CACHE[sat_solver] = build_sat_solver(sat_solver)
        solver = _SOLVER_CACHE[sat_solver]
    puzzle, _ = make_puzzle(sol, rng, givens, unique, solver, budget, time_limit)
    if flat:
        puzzle = [v for row in puzzle for v in row]
        sol = [v for row in sol for v in row]
    return (puzzle, sol) if with_solution else puzzle


def write_grid(path, g):
    with open(path, "w") as f:
        for row in g:
            f.write(" ".join(map(str, row)) + "\n")



n= generate_puzzle36x36(givens=300)
print(n)