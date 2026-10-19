#!/usr/bin/env python3
"""
36x36 Sudoku puzzle generator.

Pipeline:
  1. Solution : closed-form base pattern, then validity-preserving shuffles
                (symbols, rows within band, columns within stack, bands, stacks, transpose)
  2. Removal  : keep a target number of givens
                - default      : random removal (fast; puzzle is satisfiable but NOT guaranteed unique)
                - --unique     : greedy removal, each removal proven safe by a PySAT incremental check
                                 (needs `pip install python-sat`)

Uniqueness check (incremental, one solver reused for all cells/puzzles):
  puzzle stays unique after clearing cell (r,c) with solution value d  <=>
  SAT solver says UNSAT for: [remaining givens as assumptions] + [NOT x(r,c,d)].
  If the solver hits its conflict budget (result unknown) the given is kept, so any puzzle
  produced with --unique is guaranteed unique (it may just keep more givens than the target).

Examples:
  python gen36.py -n 5 --seed 1 --frac 0.5                 # 5 random-removal puzzles, 50% givens
  python gen36.py -n 3 --seed 1 --givens 700 --unique      # unique puzzles, aim for 700 givens
  python gen36.py -n 1 --unique --givens 0 --time-limit 600  # remove as much as possible (<=10 min)

Output (in --out, default ./puzzles36): puzzle_<seed>.txt, solution_<seed>.txt, meta.json
Format: 36 lines, 36 space-separated integers per line, 0 = empty cell.
"""

import argparse
import json
import os
import random
import time

BOX = 6
N = BOX * BOX  # 36
CELLS = N * N


# ------------------------------------------------------------------ solution
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


# ------------------------------------------------------------------ SAT
def var(r, c, v):
    """DIMACS variable for 'cell (r,c) has value v+1' (v is 0-based)."""
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
    # Cell at-most-one is implied (every row has 36 cells, 36 values, each value at most once).
    return s


# ------------------------------------------------------------------ puzzle
def make_puzzle(sol, rng, target, unique=False, solver=None, budget=20000, time_limit=None):
    """Return (puzzle, stats). puzzle[r][c] == 0 means empty."""
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
        if res is False:  # no other solution -> still unique, remove given
            givens.discard((r, c))
            stats["proven_removals"] += 1
        elif res is None:  # budget exhausted -> cannot prove, keep given
            stats["kept_unknown"] += 1
        else:  # a second solution exists
            stats["kept_not_unique"] += 1
    puzzle = [[sol[r][c] if (r, c) in givens else 0 for c in range(N)] for r in range(N)]
    return puzzle, stats


_SOLVER_CACHE = {}


def generate_puzzle36x36(givens=450, seed=None, unique=False, with_solution=False, flat=False,
                    budget=20000, time_limit=None, sat_solver="g4"):
    """Return a 36x36 puzzle as a list of 36 lists (0 = empty cell).

    givens        : target number of givens (648 = 50%). With unique=True the result may keep
                    more givens than requested if removals cannot be proven safe in time.
    seed          : int for reproducible output (None = random).
    unique        : guarantee a unique solution using PySAT (slower).
    with_solution : return (puzzle, solution) instead of just the puzzle.
    flat          : return flat lists of 1296 ints instead of 36 lists of 36.

    Example:
        import gen36
        p = gen36.generate_puzzle(700, seed=1, unique=True)
        p[0]  # first row, a list of 36 ints
    """
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


def main():
    ap = argparse.ArgumentParser(description="36x36 Sudoku generator")
    ap.add_argument("-n", "--count", type=int, default=1)
    ap.add_argument("--seed", type=int, default=0, help="base seed; puzzle i uses seed+i")
    ap.add_argument("--frac", type=float, default=0.5, help="fraction of cells kept as givens")
    ap.add_argument("--givens", type=int, default=None,
                    help="absolute number of givens (overrides --frac; 0 = remove as much as possible with --unique)")
    ap.add_argument("--unique", action="store_true", help="guarantee uniqueness via PySAT")
    ap.add_argument("--budget", type=int, default=20000, help="conflict budget per uniqueness check")
    ap.add_argument("--time-limit", type=float, default=None, help="seconds of removal per puzzle (--unique)")
    ap.add_argument("--sat-solver", default="g4", help="PySAT solver name (g4=Glucose4, m22=MiniSat)")
    ap.add_argument("--out", default="puzzles36")
    a = ap.parse_args()

    target = a.givens if a.givens is not None else round(a.frac * CELLS)
    os.makedirs(a.out, exist_ok=True)

    solver = None
    if a.unique:
        t = time.time()
        print("building SAT model (one time, may take a while)...", flush=True)
        solver = build_sat_solver(a.sat_solver)
        print("  done in %.1fs" % (time.time() - t), flush=True)

    meta = []
    for i in range(a.count):
        seed = a.seed + i
        rng = random.Random(seed)
        sol = random_solution(rng)
        assert is_valid_solution(sol)
        t = time.time()
        puzzle, stats = make_puzzle(sol, rng, target, a.unique, solver, a.budget, a.time_limit)
        n_given = sum(1 for row in puzzle for v in row if v)
        write_grid(os.path.join(a.out, "puzzle_%d.txt" % seed), puzzle)
        write_grid(os.path.join(a.out, "solution_%d.txt" % seed), sol)
        rec = dict(seed=seed, givens=n_given, target=target, seconds=round(time.time() - t, 2), **stats)
        meta.append(rec)
        print(rec, flush=True)

    with open(os.path.join(a.out, "meta.json"), "w") as f:
        json.dump(meta, f, indent=2)

n= generate_puzzle36x36(givens=300)
print(n)