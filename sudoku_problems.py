#!/usr/bin/env python3
"""
Sudoku generator with 5 difficulty levels for 4x4, 9x9 and 16x16 boards,
following the "dig-hole" approach of Team #3485,
"Sudoku Puzzles Generating: from Easy to Evil".

Pipeline (paper section 5):
  1. Terminal pattern  : Las Vegas algorithm (random givens + randomized DFS, retry on failure)
  2. Digging holes     : - Operator 1: dig sequence depends on level
                         - Operator 2: restrictions (total givens bound, min givens per row/col)
                         - Operator 3: uniqueness by reduction to absurdity
                         - Operator 4: pruning (each cell is tried once, never refilled)
                         - Operator 5: equivalent propagation (relabel digits, swap rows/cols/bands...)
  3. Grading           : 4 weighted factors (givens, row/col lower bound, human technique, DFS search count)

Usage:
    python sudoku_generator.py                       # one 9x9 puzzle for each of the 5 levels
    python sudoku_generator.py --size 4              # 4x4 puzzles
    python sudoku_generator.py --size 16 -l 2        # one 16x16 Easy puzzle
    python sudoku_generator.py -l 3 -n 2 --seed 42 -s

In code:
    import sudoku_generator as sg
    p = sg.generate_puzzle(2)             # 9x9 Easy, plain list of lists (0 = empty)
    p = sg.generate_puzzle(2, size=4)     # 4x4 Easy
    p = sg.generate_puzzle(3, size=16)    # 16x16 Medium

Notes for sizes other than 9: the given-count ranges and the per-row/column minimums of the paper
(which are defined for 9x9) are scaled proportionally to the board size.
"""

import argparse
import random
import sys
import time
from itertools import combinations
from math import isqrt

sys.setrecursionlimit(10000)


# --------------------------------------------------------------------------- #
# Board geometry (works for any perfect-square size; 4, 9 and 16 are supported)
# --------------------------------------------------------------------------- #
class Geometry:
    def __init__(self, size):
        box = isqrt(size)
        if box * box != size or size not in (4, 9, 16):
            raise ValueError("size must be 4, 9 or 16")
        self.box, self.n, self.cells = box, size, size * size
        n = size
        self.all = (1 << n) - 1  # bitmask of all digits
        self.row = [i // n for i in range(self.cells)]
        self.col = [i % n for i in range(self.cells)]
        self.blk = [(i // n // box) * box + (i % n) // box for i in range(self.cells)]
        self.pop = [bin(m).count("1") for m in range(1 << n)]
        self.row_units = [[r * n + c for c in range(n)] for r in range(n)]
        self.col_units = [[r * n + c for r in range(n)] for c in range(n)]
        self.box_units = [
            [(br * box + r) * n + bc * box + c for r in range(box) for c in range(box)]
            for br in range(box)
            for bc in range(box)
        ]
        self.units = self.row_units + self.col_units + self.box_units
        self.peers = []
        for i in range(self.cells):
            s = set(self.row_units[self.row[i]]) | set(self.col_units[self.col[i]]) | set(
                self.box_units[self.blk[i]])
            s.discard(i)
            self.peers.append(sorted(s))


_GEOMS = {}


def get_geometry(size):
    if size not in _GEOMS:
        _GEOMS[size] = Geometry(size)
    return _GEOMS[size]


def geom_of(grid):
    """Geometry that matches a flat grid (16, 81 or 256 cells)."""
    return get_geometry(isqrt(len(grid)))


# 9x9 shortcuts (kept for convenience / backward compatibility)
_G9 = get_geometry(9)
ALL, ROW, COL, BOX, POP = _G9.all, _G9.row, _G9.col, _G9.blk, _G9.pop
ROW_UNITS, COL_UNITS, BOX_UNITS, UNITS, PEERS = (
    _G9.row_units, _G9.col_units, _G9.box_units, _G9.units, _G9.peers)

# --------------------------------------------------------------------------- #
# Difficulty configuration (paper Tables 1, 2, 7) -- defined for 9x9
# --------------------------------------------------------------------------- #
LEVELS = {
    #  name               givens range  min givens per row/col  dig sequence
    1: dict(name="Extremely easy", givens=(51, 60), rc_min=5, seq="random"),
    2: dict(name="Easy",           givens=(36, 49), rc_min=4, seq="random"),
    3: dict(name="Medium",         givens=(32, 35), rc_min=3, seq="jump"),
    4: dict(name="Difficult",      givens=(28, 31), rc_min=2, seq="snake"),
    5: dict(name="Evil",           givens=(22, 27), rc_min=0, seq="row"),
}

# Hand-tuned given ranges for the other sizes (values that the greedy digger can really reach;
# a 4x4 sudoku needs at least 4 givens to be unique, a 16x16 needs far more than the 9x9 ratio).
GIVENS_OTHER = {
    4: {1: (11, 12), 2: (9, 10), 3: (7, 8), 4: (6, 6), 5: (4, 5)},
    16: {1: (190, 220), 2: (150, 175), 3: (125, 145), 4: (110, 124), 5: (95, 109)},
}


def level_config(level, gm):
    cfg = dict(LEVELS[level])
    if gm.n != 9:
        cfg["givens"] = GIVENS_OTHER[gm.n][level]
        cfg["rc_min"] = round(cfg["rc_min"] * gm.n / 9)  # proportional lower bound per row/column
    return cfg


# --------------------------------------------------------------------------- #
# Solver: depth-first search with backtracking (bitmask + "fewest candidates" cell choice)
# --------------------------------------------------------------------------- #
class Solver:
    def __init__(self, grid, rng=None, node_limit=None):
        gm = self.gm = geom_of(grid)
        self.g = list(grid)
        n = gm.n
        self.rows, self.cols, self.boxes = [0] * n, [0] * n, [0] * n
        self.valid = True
        for i, v in enumerate(self.g):
            if v:
                bit = 1 << (v - 1)
                if (self.rows[gm.row[i]] | self.cols[gm.col[i]] | self.boxes[gm.blk[i]]) & bit:
                    self.valid = False
                self.rows[gm.row[i]] |= bit
                self.cols[gm.col[i]] |= bit
                self.boxes[gm.blk[i]] |= bit
        self.rng = rng
        self.node_limit = node_limit
        self.nodes = 0
        self.aborted = False
        self.solutions = []
        self.limit = 1

    def solve(self, limit=1):
        """Return up to `limit` solutions (list of flat lists)."""
        self.solutions, self.limit = [], limit
        self.nodes, self.aborted = 0, False
        if self.valid:
            self._dfs()
        return self.solutions

    def _dfs(self):
        gm, g = self.gm, self.g
        ROW_, COL_, BLK_, POP_, ALL_ = gm.row, gm.col, gm.blk, gm.pop, gm.all
        rows, cols, boxes = self.rows, self.cols, self.boxes
        best, best_mask, best_cnt = -1, 0, gm.n + 1
        for i in range(gm.cells):
            if g[i] == 0:
                avail = ALL_ & ~(rows[ROW_[i]] | cols[COL_[i]] | boxes[BLK_[i]])
                cnt = POP_[avail]
                if cnt < best_cnt:
                    best, best_mask, best_cnt = i, avail, cnt
                    if cnt <= 1:
                        break
        if best < 0:  # no empty cell -> solved
            self.solutions.append(list(g))
            return
        if best_cnt == 0:  # dead end
            return

        digits = [d for d in range(1, gm.n + 1) if (best_mask >> (d - 1)) & 1]
        if self.rng:
            self.rng.shuffle(digits)
        r, c, b = ROW_[best], COL_[best], BLK_[best]
        for d in digits:
            self.nodes += 1
            if self.node_limit and self.nodes > self.node_limit:
                self.aborted = True
                return
            bit = 1 << (d - 1)
            g[best] = d
            rows[r] |= bit
            cols[c] |= bit
            boxes[b] |= bit
            self._dfs()
            g[best] = 0
            rows[r] ^= bit
            cols[c] ^= bit
            boxes[b] ^= bit
            if self.aborted or len(self.solutions) >= self.limit:
                return


# --------------------------------------------------------------------------- #
# Step 1: terminal pattern by Las Vegas algorithm
# --------------------------------------------------------------------------- #
def _random_givens(rng, gm, n):
    g = [0] * gm.cells
    for i in rng.sample(range(gm.cells), n):
        used = 0
        for p in gm.peers[i]:
            if g[p]:
                used |= 1 << (g[p] - 1)
        avail = [d for d in range(1, gm.n + 1) if not (used >> (d - 1)) & 1]
        if not avail:
            return None
        g[i] = rng.choice(avail)
    return g


def create_terminal_pattern(rng, n_givens=None, node_limit=None, size=9):
    """Randomly place a few givens (paper: 11 on a 9x9 board is the best trade-off), try to complete
    the grid within a small budget; if that fails, repeat (Las Vegas: always correct, random time)."""
    gm = get_geometry(size)
    if n_givens is None:
        n_givens = max(1, round(11 * gm.cells / 81))
    if node_limit is None:
        node_limit = {4: 200, 9: 3000, 16: 20000}[size]
    while True:
        g = _random_givens(rng, gm, n_givens)
        if g is None:
            continue
        sol = Solver(g, rng=rng, node_limit=node_limit).solve(1)
        if sol:
            return sol[0]


# --------------------------------------------------------------------------- #
# Step 2: digging holes
# --------------------------------------------------------------------------- #
def dig_sequence(kind, rng, size=9):
    """Operator 1: order in which cells are tried."""
    gm = get_geometry(size)
    n = gm.n
    if kind == "row":  # Sequence 1: left->right, top->bottom
        return list(range(gm.cells))
    if kind == "snake":  # Sequence 2: wandering along "S"
        return [r * n + (c if r % 2 == 0 else n - 1 - c) for r in range(n) for c in range(n)]
    if kind == "jump":  # Sequence 3: jumping one cell (checkerboard, then the other colour)
        cells = list(range(gm.cells))
        return [i for i in cells if (gm.row[i] + gm.col[i]) % 2 == 0] + [
            i for i in cells if (gm.row[i] + gm.col[i]) % 2 == 1
        ]
    seq = list(range(gm.cells))  # Sequence 4: randomize globally
    rng.shuffle(seq)
    return seq


def unique_after_dig(puzzle, idx, node_limit=None):
    """Operator 3: reduction to absurdity.
    Clear cell idx (value d). Try every other digit d' that obeys the rules; if the puzzle
    can be solved with d' there, a 2nd solution exists -> the dig is illegal.
    (If a solver run is aborted by node_limit the answer is unknown, so the dig is rejected:
    uniqueness is therefore always guaranteed.)
    Returns True (and leaves the cell empty) if the solution stays unique; else restores d."""
    gm = geom_of(puzzle)
    d = puzzle[idx]
    puzzle[idx] = 0
    used = 0
    for p in gm.peers[idx]:
        if puzzle[p]:
            used |= 1 << (puzzle[p] - 1)
    for d2 in range(1, gm.n + 1):
        if d2 == d or (used >> (d2 - 1)) & 1:
            continue
        test = list(puzzle)
        test[idx] = d2
        solver = Solver(test, node_limit=node_limit)
        if solver.solve(1) or solver.aborted:
            puzzle[idx] = d  # not unique -> refill (this cell is never tried again: pruning)
            return False
    return True


def dig_holes(terminal, level, rng):
    gm = geom_of(terminal)
    cfg = level_config(level, gm)
    lo, hi = cfg["givens"]
    bound = rng.randint(lo, hi)  # Restriction 1: random bound inside the level's range
    node_limit = None if gm.n <= 9 else 20000
    puzzle = list(terminal)
    givens = gm.cells
    row_cnt, col_cnt = [gm.n] * gm.n, [gm.n] * gm.n
    for idx in dig_sequence(cfg["seq"], rng, gm.n):  # each cell is tried at most once (Operator 4)
        if givens <= bound:
            break
        if row_cnt[gm.row[idx]] - 1 < cfg["rc_min"] or col_cnt[gm.col[idx]] - 1 < cfg["rc_min"]:
            continue  # Restriction 2: keep enough givens in every row / column
        if unique_after_dig(puzzle, idx, node_limit):
            givens -= 1
            row_cnt[gm.row[idx]] -= 1
            col_cnt[gm.col[idx]] -= 1
    return puzzle


# --------------------------------------------------------------------------- #
# Operator 5: equivalent propagation (keeps the puzzle valid and unique)
# --------------------------------------------------------------------------- #
def propagate(puzzle, solution, rng):
    gm = geom_of(puzzle)
    n, box = gm.n, gm.box
    perm = list(range(1, n + 1))
    rng.shuffle(perm)  # relabel digits

    def order():
        bands = list(range(box))
        rng.shuffle(bands)
        out = []
        for b in bands:
            rows = [b * box + k for k in range(box)]
            rng.shuffle(rows)
            out += rows
        return out

    rord, cord = order(), order()
    transpose = rng.random() < 0.5

    def transform(grid):
        res = [0] * gm.cells
        for r in range(n):
            for c in range(n):
                v = grid[rord[r] * n + cord[c]]
                res[r * n + c] = perm[v - 1] if v else 0
        if transpose:
            res = [res[c * n + r] for r in range(n) for c in range(n)]
        return res

    return transform(puzzle), transform(solution)


# --------------------------------------------------------------------------- #
# Grading (paper section 4). For sizes other than 9 the givens / row-col scores are computed on the
# 9x9-equivalent ratio; the DFS-trial thresholds are the paper's absolute numbers.
# --------------------------------------------------------------------------- #
def _score_givens(n, cells=81):
    n = n * 81 / cells
    return 1 if n > 50 else 2 if n >= 36 else 3 if n >= 32 else 4 if n >= 28 else 5


def _score_rc(m, size=9):
    m = m * 9 / size
    return 1 if m >= 5 else 2 if m >= 4 else 3 if m >= 3 else 4 if m >= 2 else 5


def _score_search(n):
    return 1 if n < 100 else 2 if n < 1000 else 3 if n < 10000 else 4 if n <= 100000 else 5


def human_technique_score(puzzle):
    """Highest technique needed (Table 3): 1 elimination/naked single, 2 lone ranger (hidden single),
    3 twins (naked pairs), 4 triplets (naked triples), 5 brute force (anything else)."""
    gm = geom_of(puzzle)
    pop, units, n = gm.pop, gm.units, gm.n
    g = list(puzzle)
    cand = [0] * gm.cells
    for i in range(gm.cells):
        if g[i] == 0:
            used = 0
            for p in gm.peers[i]:
                if g[p]:
                    used |= 1 << (g[p] - 1)
            cand[i] = gm.all & ~used

    def place(i, bit):
        g[i] = bit.bit_length()
        cand[i] = 0
        for p in gm.peers[i]:
            cand[p] &= ~bit

    hardest = 1
    while 0 in g:
        # 1) naked single
        done = False
        for i in range(gm.cells):
            if g[i] == 0 and pop[cand[i]] == 1:
                place(i, cand[i])
                done = True
                break
        if done:
            continue
        if any(g[i] == 0 and cand[i] == 0 for i in range(gm.cells)):
            return 5
        # 2) hidden single
        for unit in units:
            for d in range(n):
                bit = 1 << d
                cells = [i for i in unit if g[i] == 0 and cand[i] & bit]
                if len(cells) == 1 and not any(g[i] == d + 1 for i in unit):
                    place(cells[0], bit)
                    hardest = max(hardest, 2)
                    done = True
                    break
            if done:
                break
        if done:
            continue
        # 3/4) naked pairs / triples
        for k, score in ((2, 3), (3, 4)):
            for unit in units:
                cells = [i for i in unit if g[i] == 0 and 2 <= pop[cand[i]] <= k]
                for combo in combinations(cells, k):
                    union = 0
                    for i in combo:
                        union |= cand[i]
                    if pop[union] != k:
                        continue
                    for o in unit:
                        if g[o] == 0 and o not in combo and cand[o] & union:
                            cand[o] &= ~union
                            done = True
                    if done:
                        break
                if done:
                    break
            if done:
                hardest = max(hardest, score)
                break
        if not done:
            return 5  # needs brute force
    return hardest


class _Cap(Exception):
    pass


def dfs_search_count(puzzle, cap=100000):
    """Plain DFS (left->right, top->bottom) enumerating ALL solutions; counts successful trials."""
    gm = geom_of(puzzle)
    n = gm.n
    g = list(puzzle)
    rows, cols, boxes = [0] * n, [0] * n, [0] * n
    for i, v in enumerate(g):
        if v:
            bit = 1 << (v - 1)
            rows[gm.row[i]] |= bit
            cols[gm.col[i]] |= bit
            boxes[gm.blk[i]] |= bit
    empties = [i for i in range(gm.cells) if g[i] == 0]
    nodes = 0

    def rec(k):
        nonlocal nodes
        if k == len(empties):
            return
        i = empties[k]
        r, c, b = gm.row[i], gm.col[i], gm.blk[i]
        avail = gm.all & ~(rows[r] | cols[c] | boxes[b])
        for d in range(n):
            bit = 1 << d
            if avail & bit:
                nodes += 1
                if nodes > cap:
                    raise _Cap
                rows[r] |= bit
                cols[c] |= bit
                boxes[b] |= bit
                rec(k + 1)
                rows[r] ^= bit
                cols[c] ^= bit
                boxes[b] ^= bit

    try:
        rec(0)
    except _Cap:
        pass
    return nodes


def grade(puzzle):
    """Weighted score: 0.4*givens + 0.2*row/col bound + 0.2*technique + 0.2*search (paper Table 5)."""
    gm = geom_of(puzzle)
    n_given = sum(1 for v in puzzle if v)
    rc_min = min(
        min(sum(1 for i in u if puzzle[i]) for u in gm.row_units),
        min(sum(1 for i in u if puzzle[i]) for u in gm.col_units),
    )
    tech = human_technique_score(puzzle)
    search = dfs_search_count(puzzle)
    s = (_score_givens(n_given, gm.cells), _score_rc(rc_min, gm.n), tech, _score_search(search))
    total = 0.4 * s[0] + 0.2 * s[1] + 0.2 * s[2] + 0.2 * s[3]
    return dict(
        givens=n_given, rc_min=rc_min, technique=tech, search=search,
        scores=s, total=round(total, 2), level=min(5, max(1, int(total + 0.5))),
    )


# --------------------------------------------------------------------------- #
# Public API
# --------------------------------------------------------------------------- #
def generate(level, rng=None, max_attempts=None, size=9):
    """Generate one puzzle of the given level (1..5). Returns flat lists (puzzle, solution)."""
    rng = rng or random.Random()
    gm = get_geometry(size)
    if max_attempts is None:
        max_attempts = 40 if size <= 9 else 8
    lo, hi = level_config(level, gm)["givens"]
    best, best_dist = None, None
    for _ in range(max_attempts):
        terminal = create_terminal_pattern(rng, size=size)
        puzzle = dig_holes(terminal, level, rng)
        n = sum(1 for v in puzzle if v)
        dist = 0 if lo <= n <= hi else (n - hi if n > hi else lo - n)
        if best is None or dist < best_dist:
            best, best_dist = (puzzle, terminal), dist
        if dist == 0:
            break
    puzzle, terminal = best
    return propagate(puzzle, terminal, rng)


def generate_puzzle(level=2, rng=None, with_solution=False, size=9):
    """Return a plain size x size list of lists (0 = empty cell). Default: level 2 = Easy, 9x9.
    With with_solution=True, return (puzzle, solution) instead, both as 2D lists."""
    flat_puzzle, flat_solution = generate(level, rng, size=size)
    puzzle = [flat_puzzle[r * size:(r + 1) * size] for r in range(size)]
    if with_solution:
        return puzzle, [flat_solution[r * size:(r + 1) * size] for r in range(size)]
    return puzzle


def format_grid(grid):
    """One list per row, e.g. [8, 1, 2, 7, 5, 3, 6, 4, 9]; 0 = empty cell."""
    n = isqrt(len(grid))
    return "\n".join(str(list(grid[r * n:(r + 1) * n])) for r in range(n))


def main():
    ap = argparse.ArgumentParser(description="Sudoku generator (5 difficulty levels)")
    ap.add_argument("-l", "--level", type=int, choices=range(1, 6), help="1..5 (default: all levels)")
    ap.add_argument("-n", "--count", type=int, default=1, help="puzzles per level")
    ap.add_argument("--size", type=int, choices=(4, 9, 16), default=9, help="board size (default 9)")
    ap.add_argument("--seed", type=int, help="random seed")
    ap.add_argument("-s", "--solution", action="store_true", help="also print the solution")
    ap.add_argument("--no-grade", action="store_true", help="skip the grading step")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    levels = [args.level] if args.level else [1, 2, 3, 4, 5]
    for lv in levels:
        for k in range(args.count):
            t0 = time.time()
            puzzle, solution = generate(lv, rng, size=args.size)
            dt = time.time() - t0
            print(f"\n=== {args.size}x{args.size} Level {lv}: {LEVELS[lv]['name']}  (#{k + 1}, {dt:.2f}s) ===")
            print(format_grid(puzzle))
            if not args.no_grade:
                g = grade(puzzle)
                print(
                    f"givens={g['givens']}  min givens in row/col={g['rc_min']}  "
                    f"technique={g['technique']}  DFS trials={g['search']}"
                    f"{'+' if g['search'] >= 100000 else ''}"
                )
                print(f"factor scores={g['scores']}  weighted={g['total']}  -> graded level {g['level']}")
            if args.solution:
                print("Solution:")
                print(format_grid(solution))
            # sanity check: unique solution
            assert len(Solver(puzzle).solve(2)) == 1, "puzzle does not have a unique solution!"


if __name__ == "__main__":
    main()
