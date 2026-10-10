#!/usr/bin/env python3
"""
Sudoku generator with 5 difficulty levels, following the "dig-hole" approach of
Team #3485, "Sudoku Puzzles Generating: from Easy to Evil".

Pipeline (paper section 5):
  1. Terminal pattern  : Las Vegas algorithm (11 random givens + randomized DFS, retry on failure)
  2. Digging holes     : - Operator 1: dig sequence depends on level
                         - Operator 2: restrictions (total givens bound, min givens per row/col)
                         - Operator 3: uniqueness by reduction to absurdity
                         - Operator 4: pruning (each cell is tried only once, never refilled)
                         - Operator 5: equivalent propagation (relabel digits, swap rows/cols/bands...)
  3. Grading           : 4 weighted factors (givens, row/col lower bound, human technique, DFS search count)

Usage:
    python sudoku_generator.py                 # one puzzle for each of the 5 levels
    python sudoku_generator.py -l 3 -n 2       # two Medium puzzles
    python sudoku_generator.py --seed 42 -s    # reproducible, also print solutions
"""

import argparse
import random
import sys
import time
from itertools import combinations

sys.setrecursionlimit(10000)

# --------------------------------------------------------------------------- #
# Board geometry
# --------------------------------------------------------------------------- #
ALL = 0x1FF  # bitmask 1..9
ROW = [i // 9 for i in range(81)]
COL = [i % 9 for i in range(81)]
BOX = [(i // 27) * 3 + (i % 9) // 3 for i in range(81)]
POP = [bin(m).count("1") for m in range(512)]

ROW_UNITS = [[r * 9 + c for c in range(9)] for r in range(9)]
COL_UNITS = [[r * 9 + c for r in range(9)] for c in range(9)]
BOX_UNITS = [
    [(br * 3 + r) * 9 + bc * 3 + c for r in range(3) for c in range(3)]
    for br in range(3)
    for bc in range(3)
]
UNITS = ROW_UNITS + COL_UNITS + BOX_UNITS

PEERS = []
for _i in range(81):
    s = set(ROW_UNITS[ROW[_i]]) | set(COL_UNITS[COL[_i]]) | set(BOX_UNITS[BOX[_i]])
    s.discard(_i)
    PEERS.append(sorted(s))

# --------------------------------------------------------------------------- #
# Difficulty configuration (paper Tables 1, 2, 7)
# --------------------------------------------------------------------------- #
LEVELS = {
    #  name               givens range  min givens per row/col  dig sequence
    1: dict(name="Extremely easy", givens=(51, 60), rc_min=5, seq="random"),
    2: dict(name="Easy",           givens=(36, 49), rc_min=4, seq="random"),
    3: dict(name="Medium",         givens=(32, 35), rc_min=3, seq="jump"),
    4: dict(name="Difficult",      givens=(28, 31), rc_min=2, seq="snake"),
    5: dict(name="Evil",           givens=(22, 27), rc_min=0, seq="row"),
}


# --------------------------------------------------------------------------- #
# Solver: depth-first search with backtracking (bitmask + "fewest candidates" cell choice)
# --------------------------------------------------------------------------- #
class Solver:
    def __init__(self, grid, rng=None, node_limit=None):
        self.g = list(grid)
        self.rows, self.cols, self.boxes = [0] * 9, [0] * 9, [0] * 9
        self.valid = True
        for i, v in enumerate(self.g):
            if v:
                bit = 1 << (v - 1)
                if (self.rows[ROW[i]] | self.cols[COL[i]] | self.boxes[BOX[i]]) & bit:
                    self.valid = False
                self.rows[ROW[i]] |= bit
                self.cols[COL[i]] |= bit
                self.boxes[BOX[i]] |= bit
        self.rng = rng
        self.node_limit = node_limit
        self.nodes = 0
        self.aborted = False
        self.solutions = []
        self.limit = 1

    def solve(self, limit=1):
        """Return up to `limit` solutions (list of 81-int lists)."""
        self.solutions, self.limit = [], limit
        self.nodes, self.aborted = 0, False
        if self.valid:
            self._dfs()
        return self.solutions

    def _dfs(self):
        g = self.g
        best, best_mask, best_cnt = -1, 0, 10
        for i in range(81):
            if g[i] == 0:
                avail = ALL & ~(self.rows[ROW[i]] | self.cols[COL[i]] | self.boxes[BOX[i]])
                cnt = POP[avail]
                if cnt < best_cnt:
                    best, best_mask, best_cnt = i, avail, cnt
                    if cnt <= 1:
                        break
        if best < 0:  # no empty cell -> solved
            self.solutions.append(list(g))
            return
        if best_cnt == 0:  # dead end
            return

        digits = [d for d in range(1, 10) if (best_mask >> (d - 1)) & 1]
        if self.rng:
            self.rng.shuffle(digits)
        r, c, b = ROW[best], COL[best], BOX[best]
        for d in digits:
            self.nodes += 1
            if self.node_limit and self.nodes > self.node_limit:
                self.aborted = True
                return
            bit = 1 << (d - 1)
            g[best] = d
            self.rows[r] |= bit
            self.cols[c] |= bit
            self.boxes[b] |= bit
            self._dfs()
            g[best] = 0
            self.rows[r] ^= bit
            self.cols[c] ^= bit
            self.boxes[b] ^= bit
            if self.aborted or len(self.solutions) >= self.limit:
                return


# --------------------------------------------------------------------------- #
# Step 1: terminal pattern by Las Vegas algorithm
# --------------------------------------------------------------------------- #
def _random_givens(rng, n):
    g = [0] * 81
    for i in rng.sample(range(81), n):
        used = 0
        for p in PEERS[i]:
            if g[p]:
                used |= 1 << (g[p] - 1)
        avail = [d for d in range(1, 10) if not (used >> (d - 1)) & 1]
        if not avail:
            return None
        g[i] = rng.choice(avail)
    return g


def create_terminal_pattern(rng, n_givens=11, node_limit=3000):
    """Randomly place n givens (paper: n = 11 is the best trade-off), try to complete the grid
    within a small budget; if that fails, repeat (Las Vegas: always correct, random running time)."""
    while True:
        g = _random_givens(rng, n_givens)
        if g is None:
            continue
        sol = Solver(g, rng=rng, node_limit=node_limit).solve(1)
        if sol:
            return sol[0]


# --------------------------------------------------------------------------- #
# Step 2: digging holes
# --------------------------------------------------------------------------- #
def dig_sequence(kind, rng):
    """Operator 1: order in which cells are tried."""
    if kind == "row":  # Sequence 1: left->right, top->bottom
        return list(range(81))
    if kind == "snake":  # Sequence 2: wandering along "S"
        return [r * 9 + (c if r % 2 == 0 else 8 - c) for r in range(9) for c in range(9)]
    if kind == "jump":  # Sequence 3: jumping one cell (checkerboard, then the other colour)
        cells = list(range(81))
        return [i for i in cells if (ROW[i] + COL[i]) % 2 == 0] + [
            i for i in cells if (ROW[i] + COL[i]) % 2 == 1
        ]
    seq = list(range(81))  # Sequence 4: randomize globally
    rng.shuffle(seq)
    return seq


def unique_after_dig(puzzle, idx):
    """Operator 3: reduction to absurdity.
    Clear cell idx (value d). Try every other digit d' that obeys the rules; if the puzzle
    can be solved with d' there, a 2nd solution exists -> the dig is illegal.
    Returns True (and leaves the cell empty) if the solution stays unique; else restores d."""
    d = puzzle[idx]
    puzzle[idx] = 0
    used = 0
    for p in PEERS[idx]:
        if puzzle[p]:
            used |= 1 << (puzzle[p] - 1)
    for d2 in range(1, 10):
        if d2 == d or (used >> (d2 - 1)) & 1:
            continue
        test = list(puzzle)
        test[idx] = d2
        if Solver(test).solve(1):
            puzzle[idx] = d  # not unique -> refill (this cell is never tried again: pruning)
            return False
    return True


def dig_holes(terminal, level, rng):
    cfg = LEVELS[level]
    lo, hi = cfg["givens"]
    bound = rng.randint(lo, hi)  # Restriction 1: random bound inside the level's range
    puzzle = list(terminal)
    givens = 81
    row_cnt, col_cnt = [9] * 9, [9] * 9
    for idx in dig_sequence(cfg["seq"], rng):  # each cell is tried at most once (Operator 4)
        if givens <= bound:
            break
        if row_cnt[ROW[idx]] - 1 < cfg["rc_min"] or col_cnt[COL[idx]] - 1 < cfg["rc_min"]:
            continue  # Restriction 2: keep enough givens in every row / column
        if unique_after_dig(puzzle, idx):
            givens -= 1
            row_cnt[ROW[idx]] -= 1
            col_cnt[COL[idx]] -= 1
    return puzzle


# --------------------------------------------------------------------------- #
# Operator 5: equivalent propagation (keeps the puzzle valid and unique)
# --------------------------------------------------------------------------- #
def propagate(puzzle, solution, rng):
    perm = list(range(1, 10))
    rng.shuffle(perm)  # relabel digits

    def order():
        bands = list(range(3))
        rng.shuffle(bands)
        out = []
        for b in bands:
            rows = [b * 3 + k for k in range(3)]
            rng.shuffle(rows)
            out += rows
        return out

    rord, cord = order(), order()
    transpose = rng.random() < 0.5

    def transform(grid):
        res = [0] * 81
        for r in range(9):
            for c in range(9):
                v = grid[rord[r] * 9 + cord[c]]
                res[r * 9 + c] = perm[v - 1] if v else 0
        if transpose:
            res = [res[c * 9 + r] for r in range(9) for c in range(9)]
        return res

    return transform(puzzle), transform(solution)


# --------------------------------------------------------------------------- #
# Grading (paper section 4)
# --------------------------------------------------------------------------- #
def _score_givens(n):
    return 1 if n > 50 else 2 if n >= 36 else 3 if n >= 32 else 4 if n >= 28 else 5


def _score_rc(m):
    return 1 if m >= 5 else 2 if m == 4 else 3 if m == 3 else 4 if m == 2 else 5


def _score_search(n):
    return 1 if n < 100 else 2 if n < 1000 else 3 if n < 10000 else 4 if n <= 100000 else 5


def human_technique_score(puzzle):
    """Highest technique needed (Table 3): 1 elimination/naked single, 2 lone ranger (hidden single),
    3 twins (naked pairs), 4 triplets (naked triples), 5 brute force (anything else)."""
    g = list(puzzle)
    cand = [0] * 81
    for i in range(81):
        if g[i] == 0:
            used = 0
            for p in PEERS[i]:
                if g[p]:
                    used |= 1 << (g[p] - 1)
            cand[i] = ALL & ~used

    def place(i, bit):
        g[i] = bit.bit_length()
        cand[i] = 0
        for p in PEERS[i]:
            cand[p] &= ~bit

    hardest = 1
    while 0 in g:
        # 1) naked single
        done = False
        for i in range(81):
            if g[i] == 0 and POP[cand[i]] == 1:
                place(i, cand[i])
                done = True
                break
        if done:
            continue
        if any(g[i] == 0 and cand[i] == 0 for i in range(81)):
            return 5
        # 2) hidden single
        for unit in UNITS:
            for d in range(9):
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
            for unit in UNITS:
                cells = [i for i in unit if g[i] == 0 and 2 <= POP[cand[i]] <= k]
                for combo in combinations(cells, k):
                    union = 0
                    for i in combo:
                        union |= cand[i]
                    if POP[union] != k:
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
    g = list(puzzle)
    rows, cols, boxes = [0] * 9, [0] * 9, [0] * 9
    for i, v in enumerate(g):
        if v:
            bit = 1 << (v - 1)
            rows[ROW[i]] |= bit
            cols[COL[i]] |= bit
            boxes[BOX[i]] |= bit
    empties = [i for i in range(81) if g[i] == 0]
    nodes = 0

    def rec(k):
        nonlocal nodes
        if k == len(empties):
            return
        i = empties[k]
        r, c, b = ROW[i], COL[i], BOX[i]
        avail = ALL & ~(rows[r] | cols[c] | boxes[b])
        for d in range(9):
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
    n_given = sum(1 for v in puzzle if v)
    rc_min = min(
        min(sum(1 for i in u if puzzle[i]) for u in ROW_UNITS),
        min(sum(1 for i in u if puzzle[i]) for u in COL_UNITS),
    )
    tech = human_technique_score(puzzle)
    search = dfs_search_count(puzzle)
    s = (_score_givens(n_given), _score_rc(rc_min), tech, _score_search(search))
    total = 0.4 * s[0] + 0.2 * s[1] + 0.2 * s[2] + 0.2 * s[3]
    return dict(
        givens=n_given, rc_min=rc_min, technique=tech, search=search,
        scores=s, total=round(total, 2), level=min(5, max(1, int(total + 0.5))),
    )


# --------------------------------------------------------------------------- #
# Public API
# --------------------------------------------------------------------------- #
def generate(level, rng=None, max_attempts=40):
    """Generate one puzzle of the given level (1..5). Returns (puzzle, solution)."""
    rng = rng or random.Random()
    lo, hi = LEVELS[level]["givens"]
    best, best_dist = None, None
    for _ in range(max_attempts):
        terminal = create_terminal_pattern(rng)
        puzzle = dig_holes(terminal, level, rng)
        n = sum(1 for v in puzzle if v)
        dist = 0 if lo <= n <= hi else (n - hi if n > hi else lo - n)
        if best is None or dist < best_dist:
            best, best_dist = (puzzle, terminal), dist
        if dist == 0:
            break
    puzzle, terminal = best
    return propagate(puzzle, terminal, rng)


class Puzzle(list):
    """A 9x9 puzzle as a normal list of 9 lists (0 = empty cell).
    print(p) shows one row per line; p.solution holds the solved grid (also 9x9)."""

    solution = None

    def __str__(self):
        return "\n".join(str(row) for row in self)


def generate_puzzle(level=2, rng=None, with_solution=False):
    """Return a plain 9x9 list of lists (0 = empty cell). Default level 2 = Easy.
    With with_solution=True, return (puzzle, solution) instead, both 9x9."""
    flat_puzzle, flat_solution = generate(level, rng)
    puzzle = [flat_puzzle[r * 9:(r + 1) * 9] for r in range(9)]
    if with_solution:
        return puzzle, [flat_solution[r * 9:(r + 1) * 9] for r in range(9)]
    return puzzle


def format_grid(grid):
    """One list per row, e.g. [8, 1, 2, 7, 5, 3, 6, 4, 9]; 0 = empty cell."""
    return "\n".join(str(list(grid[r * 9:(r + 1) * 9])) for r in range(9))

"""
def main():
    ap = argparse.ArgumentParser(description="Sudoku generator (5 difficulty levels)")
    ap.add_argument("-l", "--level", type=int, choices=range(1, 6), help="1..5 (default: all levels)")
    ap.add_argument("-n", "--count", type=int, default=1, help="puzzles per level")
    ap.add_argument("--seed", type=int, help="random seed")
    ap.add_argument("-s", "--solution", action="store_true", help="also print the solution")
    ap.add_argument("--no-grade", action="store_true", help="skip the grading step")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    levels = [args.level] if args.level else [1, 2, 3, 4, 5]
    for lv in levels:
        for k in range(args.count):
            t0 = time.time()
            puzzle, solution = generate(lv, rng)
            dt = time.time() - t0
            print(f"\n=== Level {lv}: {LEVELS[lv]['name']}  (#{k + 1}, {dt:.2f}s) ===")
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
"""

n = generate_puzzle(4)
print(n)