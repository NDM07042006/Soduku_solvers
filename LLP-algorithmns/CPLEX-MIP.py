
import time
from docplex.mp.model import Model

def solve_cplex_mip(grid):

    start = time.perf_counter()

    n = len(grid)
    box = int(n ** 0.5)

    if box * box != n:
        raise ValueError("Sudoku size must be a perfect square.")

    model = Model(name="Sudoku_MIP")

    x = {
        (r, c, v): model.binary_var(name=f"x_{r}_{c}_{v+1}")
        for r in range(n)
        for c in range(n)
        for v in range(n)
    }

    for r in range(n):
        for c in range(n):
            model.add_constraint(
                model.sum(x[r, c, v] for v in range(n)) == 1
            )

    for r in range(n):
        for v in range(n):
            model.add_constraint(
                model.sum(x[r, c, v] for c in range(n)) == 1
            )

    for c in range(n):
        for v in range(n):
            model.add_constraint(
                model.sum(x[r, c, v] for r in range(n)) == 1
            )

    for br in range(0, n, box):
        for bc in range(0, n, box):
            for v in range(n):
                model.add_constraint(
                    model.sum(
                        x[r, c, v]
                        for r in range(br, br + box)
                        for c in range(bc, bc + box)
                    ) == 1
                )

    for r in range(n):
        for c in range(n):
            if grid[r][c] != 0:
                v = grid[r][c] - 1
                model.add_constraint(x[r, c, v] == 1)

    model.minimize(0)

    build_time = time.perf_counter() - start

    solve_start = time.perf_counter()
    solution = model.solve(log_output=False)
    solve_time = time.perf_counter() - solve_start

    solved_grid = None
    status = "UNSAT"

    if solution is not None:
        solved_grid = [
            [
                next(
                    v + 1
                    for v in range(n)
                    if solution.get_value(x[r, c, v]) > 0.5
                )
                for c in range(n)
            ]
            for r in range(n)
        ]
        status = "SAT"

    return {
        "method": "CPLEX MIP",
        "status": status,
        "build_time": build_time,
        "solve_time": solve_time,
        "total_time": build_time + solve_time,
        "solution": solved_grid,
    }