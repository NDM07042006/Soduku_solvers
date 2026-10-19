
from ortools.sat.python import cp_model
import time


def solve_cp_sat(grid):


    start = time.perf_counter()

    n = len(grid)
    box = int(n ** 0.5)

    if box * box != n:
        raise ValueError("Sudoku size must be a perfect square.")

    model = cp_model.CpModel()

    x = [
        [
            model.new_int_var(1, n, f"x_{r}_{c}")
            for c in range(n)
        ]
        for r in range(n)
    ]

    for r in range(n):
        model.add_all_different(x[r])

    for c in range(n):
        model.add_all_different([x[r][c] for r in range(n)])

    for br in range(0, n, box):
        for bc in range(0, n, box):
            cells = [
                x[r][c]
                for r in range(br, br + box)
                for c in range(bc, bc + box)
            ]
            model.add_all_different(cells)

    for r in range(n):
        for c in range(n):
            if grid[r][c] != 0:
                model.add(x[r][c] == grid[r][c])

    build_time = time.perf_counter() - start

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 60

    solve_start = time.perf_counter()
    status_code = solver.solve(model)
    solve_time = time.perf_counter() - solve_start

    if status_code in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        status = "SAT"
        solved_grid = [
            [solver.value(x[r][c]) for c in range(n)]
            for r in range(n)
        ]
    elif status_code == cp_model.INFEASIBLE:
        status = "UNSAT"
        solved_grid = None
    else:
        status = "UNKNOWN"
        solved_grid = None

    return {
        "method": "CP-SAT",
        "status": status,
        "build_time": build_time,
        "solve_time": solve_time,
        "total_time": build_time + solve_time,
        "solution": solved_grid,
    }