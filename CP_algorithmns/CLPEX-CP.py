
import importlib

from docplex.cp.model import CpoModel
import time


def solve_cplex_cp(grid):

    start = time.perf_counter()

    n = len(grid)
    box = int(n ** 0.5)

    if box * box != n:
        raise ValueError("Sudoku size must be a perfect square.")

    model = CpoModel()

    # x[r][c] là giá trị của ô (r, c), từ 1 đến n
    x = [
        [
            model.integer_var(min=1, max=n, name=f"x_{r}_{c}")
            for c in range(n)
        ]
        for r in range(n)
    ]

    # Mỗi hàng và cột chứa các giá trị khác nhau
    for r in range(n):
        model.add(model.all_diff(x[r]))

    for c in range(n):
        model.add(model.all_diff([x[r][c] for r in range(n)]))

    # Mỗi box chứa các giá trị khác nhau
    for br in range(0, n, box):
        for bc in range(0, n, box):
            cells = [
                x[r][c]
                for r in range(br, br + box)
                for c in range(bc, bc + box)
            ]
            model.add(model.all_diff(cells))

    # Giữ nguyên các ô đã cho
    for r in range(n):
        for c in range(n):
            if grid[r][c] != 0:
                model.add(x[r][c] == grid[r][c])

    build_time = time.perf_counter() - start

    solve_start = time.perf_counter()
    solution = model.solve(TimeLimit=60)
    solve_time = time.perf_counter() - solve_start

    status = "UNSAT"
    solved_grid = None

    if solution is not None:
        solved_grid = [
            [solution.get_value(x[r][c]) for c in range(n)]
            for r in range(n)
        ]
        status = "SAT"

    return {
        "method": "CPLEX CP",
        "status": status,
        "build_time": build_time,
        "solve_time": solve_time,
        "total_time": build_time + solve_time,
        "solution": solved_grid,
    }
