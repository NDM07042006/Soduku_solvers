
import gurobipy as gp
from gurobipy import GRB
import time

def solve_gurobi(grid):

    start = time.perf_counter()

    n = len(grid)
    box = int(n ** 0.5)

    if box * box != n:
        raise ValueError("Sudoku size must be a perfect square.")

    model = gp.Model("Sudoku_Gurobi")
    model.Params.OutputFlag = 0
    model.Params.TimeLimit = 60

    # x[r,c,v] = 1 nếu ô (r,c) nhận giá trị v+1
    x = model.addVars(
        n, n, n,
        vtype=GRB.BINARY,
        name="x"
    )

    # Mỗi ô có đúng một giá trị
    for r in range(n):
        for c in range(n):
            model.addConstr(
                gp.quicksum(x[r, c, v] for v in range(n)) == 1
            )

    # Hàng
    for r in range(n):
        for v in range(n):
            model.addConstr(
                gp.quicksum(x[r, c, v] for c in range(n)) == 1
            )

    # Cột
    for c in range(n):
        for v in range(n):
            model.addConstr(
                gp.quicksum(x[r, c, v] for r in range(n)) == 1
            )

    # Box
    for br in range(0, n, box):
        for bc in range(0, n, box):
            for v in range(n):
                model.addConstr(
                    gp.quicksum(
                        x[r, c, v]
                        for r in range(br, br + box)
                        for c in range(bc, bc + box)
                    ) == 1
                )

    for r in range(n):
        for c in range(n):
            if grid[r][c] != 0:
                model.addConstr(x[r, c, grid[r][c] - 1] == 1)

    model.setObjective(0, GRB.MINIMIZE)

    build_time = time.perf_counter() - start

    solve_start = time.perf_counter()
    model.optimize()
    solve_time = time.perf_counter() - solve_start

    solved_grid = None
    if model.SolCount > 0:
        solved_grid = [
            [
                next(
                    v + 1 for v in range(n)
                    if x[r, c, v].X > 0.5
                )
                for c in range(n)
            ]
            for r in range(n)
        ]

    if model.Status == GRB.INFEASIBLE:
        status = "UNSAT"
    elif model.SolCount > 0:
        status = "SAT"
    elif model.Status == GRB.TIME_LIMIT:
        status = "UNKNOWN"
    else:
        status = "UNKNOWN"

    result = {
        "method": "Gurobi",
        "status": status,
        "build_time": build_time,
        "solve_time": solve_time,
        "total_time": build_time + solve_time,
        "solution": solved_grid,
    }

    model.dispose()
    return result