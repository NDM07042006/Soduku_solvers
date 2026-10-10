"""
2 test case minh hoa cach dung ham scamo_scl(variables, w) trong thuc te:
- Test case 1: giai mot bai toan SCAMO don gian, in ra 1 nghiem va tu kiem
  tra bang tay xem co dung khong.
- Test case 2: them mot rang buoc phu (ep 1 vai bien phai True) de xem
  solver tu suy ra cac bien con lai phai False the nao, va thu truong hop
  UNSAT khi ep qua nhieu bien True trong cung 1 cua so.
"""
from pysat.formula import IDPool
from pysat.solvers import Cadical195
from Testing import scamo_scl


def print_solution(model, variables, w, title):
    model_set = set(model)
    bits = [1 if v in model_set else 0 for v in variables]
    print(f"--- {title} ---")
    print("Gia tri x1..xn:", bits)

    # Tu kiem tra bang tay: quet moi cua so w bien lien tiep
    ok = True
    for i in range(len(bits) - w + 1):
        window_sum = sum(bits[i:i + w])
        if window_sum > 1:
            ok = False
            print(f"  -> VI PHAM tai cua so x{i+1}..x{i+w}, tong = {window_sum}")
    print("Ket qua kiem tra SCAMO:", "HOP LE" if ok else "VI PHAM")
    print()


# =========================================================================
# TEST CASE 1: n=10, w=4 (dung dung vi du trong bai bao) - giai binh thuong
# =========================================================================
n, w = 10, 4
vpool = IDPool(start_from=1)
x = [1, 1, 1, 1, 1]

clauses, vpool = scamo_scl(x, w, vpool=vpool)

with Cadical195(bootstrap_with=clauses) as solver:
    if solver.solve():
        model = solver.get_model()
        print_solution(model, x, w, "Test case 1: n=10, w=4, khong ep gi them")
    else:
        print("Test case 1: UNSAT (khong xay ra voi truong hop nay)")


# =========================================================================
# TEST CASE 2: n=10, w=4 - EP THEM x1=True va x3=True (cung trong 1 cua so
# 4 bien x1..x4) -> phai la UNSAT vi vi pham SCAMO ngay tu dau
# =========================================================================
vpool2 = IDPool(start_from=1)
x2 = [vpool2.id(f"x{i}") for i in range(1, n + 1)]
clauses2, vpool2 = scamo_scl(x2, w, vpool=vpool2)

extra_assumptions = [x2[0], x2[2]]  # ep x1=True, x3=True

with Cadical195(bootstrap_with=clauses2) as solver:
    sat = solver.solve(assumptions=extra_assumptions)
    print(f"--- Test case 2: ep x1=True va x3=True (cung 1 cua so 4 bien) ---")
    print("Ket qua solver:", "SAT" if sat else "UNSAT (dung nhu ky vong)")
    if sat:
        model = solver.get_model()
        print_solution(model, x2, w, "Test case 2 (khong dung ky vong)")
    print()

# Doi chung: ep x1=True va x5=True (khac cua so, khong vi pham) -> phai SAT
with Cadical195(bootstrap_with=clauses2) as solver:
    sat = solver.solve(assumptions=[x2[0], x2[4]])
    print("--- Doi chung: ep x1=True va x5=True (khac cua so) ---")
    print("Ket qua solver:", "SAT (dung nhu ky vong)" if sat else "UNSAT")
    if sat:
        model = solver.get_model()
        print_solution(model, x2, w, "Doi chung")