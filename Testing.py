"""
SCL - Sequential Counter cho rang buoc Staircase At-Most-One (SCAMO)
Cai dat theo: Truong, Van Kieu, Van To (2025), "Sequential Counter Encoding
for Staircase At-Most-One Constraints", ICAART 2025.

Dung chung voi PySAT: sinh ra list cac clause (list[list[int]]) de add
truc tiep vao pysat.solvers.Solver hoac pysat.formula.CNF.
"""
from pysat.formula import IDPool


def _sc_block(lits, is_amo, vpool):
    """
    Xay mot khoi Sequential Counter cho danh sach `lits` (da sap theo dung
    thu tu can dung - lits[0] la bien duoc coi la "gan bien mo dau nhat").

    R_{i,1} duoc dinh nghia = lits[0] (khong sinh bien moi).
    R_{i,j} (j=2..len(lits)) la bien phu, dai dien "tong cua j bien dau".

    is_amo=True  -> ap dung ca 4 cong thuc (khoi AMO, THUC SU rang buoc <=1)
    is_amo=False -> chi ap dung cong thuc (1)-(3) (khoi AMZ, chi de tinh
                    tong rieng phuc vu ket noi, KHONG tu rang buoc AMO)

    Tra ve (clauses, R) voi R = [R_{i,1}, R_{i,2}, ..., R_{i,len(lits)}]
    """
    clauses = []
    R = [lits[0]]
    R_prev = lits[0]
    for j in range(1, len(lits)):
        xj = lits[j]
        Rj = vpool.id(("R", id(lits), j))
        clauses.append([-xj, Rj])            # (1) x_j -> R_j
        clauses.append([-R_prev, Rj])        # (2) R_{j-1} -> R_j
        clauses.append([xj, R_prev, -Rj])    # (3) (~x_j ^ ~R_{j-1}) -> ~R_j
        if is_amo:
            clauses.append([-xj, -R_prev])   # (4) x_j -> ~R_{j-1}
        R.append(Rj)
        R_prev = Rj
    return clauses, R


def scamo_scl(variables, w, vpool=None):
    """
    Ma hoa SCAMO(variables, w): trong MOI w bien lien tiep cua `variables`
    (danh sach literal PySAT, so nguyen duong, theo dung thu tu) co toi
    da 1 bien duoc gan True.

    Tra ve (clauses, vpool):
        clauses : list[list[int]]  -- CNF (dang PySAT)
        vpool   : IDPool           -- de tiep tuc sinh bien moi cho phan
                                       con lai cua cong thuc lon hon (ABP...)
    """
    n = len(variables)
    if not (1 < w <= n):
        raise ValueError("Can 1 < w <= n")
    if vpool is None:
        vpool = IDPool(start_from=max(variables) + 1)

    # 1) Chia n bien thanh M = ceil(n/w) khoi KHONG chong lap
    windows = [variables[i:i + w] for i in range(0, n, w)]
    M = len(windows)

    all_clauses = []
    forward_R = [None] * M   # khoi "huong ve bien DAU" cua window -> noi voi khoi TRUOC
    backward_R = [None] * M  # khoi "huong ve bien CUOI" cua window -> noi voi khoi SAU

    for i, win in enumerate(windows):
        is_first, is_last = (i == 0), (i == M - 1)

        if is_first:
            # Bien canh (chi co lang gieng ben phai) -> 1 khoi AMO, huong ra bien cuoi
            cls, R = _sc_block(list(reversed(win)), is_amo=True, vpool=vpool)
            all_clauses += cls
            backward_R[i] = R
        elif is_last:
            # Bien canh (chi co lang gieng ben trai) -> 1 khoi AMO, huong ra bien dau
            cls, R = _sc_block(win, is_amo=True, vpool=vpool)
            all_clauses += cls
            forward_R[i] = R
        else:
            # Khoi giua: CAN CA 2 khoi
            cls_amo, R_amo = _sc_block(win, is_amo=True, vpool=vpool)          # -> khoi truoc
            all_clauses += cls_amo
            forward_R[i] = R_amo
            cls_amz, R_amz = _sc_block(list(reversed(win)), is_amo=False, vpool=vpool)  # -> khoi sau
            all_clauses += cls_amz
            backward_R[i] = R_amz

    # 2) Noi cac khoi lien tiep (Proposition 1 / 2 trong bai bao)
    for i in range(M - 1):
        R_prev, R_next = backward_R[i], forward_R[i + 1]
        s_prev, s_next = len(R_prev), len(R_next)
        for L in range(1, w):
            k_prev = w - L
            if k_prev <= s_prev and L <= s_next:
                all_clauses.append([-R_prev[k_prev - 1], -R_next[L - 1]])

    return all_clauses, vpool


# ---------------------------------------------------------------------------
# Kiem chung: doi chieu voi liet ke toan bo 2^n assignment (chi dung cho n nho)
# ---------------------------------------------------------------------------
def _brute_force_scamo_ok(bits, w):
    n = len(bits)
    for i in range(n - w + 1):
        if sum(bits[i:i + w]) > 1:
            return False
    return True


def test_scamo_scl(n=10, w=4, verbose=True):
    import itertools
    variables = list(range(1, n + 1))
    clauses, _ = scamo_scl(variables, w)

    mismatches = 0
    for bits in itertools.product([False, True], repeat=n):
        assignment = {variables[i]: bits[i] for i in range(n)}

        def lit_true(lit):
            v = abs(lit)
            return assignment[v] if lit > 0 else not assignment[v]

        # Chi xet cac bien goc (x1..xn); bien phu R se duoc SAT solver tu
        # gan gia tri phu hop khi giai thuc te. Trong kiem tra brute-force
        # nay ta chi can kiem tra: TON TAI cach gan cac bien R sao cho CNF
        # thoa man <=> assignment goc thoa SCAMO. Vi CNF chi "rang buoc"
        # (Horn-like) cac bien R theo mot huong, ta gan R theo dung dinh
        # nghia (tong riel thuc te) roi kiem tra CNF co bi vi pham khong.
        sat = _check_with_correct_R(clauses, assignment, variables, w)
        expected = _brute_force_scamo_ok(list(bits), w)
        if sat != expected:
            mismatches += 1
            if verbose:
                print("SAI:", bits, "ma_hoa=", sat, "thuc_te=", expected)

    print("Ket qua:", "DUNG" if mismatches == 0 else f"SAI ({mismatches} truong hop)")
    return mismatches == 0


def _check_with_correct_R(clauses, assignment, variables, w):
    """Gan gia tri cho bien R DUNG theo dinh nghia (khong doan), roi kiem
    tra tat ca clause co thoa man khong -> cach nay kiem tra dung ca chieu
    'clauses khong loai bo assignment hop le' va 'clauses loai duoc assignment
    khong hop le', vi cac bien R chi xuat hien ben trong cac Horn-clause
    rang buoc mot chieu tu x, khong tao rang buoc gia."""
    # De don gian va chinh xac 100%, ta giai lai bang SAT solver thuc su:
    from pysat.solvers import Cadical195
    with Cadical195(bootstrap_with=clauses) as s:
        # Gan cung cac bien x1..xn theo assignment, hoi solver co model nao khop khong
        assumptions = [v if assignment[v] else -v for v in variables]
        return s.solve(assumptions=assumptions)


if __name__ == "__main__":
    test_scamo_scl(n=10, w=4)
    test_scamo_scl(n=9, w=3)