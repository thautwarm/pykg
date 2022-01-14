import z3

TupleType = z3.Datatype("Tuple")

TupleType.declare(
    "cons", ("major", z3.IntSort()), ("minor", z3.IntSort()), ("micro", z3.IntSort())
)
TupleType = TupleType.create()
TupleCons = TupleType.cons


def create_tuple(name):
    return z3.Const(name, TupleType)


get_major = TupleType.major
get_minor = TupleType.minor
get_micro = TupleType.micro

cmp_tuple = z3.Function("compare_tuple", TupleType, TupleType)
cmp_int = z3.Function("compare_int", z3.IntSort(), z3.IntSort())

le_tuple = z3.Function("le_tuple", TupleType, TupleType, z3.BoolSort())
lt_tuple = z3.Function("lt_tuple", TupleType, TupleType, z3.BoolSort())
eq_tuple = z3.Function("eq_tuple", TupleType, TupleType, z3.BoolSort())

T = z3.BoolVal(True)
F = z3.BoolVal(False)


def lt_tuple(tp_a, tp_b):
    return z3.If(
        get_major(tp_a) < get_major(tp_b),
        T,
        z3.If(
            z3.And(
                get_major(tp_a) == get_major(tp_b), get_minor(tp_a) < get_minor(tp_b)
            ),
            T,
            z3.And(
                get_minor(tp_a) == get_minor(tp_b), get_micro(tp_a) < get_micro(tp_b)
            ),
        ),
    )


def le_tuple(tp_a, tp_b):
    return z3.Or(tp_a == tp_b, lt_tuple(tp_a, tp_b))


def ge_tuple(a, b):
    return le_tuple(b, a)


def gt_tuple(a, b):
    return ge_tuple(b, a)


def solve_deps(deps: list):
    solver = z3.Solver()
    solver.add(*deps)
    if solver.check() == z3.sat:
        return solver.model()
    return None
