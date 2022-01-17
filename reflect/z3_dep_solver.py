import z3

TupleType = z3.Datatype("Tuple")

TupleType.declare(
    "cons", ("major", z3.IntSort()), ("minor", z3.IntSort()), ("micro", z3.IntSort())
)
TupleType = TupleType.create()
TupleCons = TupleType.cons


def create_tuple(name):
    return z3.Const(name, TupleType)

tuple_var = create_tuple


get_major = TupleType.major
get_minor = TupleType.minor
get_micro = TupleType.micro

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
    return lt_tuple(b, a)


def eq_tuple(a, b):
    return a == b

def ne_tuple(a, b):
    return a != b


def solve_deps(deps: list):
    solver = z3.Solver()
    solver.add(*deps)
    if solver.check() == z3.sat:
        return solver.model()
    return None
