from util import *


@apply
def apply(given):
    or_eqs = given.of(Or)

    ss = []
    var = None
    for eq in or_eqs:
        x, s = eq.of(Contains)

        if var is None:
            var = x
        else:
            assert x == var
        ss.append(s)

    return Contains(x, Union(*ss))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    C = Symbol.C(etype=dtype.real)

    Eq << apply(Or(Contains(x, A), Contains(x, B), Contains(x, C)))

    Eq << Eq[0].simplify()


if __name__ == '__main__':
    run()

from . import piecewise
