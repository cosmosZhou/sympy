from util import *


@apply
def apply(given):
    x, complement = given.of(Contains)
    U, y = complement.of(Complement)
    y = y.of(FiniteSet)
    return Unequal(x, y)

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    y = Symbol.y(complex=True, shape=(n,), given=True)
    C = Symbol.C(etype=dtype.complex * n, given=True)
    Eq << apply(Contains(x, C - {y}))

    Eq << ~Eq[1]

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()

