from sympy import *
from axiom.utility import prove, apply


@apply
def apply(x, y):
    return Equivalent(Unequal(x, y), Contains(x, y.universalSet // {y}))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    y = Symbol.y(complex=True, shape=(n,), given=True)

    Eq << apply(x, y)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    prove()

