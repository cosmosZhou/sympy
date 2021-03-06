from sympy.core.relational import Unequality
from axiom.utility import prove, apply
from sympy import Symbol
from sympy.logic.boolalg import Equivalent
from sympy.sets.contains import Contains


@apply(imply=True)
def apply(x, y):
    return Equivalent(Unequality(x, y), Contains(x, y.universalSet - y.set))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    y = Symbol.y(complex=True, shape=(n,), given=True)

    Eq << apply(x, y)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    prove(__file__)

