from util import *


@apply(given=None)
def apply(given, lhs=-1, rhs=None):
    from axiom.algebra.eq.transport import transport
    return Equivalent(given, transport(GreaterEqual, given, lhs=lhs, rhs=rhs), evaluate=False)


@prove
def prove(Eq):
    x, y, a = Symbol(real=True)
    Eq << apply(GreaterEqual(x + a, y))

    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()
# created on 2019-09-03
