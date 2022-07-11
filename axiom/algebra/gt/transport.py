from util import *


@apply(given=None)
def apply(given, lhs=-1, rhs=None):
    from axiom.algebra.eq.transport import transport
    return Equivalent(given, transport(Greater, given, lhs=lhs, rhs=rhs), evaluate=False)


@prove
def prove(Eq):
    a, x, y = Symbol(real=True)
    Eq << apply(Greater(x + a, y))

    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()
# created on 2019-06-13
