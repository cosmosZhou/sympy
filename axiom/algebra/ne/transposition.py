from util import *


@apply(given=None)
def apply(given, index=-1, left=True):
    from axiom.algebra.eq.transposition import transposition
    return Equivalent(given, transposition(Unequal, given, index=index, left=left), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    Eq << apply(Unequal(x + a, y))

    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()