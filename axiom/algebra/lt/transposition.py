from util import *


@apply(given=None)
def apply(given, index=-1, left=True, right=False):
    from axiom.algebra.eq.transposition import transposition
    if right:
        left = False
    return Equivalent(given, transposition(Less, given, index=index, left=left), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    Eq << apply(Less(x + a, y))

    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()
