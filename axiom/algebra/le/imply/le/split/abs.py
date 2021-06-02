from util import *
import axiom



@apply
def apply(given, negate=False):
    x, M = given.of(LessEqual)
    x = x.of(Abs)
    if negate:
        x = -x
    return LessEqual(x, M)


@prove
def prove(Eq):
    from axiom import algebra
    M = Symbol.M(real=True)
    a = Symbol.a(real=True)

    Eq << apply(LessEqual(abs(a), M), negate=True)

    Eq << algebra.imply.le.abs.apply(a, negate=True)

    Eq << algebra.le.le.imply.le.transit.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

